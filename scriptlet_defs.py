#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Generate data-only XBrowser scriptlet definitions from uBO-style filter lists.

The output never contains code: only scriptlet names (validated against the
packaged engine's manifest), argument strings and hostnames. It must be
byte-identical to blocker/scriptlet-defs.mjs for the same list text; see
tests/scriptlet-defs-parity.mjs. Parsing follows uBlock Origin's
static-filtering-parser.js and arglist-parser.js for the scriptlet path.

Commands:
  compile   one local list -> definitions JSON (used by the parity test)
  generate  fetch every catalog list, write per-list definitions + index.json
  sign      sign index.json with an ECDSA P-256 private key (index.json.sig)
  keygen    create a signing key pair
"""
import argparse
import base64
import datetime
import hashlib
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request

FORMAT = 1
ENVIRONMENT = ('chromium', 'edge', 'ublock')
MAX_LIST_BYTES = 16 * 1024 * 1024
MAX_INCLUDE_DEPTH = 8

# JavaScript's \s (WhiteSpace + LineTerminator); Python's \s differs slightly.
JS_WS = '\t\n\v\f\r                  　﻿'
JS_WS_CLASS = '[' + re.escape(JS_WS) + ']'
JS_NON_WS_CLASS = '[^' + re.escape(JS_WS) + ']'


# ---------------------------------------------------------------------------
# Preparser (utils.preparser in static-filtering-parser.js)

PREPARSER_TOKENS = {
    'ext_ublock': 'ublock', 'ext_ubol': 'ubol', 'ext_devbuild': 'devbuild',
    'env_brave': 'brave', 'env_chromium': 'chromium', 'env_edge': 'edge',
    'env_firefox': 'firefox', 'env_legacy': 'legacy', 'env_mobile': 'mobile',
    'env_mv3': 'mv3', 'env_safari': 'safari', 'cap_html_filtering': 'html_filtering',
    'cap_ipaddress': 'ipaddress', 'false': 'false', 'ext_abp': 'false',
    'adguard': 'adguard', 'adguard_app_android': 'false', 'adguard_app_cli': 'false',
    'adguard_app_ios': 'false', 'adguard_app_mac': 'false', 'adguard_app_windows': 'false',
    'adguard_ext_android_cb': 'false', 'adguard_ext_chromium': 'chromium',
    'adguard_ext_chromium_mv3': 'mv3', 'adguard_ext_edge': 'edge',
    'adguard_ext_firefox': 'firefox', 'adguard_ext_opera': 'chromium',
    'adguard_ext_safari': 'false',
}
RE_IF = re.compile(r'^!#(if|else|endif)\b([^\n]*)(?:[\n\r]+|$)', re.M)
RE_EXPR_PART = re.compile(r'(?:(?:&&|\|\|)' + JS_WS_CLASS + r'+)?' + JS_NON_WS_CLASS + '+')


def evaluate_expr_token(token, env):
    not_ = token.startswith('!')
    if not_:
        token = token[1:]
    state = PREPARSER_TOKENS.get(token)
    if state is None:
        if not token.startswith('cap_'):
            return None
        state = 'false'
    return (state == 'false' and not_) or ((state in env) != not_)


def evaluate_expr(expr, env):
    if expr.startswith('(') and expr.endswith(')'):
        expr = expr[1:-1]
    matches = [m.group(0) for m in RE_EXPR_PART.finditer(expr)]
    if not matches:
        return None
    if matches[0].startswith('|') or matches[0].startswith('&'):
        return None
    result = evaluate_expr_token(matches[0], env)
    for part in matches[1:]:
        parts = re.split(' +', part)
        if len(parts) != 2:
            return None
        state = evaluate_expr_token(parts[1], env)
        if state is None:
            return None
        if parts[0] == '||':
            result = result or state
        elif parts[0] == '&&':
            result = result and state
        else:
            return None
    return result


def js_trim(s):
    return s.strip(JS_WS)


def preparser_split(content, env):
    stack, parts = [], [0]
    state = {'discard': False}

    def should_discard():
        return any(v['known'] and v['discard'] for v in stack)

    def begif(details):
        if not state['discard'] and details['known'] and details['discard']:
            parts.append(details['pos'])
            state['discard'] = True
        stack.append(details)

    def endif(match):
        if stack:
            stack.pop()
        if state['discard'] and not should_discard():
            parts.append(match.end())
            state['discard'] = False

    for match in RE_IF.finditer(content):
        kind = match.group(1)
        if kind == 'if':
            result = evaluate_expr(js_trim(match.group(2)), env)
            begif({'known': result is not None, 'discard': result is False, 'pos': match.start()})
        elif kind == 'else':
            if not stack:
                continue
            details = stack[-1]
            endif(match)
            details['discard'] = details['discard'] is False
            details['pos'] = match.start()
            begif(details)
        else:
            endif(match)
    parts.append(len(content))
    return parts


def prune(content, env=ENVIRONMENT):
    parts = preparser_split(content, env)
    return '\n'.join(content[parts[i]:parts[i + 1]] for i in range(0, len(parts), 2))


# ---------------------------------------------------------------------------
# Argument lists (arglist-parser.js)

RE_WS_START = re.compile('^' + JS_WS_CLASS + '+')
RE_WS_END = re.compile('(?:^|' + JS_NON_WS_CLASS + ')(' + JS_WS_CLASS + '+)$')
RE_ODD_TRAILING_ESCAPE = re.compile(r'(?:^|[^\\])(?:\\\\)*\\$')
RE_TRAILING_ESCAPES = re.compile(r'\\+$')


class ArglistParser:
    def __init__(self, separator=',', must_quote=False):
        self.separator = self.actual_separator = separator
        self.must_quote = must_quote
        self.quote_beg = self.quote_end = 0
        self.arg_beg = self.arg_end = 0
        self.separator_beg = self.separator_end = 0
        self.transform = False
        self.failed = False

    @staticmethod
    def left_ws(s):
        m = RE_WS_START.search(s)
        return len(m.group(0)) if m else 0

    @staticmethod
    def right_ws(s):
        m = RE_WS_END.search(s)
        return len(m.group(1)) if m else 0

    def next_arg(self, pattern, beg=0):
        length = len(pattern)
        self.quote_beg = beg + self.left_ws(pattern[beg:])
        self.failed = False
        qc = pattern[self.quote_beg] if self.quote_beg < length else ''
        if qc in ('"', "'", '`'):
            self.index_of_next_separator(pattern, qc)
            if self.arg_end != length:
                self.quote_end = self.arg_end + 1
                self.separator_beg = self.separator_end = self.quote_end
                self.separator_end += self.left_ws(pattern[self.quote_end:])
                if self.separator_end == length:
                    return self
                if pattern[self.separator_end] == self.separator:
                    self.separator_end += 1
                    return self
        self.index_of_next_separator(pattern, self.separator)
        self.separator_beg = self.separator_end = self.arg_end
        if self.separator_beg < length:
            self.separator_end += 1
        self.arg_end -= self.right_ws(pattern[:self.separator_beg])
        self.quote_end = self.arg_end
        if self.must_quote:
            self.failed = True
        return self

    def normalize_arg(self, s, char=''):
        if char == '':
            char = self.actual_separator
        out = ''
        while True:
            pos = s.rfind(char)
            if pos == -1:
                break
            out = s[pos:] + out
            s = s[:pos]
            m = RE_TRAILING_ESCAPES.search(s)
            if m is None:
                continue
            tail = m.group(0)[:-1] if len(m.group(0)) & 1 else m.group(0)
            out = tail + out
            s = s[:-len(m.group(0))]
        return s if out == '' else s + out

    def index_of_next_separator(self, pattern, separator):
        self.arg_beg = self.arg_end = self.quote_beg + 1 if separator != self.separator else self.quote_beg
        self.transform = False
        self.actual_separator = separator
        while self.arg_end < len(pattern):
            pos = pattern.find(separator, self.arg_end)
            if pos == -1:
                self.arg_end = len(pattern)
                return
            if not RE_ODD_TRAILING_ESCAPE.search(pattern[:pos]):
                self.arg_end = pos
                return
            self.transform = True
            self.arg_end = pos + 1


def parse_scriptlet_args(s, must_quote):
    """Mirror of parseExtPatternScriptletArgs/Arglist: returns (args, failed)."""
    if s == '':
        return [], False
    parser = ArglistParser(',', must_quote)
    failed = False
    details = parser.next_arg(s, 0)
    token = s[details.arg_beg:details.arg_end]
    if token.endswith('.js'):
        token = token[:-3]
    failed |= details.failed
    args = [token]
    rest = s[details.separator_end:]
    if rest == '':
        return args, failed
    i, end = 0, len(rest)
    while True:
        details = parser.next_arg(rest, i)
        if i == end:
            break
        arg = rest[details.arg_beg:details.arg_end]
        if details.transform:
            arg = parser.normalize_arg(arg)
        args.append(arg)
        failed |= details.failed
        i = details.separator_end
    return args, failed


# ---------------------------------------------------------------------------
# Hostname lists (parseDomainList/parseDomain/normalizeDomainValue)

RE_HOSTNAME_ASCII = re.compile(r'^(?:[\da-z][\da-z_-]*\.)*[\da-z][\da-z-]*[\da-z]$')
RE_BAD_HOSTNAME_CHARS = re.compile(r'[\x00-\x24\x26-\x29\x2b\x2c\x2f\x3b-\x40\x5c\x5e\x60\x7b-\x7f]')
RE_PLAIN_ENTITY = re.compile(r'^(?:[\da-z][\da-z_-]*\.)+\*$')
RE_IS_ENTITY = re.compile(r'^[^*]+\.\*$')
RE_ADVANCED_DOMAIN = re.compile(r'^([^>]+?)(>>)?(/.*)?$', re.S)
CAN_USE_WILDCARD, CAN_USE_ENTITY, CAN_USE_SINGLE_WILDCARD = 0b0000001, 0b0000010, 0b0000100
CAN_BE_NEGATED, CAN_BE_REGEX, CAN_BE_ANCESTOR, CAN_HAVE_PATH = 0b0001000, 0b0010000, 0b0100000, 0b1000000
FROM_EXT_LIST = CAN_USE_ENTITY | CAN_USE_SINGLE_WILDCARD | CAN_BE_NEGATED | CAN_BE_REGEX | CAN_BE_ANCESTOR | CAN_HAVE_PATH
FORBIDDEN_HOST = set('\x00\t\n\r #/:<>?@[\\]^|%')


def url_hostname(hn):
    """WHATWG URL host setter for special schemes (enough for filter hostnames)."""
    host = urllib.parse.unquote(hn, errors='strict')
    if any(not c.isascii() for c in host):
        import idna  # UTS #46, as used by browsers
        mapped = idna.uts46_remap(host, std3_rules=False, transitional=False)
        labels = []
        for label in mapped.split('.'):
            labels.append(label if label.isascii() else 'xn--' + label.encode('punycode').decode('ascii'))
        host = '.'.join(labels)
    host = host.lower()
    if any(c in FORBIDDEN_HOST or ord(c) < 0x20 or ord(c) == 0x7f for c in host):
        raise ValueError('forbidden host code point')
    return ipv4_normalize(host)


def ipv4_normalize(host):
    labels = host.split('.')
    if labels and labels[-1] == '' and len(labels) > 1:
        labels = labels[:-1]
    last = labels[-1] if labels else ''

    def number(part):
        if part == '':
            return None
        if part[:2] in ('0x', '0X'):
            digits, base = part[2:], 16
            if digits == '':
                return 0
            if not all(c in '0123456789abcdefABCDEF' for c in digits):
                return None
        elif len(part) > 1 and part.startswith('0'):
            digits, base = part[1:], 8
            if not all(c in '01234567' for c in digits):
                return None
        else:
            digits, base = part, 10
            if not digits.isdigit():
                return None
        return int(digits, base)

    if number(last) is None and not (last.isdigit() if last else False):
        return host
    values = [number(p) for p in labels]
    if any(v is None for v in values) or len(values) > 4:
        raise ValueError('invalid IPv4')
    if any(v > 255 for v in values[:-1]) or values[-1] >= 256 ** (5 - len(values)):
        raise ValueError('invalid IPv4')
    ipv4 = values[-1]
    for i, v in enumerate(values[:-1]):
        ipv4 += v * 256 ** (3 - i)
    return '.'.join(str((ipv4 >> s) & 255) for s in (24, 16, 8, 0))


def normalize_hostname_value(s, mode):
    if RE_HOSTNAME_ASCII.match(s):
        return None
    if RE_BAD_HOSTNAME_CHARS.search(s):
        return ''
    hn = s
    has_wildcard = '*' in hn
    if has_wildcard:
        if mode == 0:
            return ''
        if len(hn) == 1:
            return '' if (mode & CAN_USE_SINGLE_WILDCARD) == 0 else None
        if mode & CAN_USE_ENTITY:
            if RE_PLAIN_ENTITY.match(hn):
                return None
            if not RE_IS_ENTITY.match(hn):
                return ''
        elif (mode & CAN_USE_WILDCARD) == 0:
            return ''
        hn = hn.replace('*', '__asterisk__')
    try:
        hn = url_hostname(hn)
    except Exception:
        return ''
    if hn in ('_', ''):
        return ''
    if has_wildcard:
        hn = hn.replace('__asterisk__', '*')
    if (mode & CAN_USE_WILDCARD) == 0 and (hn.startswith('.') or hn.endswith('.')):
        return ''
    return hn


def normalize_domain_value(raw, is_regex, mode):
    if is_regex:
        if (mode & CAN_BE_REGEX) == 0:
            return ''
        regex = raw[9:-1] if raw.startswith('[$domain=/') else raw
        regex = regex.replace('\\|', '|')
        source = regex[1:-1] if len(regex) > 2 and regex.startswith('/') and regex.endswith('/') else regex
        if source == '':
            return ''
        after = '/' + source + '/'
        return None if after == raw else after
    r1 = normalize_hostname_value(raw, mode)
    if r1 is None:
        return None
    if r1 != '':
        return r1
    m = RE_ADVANCED_DOMAIN.match(raw)
    if m is None:
        return ''
    is_ancestor, has_path = m.group(2) is not None, m.group(3) is not None
    if is_ancestor and (mode & CAN_BE_ANCESTOR) == 0:
        return ''
    if has_path and (mode & CAN_HAVE_PATH) == 0:
        return ''
    if is_ancestor and has_path:
        return ''
    r2 = normalize_hostname_value(m.group(1), mode)
    if r2 is None:
        return None
    if r2 == '':
        return ''
    return r2 + (m.group(2) or '') + (m.group(3) or '')


def parse_domain_list(line, list_beg, list_end, mode=FROM_EXT_LIST):
    """Returns (domains, error). domains: [{'hn', 'not'}] for valid entries."""
    s = line[list_beg:list_end]
    domains, error = [], False
    regex_parser = ArglistParser('/')
    beg, list_len = 0, len(s)
    separator_pending = False
    while beg < list_len:
        # parseDomain on the open-ended remainder.
        abs_beg = list_beg + beg
        parent_end = list_end
        not_ = line[abs_beg] == '~'
        d_beg = abs_beg + 1 if not_ else abs_beg
        node_error = not_ and (mode & CAN_BE_NEGATED) == 0
        is_regex = False
        c0 = line[d_beg] if d_beg < len(line) else ''
        if c0 == '/':
            regex_parser.next_arg(line, d_beg + 1)
            end = regex_parser.separator_end
            if end <= parent_end:
                is_regex = True
            else:
                end = -1
        elif c0 == '[' and line.startswith('[$domain=/', d_beg):
            end = line.find('/]', d_beg + 10, parent_end)
            if end != -1:
                end += 2
            is_regex = True
        else:
            end = line.find(',', d_beg, parent_end)
        if end == -1:
            end = parent_end
        hn = None
        if d_beg != end:
            raw = line[d_beg:end]
            value = normalize_domain_value(raw, is_regex, mode)
            if value is None:
                hn = raw
            elif value != '':
                hn = value
            else:
                node_error = error = True
        else:
            node_error = error = True
        length = end - abs_beg
        # parseDomainList bookkeeping
        end_rel = beg + length
        bad_separator = end_rel < list_len and s[end_rel] != ','
        if bad_separator:
            end_rel = s.find(',', end_rel)
            if end_rel == -1:
                end_rel = list_len
        if end_rel != beg:
            if bad_separator:
                node_error = error = True
            if not node_error and hn is not None:
                domains.append({'hn': hn, 'not': not_})
            domain_present = True
        else:
            domain_present = False
            if separator_pending:
                error = True
        if end_rel < list_len and s[end_rel] == ',':
            if not domain_present:
                error = True
            separator_pending = True
            beg = end_rel + 1
        else:
            separator_pending = False
            beg = end_rel
    if separator_pending:
        error = True
    return domains, error


# ---------------------------------------------------------------------------
# Lines (parse/parseFilter/parseExt/parseExtPattern for scriptlets)

RE_COMMENT_LINE = re.compile(r'^(?:!|#' + JS_WS_CLASS + '|####|\\[adblock)', re.I)
RE_EXT_ANCHOR = re.compile(r'(#@?(?:\$\?|\$|%|\?)?#).{1,2}')
RE_SCRIPTLET = re.compile(r'^\+js\(.*\)$')
RE_ADG_SCRIPTLET = re.compile(r'^//scriptlet\(.*\)$')


def anchor_flags(anchor):
    """Returns (exception, adg, supported)."""
    exception = anchor.startswith('#@')
    core = '#' + anchor[2:] if exception else anchor
    if core == '##' or core == '#?#' or core == '#$#' or core == '#$?#':
        return exception, False, True
    if core == '#%#':
        return exception, True, True
    return exception, False, False


def parse_scriptlet_line(raw):
    """Returns None for non-scriptlet lines, else a dict with error/exception/domains/args."""
    body = js_trim(raw)
    if body == '' or RE_COMMENT_LINE.match(body):
        return None
    m = RE_EXT_ANCHOR.search(body)
    if m is None:
        return None
    anchor_beg, anchor = m.start(), m.group(1)
    exception, adg, supported = anchor_flags(anchor)
    pattern = body[anchor_beg + len(anchor):]
    if pattern.startswith('+'):
        if not RE_SCRIPTLET.match(pattern):
            return None
        inner = pattern[4:-1]
    elif adg:
        if not RE_ADG_SCRIPTLET.match(pattern):
            return None
        inner = pattern[12:-1]
    else:
        return None
    error = not supported
    domains, has_options = [], anchor_beg > 0
    if has_options:
        domains, domain_error = parse_domain_list(body, 0, anchor_beg)
        error |= domain_error
    args, failed = parse_scriptlet_args(inner, adg)
    error |= failed
    return {'error': error, 'exception': exception, 'domains': domains, 'args': args}


# ---------------------------------------------------------------------------
# Definitions (same data layout as blocker/scriptlet-defs.mjs)

def js_json(value):
    return json.dumps(value, ensure_ascii=False, separators=(',', ':'))


TABLE_WIDTH = 7


def utf16_len(s):
    return len(s.encode('utf-16-le', 'surrogatepass')) // 2


def to36(n):
    digits = '0123456789abcdefghijklmnopqrstuvwxyz'
    out = ''
    while True:
        n, r = divmod(n, 36)
        out = digits[r] + out
        if n == 0:
            return out.rjust(TABLE_WIDTH, '0')


def table(items):
    """String table: count, count+1 offsets (UTF-16 units, base 36), then items."""
    header, offset = [to36(len(items)), to36(0)], 0
    for item in items:
        offset += utf16_len(item)
        header.append(to36(offset))
    return ''.join(header) + ''.join(items)


def compile_defs(raw, list_id, trusted, manifest):
    if re.search(r'^!#include ', raw, re.M):
        raise ValueError('Expand includes before compiling scriptlet definitions')
    text = prune(raw)
    rules = {}
    stats = {'rules': 0, 'unsupported': 0, 'untrusted': 0, 'rejected': 0}
    for line in re.split(r'\r?\n', text):
        parsed = parse_scriptlet_line(line)
        if parsed is None:
            continue
        if parsed['error']:
            stats['rejected'] += 1
            continue
        domains, exception, args = parsed['domains'], parsed['exception'], parsed['args']
        if args:
            token = args[0] if args[0].endswith('.js') else args[0] + '.js'
            name = manifest['aliases'].get(token, token)
            entry = manifest['scriptlets'].get(name)
            if entry is None:
                stats['unsupported'] += 1
                continue
            if entry['trusted'] and not trusted:
                stats['untrusted'] += 1
                continue
            args[0] = name[:-3]
        elif not exception:
            continue
        if not exception and not any(not d['not'] for d in domains):
            stats['rejected'] += 1
            continue
        key = tuple(args)
        rule = rules.get(key)
        if rule is None:
            rule = rules[key] = {'args': args, 'matches': {}, 'excludes': {}}
        for d in domains:
            if exception and d['not']:
                continue
            (rule['excludes'] if exception or d['not'] else rule['matches'])[d['hn']] = True
        if exception and not domains:
            rule['excludes']['*'] = True
        stats['rules'] += 1

    arg_index, arglists = {}, {'': 0}
    hostnames, regexes = {}, {}
    flags = {'entities': False, 'ancestors': False}

    def add(hn, ref):
        if '/' in hn:
            if len(hn) > 2 and hn.startswith('/') and hn.endswith('/'):
                regexes.setdefault(hn[1:-1], []).append(ref)
            return
        if ref > 0:
            flags['entities'] = flags['entities'] or hn.endswith('.*') or hn.endswith('.*>>')
            flags['ancestors'] = flags['ancestors'] or hn.endswith('>>')
        hostnames.setdefault(hn, []).append(ref)

    for rule in rules.values():
        if not rule['args']:
            for hn in rule['excludes']:
                add(hn, 0)
            continue
        arglist = [rule['args'][0]]
        for arg in rule['args'][1:]:
            if arg not in arg_index:
                arg_index[arg] = len(arg_index)
            arglist.append(arg_index[arg])
        key = js_json(arglist)[1:-1]
        if key not in arglists:
            arglists[key] = len(arglists)
        index = arglists[key]
        for hn in rule['matches']:
            add(hn, index)
        for hn in rule['excludes']:
            add(hn, ~index)

    def utf16_key(s):
        units = s.encode('utf-16-le')
        return (len(units) // 2, [int.from_bytes(units[i:i + 2], 'little') for i in range(0, len(units), 2)])

    ordered = sorted(hostnames, key=utf16_key)
    return {
        'format': FORMAT, 'list': list_id,
        'entities': flags['entities'], 'ancestors': flags['ancestors'],
        'hostnames': table(ordered),
        'refs': table([','.join(str(r) for r in hostnames[hn]) for hn in ordered]),
        'regexes': [[source, ','.join(str(r) for r in refs)] for source, refs in regexes.items()],
        'arglists': table(list(arglists)),
        'args': table(list(arg_index)),
        'stats': stats,
    }


# ---------------------------------------------------------------------------
# Fetching lists with uBO include semantics (preparser.expandIncludes)

RE_INCLUDE = re.compile(r'^!#include +(\S+)[^\n\r]*(?:[\n\r]+|$)', re.M)


def fetch_text(url, timeout=60):
    if not url.startswith('https://'):
        raise ValueError('Only HTTPS lists are fetched: ' + url)
    request = urllib.request.Request(url, headers={'User-Agent': 'XBrowser-scriptlet-defs/1'})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        data = response.read(MAX_LIST_BYTES + 1)
    if len(data) > MAX_LIST_BYTES:
        raise ValueError('List exceeds size budget: ' + url)
    return data.decode('utf-8-sig')


def expand_includes(url, fetch=fetch_text, depth=0, seen=None):
    """Text of a list with its !#include sublists inlined, as uBO loads it."""
    seen = set() if seen is None else seen
    if depth > MAX_INCLUDE_DEPTH or url in seen:
        raise ValueError('Include depth or cycle: ' + url)
    seen = seen | {url}
    content = fetch(url)
    slices = preparser_split(content, ENVIRONMENT)
    out = []
    for i in range(0, len(slices), 2):
        chunk = content[slices[i]:slices[i + 1]]
        last = 0
        for m in RE_INCLUDE.finditer(chunk):
            target = m.group(1)
            if urllib.parse.urlsplit(target.strip()).scheme or '..' in target:
                continue
            pos = url.rfind('/')
            if pos == -1:
                continue
            sub = url[:pos + 1] + target.strip()
            out.append(chunk[last:m.end()])
            out.append(expand_includes(sub, fetch, depth + 1, seen) + '\n')
            last = m.end()
        out.append(chunk[last:])
    # Include directives were consumed above; keep them as comments so the
    # compiler's guard against unexpanded includes does not trigger.
    return re.sub(r'^!#include ', '! #include ', ''.join(out), flags=re.M)


# ---------------------------------------------------------------------------
# Commands

def load_json(path):
    with open(path, encoding='utf-8') as f:
        return json.load(f)


def write_bytes(path, data):
    with open(path, 'wb') as f:
        f.write(data)


def cmd_compile(args):
    manifest = load_json(args.manifest)
    with open(args.input, encoding='utf-8', newline='') as f:
        raw = f.read()
    trusted = args.trusted if args.trusted is not None else args.list.startswith('ublock-')
    sys.stdout.buffer.write(js_json(compile_defs(raw, args.list, trusted, manifest)).encode('utf-8'))


def cmd_generate(args):
    manifest = load_json(args.manifest)
    catalog = load_json(args.catalog)
    os.makedirs(args.out, exist_ok=True)
    sequence = args.sequence or int(time.time())
    index = {'format': FORMAT, 'kind': 'xbrowser-scriptlet-defs', 'sequence': sequence,
             'generated': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
             'lists': {}}
    failures = []
    for entry in catalog:
        list_id = entry['id']
        if not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', list_id):
            raise ValueError('Invalid list id: ' + list_id)
        raw = None
        for url in entry['urls']:
            try:
                raw = expand_includes(url)
                break
            except Exception as error:  # try the next mirror
                last_error = error
        if raw is None:
            failures.append(f'{list_id}: {last_error}')
            continue
        defs = compile_defs(raw, list_id, list_id.startswith('ublock-'), manifest)
        data = js_json(defs).encode('utf-8')
        write_bytes(os.path.join(args.out, list_id + '.json'), data)
        index['lists'][list_id] = {'file': list_id + '.json', 'sha256': hashlib.sha256(data).hexdigest(),
                                   'bytes': len(data), 'rules': defs['stats']['rules']}
        print(f'{list_id}: {defs["stats"]}', file=sys.stderr)
    write_bytes(os.path.join(args.out, 'index.json'), js_json(index).encode('utf-8'))
    for failure in failures:
        print('FAILED ' + failure, file=sys.stderr)
    if len(failures) > args.max_failures:
        sys.exit(1)


def cmd_sign(args):
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
    key_pem = os.environ.get(args.key_env, '').encode() if args.key_env else open(args.key, 'rb').read()
    key = serialization.load_pem_private_key(key_pem, password=None)
    if not isinstance(key, ec.EllipticCurvePrivateKey) or key.curve.name != 'secp256r1':
        raise ValueError('Signing key must be ECDSA P-256')
    with open(args.index, 'rb') as f:
        data = f.read()
    r, s = decode_dss_signature(key.sign(data, ec.ECDSA(hashes.SHA256())))
    # IEEE P1363 (r || s), the format Windows' EcdsaP256Sha256 verifier expects.
    signature = r.to_bytes(32, 'big') + s.to_bytes(32, 'big')
    write_bytes(args.index + '.sig', base64.b64encode(signature) + b'\n')


def cmd_keygen(args):
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    key = ec.generate_private_key(ec.SECP256R1())
    write_bytes(args.private, key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                                serialization.NoEncryption()))
    public = key.public_key().public_bytes(serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo)
    print('Public key (SubjectPublicKeyInfo, base64) for ScriptletDefinitionService.PublicKey:')
    print(base64.b64encode(public).decode('ascii'))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('compile')
    p.add_argument('--input', required=True)
    p.add_argument('--list', required=True)
    p.add_argument('--manifest', required=True)
    p.add_argument('--trusted', type=lambda v: v == 'true', default=None)
    p.set_defaults(func=cmd_compile)
    p = sub.add_parser('generate')
    p.add_argument('--catalog', required=True)
    p.add_argument('--manifest', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--sequence', type=int)
    p.add_argument('--max-failures', type=int, default=5)
    p.set_defaults(func=cmd_generate)
    p = sub.add_parser('sign')
    p.add_argument('--index', required=True)
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('--key')
    group.add_argument('--key-env')
    p.set_defaults(func=cmd_sign)
    p = sub.add_parser('keygen')
    p.add_argument('--private', required=True)
    p.set_defaults(func=cmd_keygen)
    args = parser.parse_args()
    args.func(args)


if __name__ == '__main__':
    main()
