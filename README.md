# XBrowser scriptlet definitions

Data-only scriptlet definitions for XBrowser, regenerated every 6 hours by
GitHub Actions and published to the [`scriptlet-defs` release](../../releases/tag/scriptlet-defs).

Each file lists which scriptlets **already packaged in the XBrowser app** run on
which websites, with which text arguments. There is no code here: the app
verifies the signed `index.json`, checks every file's SHA-256 and schema, and
never runs anything but its own packaged scriptlet functions.

- `scriptlet_defs.py` fetches the filter lists in `catalog.json`, parses their
  `##+js(...)` rules the way uBlock Origin does, and writes one file per list.
- `scriptlet-manifest.json` lists the scriptlets the current app contains.
- `tests/` holds a syntax fixture whose expected output comes from uBlock
  Origin's own parser; the workflow does not publish if they differ.

Generated from filter lists by their respective authors (uBlock Origin uAssets,
EasyList and others), under their licenses.
