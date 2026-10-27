#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/.."
python3 - <<'PY'
import pathlib, re, sys
pin = pathlib.Path('lean-toolchain').read_text().strip()
m = re.fullmatch(r'leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?', pin)
if not m:
    sys.exit('Unsupported toolchain pin: ' + pin)
major, minor, patch = map(int, m.group(1, 2, 3))
rc = int(m.group(4)) if m.group(4) else 999
if (major, minor, patch, rc) < (4, 35, 0, 2):
    sys.exit('Palomar requires >= v4.35.0-rc2 as checked 2026-10-25. '
             'This verified release is ' + pin + '; port Lean and Mathlib first. '
             'See docs/PALOMAR.md. No Comparator check was run.')
PY
for command in bwrap lake lean python3; do
    command -v "$command" >/dev/null 2>&1 || { echo "Missing: $command" >&2; exit 1; }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
    test -x "$prefix/bin/$tool" || { echo "Missing bundled checker: $tool" >&2; exit 1; }
done
config=$(mktemp)
trap 'rm -f "$config"' EXIT HUP INT TERM
python3 - "$config" "$prefix" <<'PY'
import json, pathlib, sys
config = json.loads(pathlib.Path('comparator.json').read_text())
if 'external_kernels' in config:
    sys.exit('Submitted comparator.json must not set external_kernels')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(pathlib.Path(sys.argv[2]) / 'bin/nanoda_bin')],
    'con-ron': [str(pathlib.Path(sys.argv[2]) / 'bin/con-ron')],
}
pathlib.Path(sys.argv[1]).write_text(json.dumps(config))
PY
lake exe cache get
lake comparator --config "$config"
