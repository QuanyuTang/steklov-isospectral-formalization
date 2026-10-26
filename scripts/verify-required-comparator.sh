#!/usr/bin/env bash
set -euo pipefail

# Required phase from PalomarPolicy/CONTRIBUTING.md section 5: bundled Lean
# and NanoDa replay before the additional con-ron attempt. The upstream
# all-kernel PalomarTemplate script is retained as verify-comparator.sh.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "error: $required_command is required" >&2
    exit 1
  }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin; do
  test -x "$prefix/bin/$tool" || {
    echo "error: the pinned toolchain does not bundle $tool" >&2
    exit 1
  }
done

# This temporary configuration is outside the project's sandbox-writable .lake.
# The submitted comparator.json never supplies external_kernels.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-required.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict) or "external_kernels" in config:
    raise SystemExit("error: invalid submitter Comparator configuration")
if config.get("definition_names") != []:
    raise SystemExit("error: concrete statement definitions must be compared in full")
if set(config.get("permitted_axioms", [])) != {"propext", "Classical.choice", "Quot.sound"}:
    raise SystemExit("error: the required axiom set changed")
config.pop("enable_nanoda", None)
config["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"]}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
# Sandbox remains enabled. The trusted bundled Comparator invokes its bundled
# leanchecker after NanoDa and enforces declaration equality and axiom checks.
lake comparator --config "$config"
