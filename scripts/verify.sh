#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/.."
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/check-release.py
