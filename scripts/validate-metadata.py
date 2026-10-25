#!/usr/bin/env python3
"""Validate JSON-compatible formalization.yaml against the official v0.4 schema."""
from pathlib import Path
import json
import sys

try:
    import jsonschema
except ImportError:
    sys.exit('Install the validation dependency: python3 -m pip install jsonschema==4.25.1')

root = Path(__file__).resolve().parents[1]
schema = json.loads((root / 'verification/schema/formalization-v0.4.schema.json').read_text(encoding='utf-8'))
document = json.loads((root / 'formalization.yaml').read_text(encoding='utf-8'))
jsonschema.Draft7Validator.check_schema(schema)
errors = sorted(jsonschema.Draft7Validator(schema).iter_errors(document), key=lambda e: str(list(e.path)))
for error in errors:
    print(f'{list(error.path)}: {error.message}', file=sys.stderr)
if errors:
    raise SystemExit(1)
assert document['project']['authors'] == ['taohu-hub', 'RGConj', 'QuanyuTang']
assert document['project']['responsible_maintainers'] == ['taohu-hub', 'RGConj', 'QuanyuTang']
assert document['project']['license'] == 'Apache-2.0'
print('Official v0.4 schema, ordered authorship, maintainers, and license metadata: PASS')
