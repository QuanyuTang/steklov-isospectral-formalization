#!/usr/bin/env python3
"""Validate JSON-compatible formalization.yaml against the official v0.4 schema."""
from pathlib import Path
import json
import re
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


def require(condition, message):
    # These are release contracts, so Python's -O option must not disable them.
    if not condition:
        raise SystemExit('FAIL: ' + message)


def placeholder_paths(value, path='$'):
    if isinstance(value, dict):
        return [p for key, child in value.items()
                for p in placeholder_paths(child, f'{path}.{key}')]
    if isinstance(value, list):
        return [p for index, child in enumerate(value)
                for p in placeholder_paths(child, f'{path}[{index}]')]
    if isinstance(value, str) and re.match(r'^TEMPLATE(?::|$)', value.lstrip()):
        return [path]
    return []


require(document.get('version') == 'v0.4', 'metadata version must be v0.4')
require(document['project']['authors'] == ['taohu-hub', 'RGConj', 'QuanyuTang'],
        'ordered formalization authors changed; review authorship intentionally')
require(document['project']['responsible_maintainers'] == ['taohu-hub', 'RGConj', 'QuanyuTang'],
        'responsible maintainers changed; review maintenance intentionally')
require(document['project']['license'] == 'Apache-2.0', 'project license must be Apache-2.0')
description = document['project'].get('description', '')
require(isinstance(description, str) and 0 < len(description.strip()) <= 10000,
        'project.description must be nonempty text of at most 10000 characters')
placeholders = placeholder_paths(document)
require(not placeholders, 'unreplaced template values: ' + ', '.join(placeholders))

relationships = {'formalizes', 'adapts', 'independently-proves', 'background', 'other'}
sources = document.get('sources', [])
require(bool(sources), 'at least one mathematical source or original-proof declaration is required')
for index, source in enumerate(sources):
    require(source.get('relationship') in relationships,
            f'sources[{index}].relationship is not a supported source relationship')
original = [source for source in sources if source.get('type') == 'original-proof']
if original:
    require(len(original) == 1 and original[0]['relationship'] == 'other',
            'use exactly one original-proof source with relationship other')
    require(all(source['relationship'] in {'background', 'other'} for source in sources),
            'original-proof origin cannot be combined with a source-based origin')
else:
    require(any(source['relationship'] in {'formalizes', 'adapts', 'independently-proves'}
                for source in sources), 'a source-based result must identify its mathematical source')
require(document.get('repository', {}).get('role', 'substantive-development') == 'substantive-development',
        'this repository is the substantive proof development, not a thin wrapper')
print('Official v0.4 schema, template/source rules, authorship, maintainers, and license metadata: PASS')
