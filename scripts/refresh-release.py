#!/usr/bin/env python3
"""Refresh source and publication manifests after intentional release edits.

This updates integrity metadata, not proof-verification evidence. Rebuild and
audit the resulting exact commit before claiming a newly verified snapshot.
"""
from pathlib import Path
import json
import subprocess
import sys

from release_manifest import DERIVED_FILES, file_hash, release_files

root = Path(__file__).resolve().parents[1]
names = release_files(root)
source_names = sorted(set(names) - DERIVED_FILES)
(root / 'SOURCE_SHA256SUMS').write_text(
    ''.join(f'{file_hash(root, name)}  {name}\n' for name in source_names),
    encoding='utf-8', newline='\n')
subprocess.run([sys.executable, str(root / 'scripts/check-release.py'), '--write-report'],
               cwd=root, check=True)
manifest_path = root / 'publication-manifest.json'
manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
manifest['file_sha256'] = {name: file_hash(root, name)
                          for name in release_files(root) if name != 'publication-manifest.json'}
manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n',
                         encoding='utf-8', newline='\n')
subprocess.run([sys.executable, str(root / 'scripts/check-release.py')], cwd=root, check=True)
print('Release manifests refreshed and checked. Existing build/kernel evidence was not changed.')
