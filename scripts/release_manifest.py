"""Shared file inventory for reproducible release manifests (requires a Git checkout)."""
from pathlib import Path
import hashlib
import subprocess

DERIVED_FILES = {'SOURCE_SHA256SUMS', 'publication-manifest.json',
                 'verification/release-check.json'}


def release_files(root):
    """Include tracked files and nonignored additions, never build/cache output."""
    try:
        top = subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=root,
                                      stderr=subprocess.PIPE).decode('utf-8').strip()
        if Path(top).resolve() != root.resolve():
            raise SystemExit('FAIL: run release checks inside this project\'s Git checkout')
        listing = subprocess.check_output(
            ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
            cwd=root, stderr=subprocess.PIPE).decode('utf-8')
    except (OSError, subprocess.CalledProcessError, UnicodeError) as error:
        raise SystemExit('FAIL: a Git checkout and Git are required for complete release-file '
                         'coverage; clone the repository before checking or refreshing') from error
    names = sorted(set(name for name in listing.split('\0') if name))
    for name in names:
        path = root / name
        if (Path(name).is_absolute() or '..' in Path(name).parts or '\\' in name
                or '\n' in name or '\r' in name or not path.is_file() or path.is_symlink()):
            raise SystemExit('FAIL: release inventory requires a regular repository file: ' + name)
    return names


def file_hash(root, name):
    return hashlib.sha256((root / name).read_bytes()).hexdigest()
