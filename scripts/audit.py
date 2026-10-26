#!/usr/bin/env python3
"""Run the complete preserved axiom inventory and proof/type checks after lake build."""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
templates = root / 'verification/templates'
sources = [templates / (name + '.lean.in') for name in
           ['Audit', 'AuditRun18', 'AuditRun19', 'AuditRun20', 'Run20Audit']]
imports = ['import Solution']
bodies = []
for source in sources:
    text = source.read_text(encoding='utf-8')
    for line in text.splitlines():
        if re.match(r'^import\s+', line) and line not in imports:
            imports.append(line)
    bodies.append(re.sub(r'^import\s+[^\n]+\n?', '', text, flags=re.M))
target = root / '.lake/audit/ReleaseAudit.lean'
target.parent.mkdir(parents=True, exist_ok=True)
smooth_contract = '''
open scoped ENNReal ContDiff
example (B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ) (V : Submodule ℝ (ℂ → ℝ)) :
    Steklov.AdmissibleSpace B k V ↔
      ((∀ u ∈ V, ContDiff ℝ ∞ u) ∧ Module.finrank ℝ V = k + 1 ∧
        ∀ u ∈ V, u ≠ 0 → B u ≠ 0) := Iff.rfl
'''
target.write_text('\n'.join(imports) + '\n\n' + smooth_contract + '\n\n' + '\n\n'.join(bodies)
                  + '\n#print axioms SteklovSubmission.main_result\n', encoding='utf-8')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-log', type=Path, help='Validate an existing log only; does not rerun Lean')
args = parser.parse_args()
expected = set(re.findall(r'^#print axioms\s+(\S+)', target.read_text(encoding='utf-8'), re.M))
if args.check_log:
    output = args.check_log.read_text(encoding='utf-8')
else:
    print('Checking preserved proof/type contracts, full axiom inventory, and public entry.', flush=True)
    process = subprocess.Popen(['lake', 'env', 'lean',
                               '-Dbackward.isDefEq.respectTransparency=false',
                               '-Dbackward.defeqAttrib.useBackward=true',
                               target.relative_to(root).as_posix()],
                               cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               text=True, encoding='utf-8')
    lines = []
    for line in process.stdout:
        print(line, end='', flush=True)
        lines.append(line)
    result = process.wait()
    if result:
        sys.exit(result)
    output = ''.join(lines)

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = {}
for name, axioms in re.findall(r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", output, re.M):
    axioms = {item.strip() for item in axioms.split(',') if item.strip()}
    if axioms - allowed:
        sys.exit(f'FAIL: {name} depends on forbidden axioms: {sorted(axioms - allowed)}')
    if name in records and records[name] != sorted(axioms):
        sys.exit(f'FAIL: inconsistent axiom reports for {name}')
    records[name] = sorted(axioms)
for name in re.findall(r"^'(.+)' does not depend on any axioms", output, re.M):
    records[name] = []
missing = expected - records.keys()
if missing:
    sys.exit(f'FAIL: missing axiom reports for {sorted(missing)}')
report = {'status': 'pass', 'fresh_lean_run': not bool(args.check_log),
          'smooth_infinity_contract_checked': not bool(args.check_log),
          'audited_unique_targets': len(expected), 'permitted_axioms': sorted(allowed),
          'targets': {name: records[name] for name in sorted(expected)}}
if not args.check_log:
    (target.parent / 'axioms.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(f'Axiom allowlist enforced for all {len(expected)} distinct targets: PASS', flush=True)
if not args.check_log:
    print('Smooth-infinity admissibility contract: PASS', flush=True)
