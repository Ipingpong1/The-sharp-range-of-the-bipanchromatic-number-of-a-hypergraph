#!/usr/bin/env python3
"""Build, audit every proved declaration, and replay the final theorem's full
import closure through Lean's kernel in a fresh environment.
Scope: p >= 2, 1 <= a < p, 2*p <= n+a. Publication novelty is not assessed.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
lake = shutil.which('lake')
if lake is None:
    candidate = Path.home() / '.elan/bin/lake'
    if candidate.is_file():
        lake = str(candidate)
if lake is None:
    raise SystemExit('Install the pinned Lean toolchain via elan, then run this script again.')


def run(args, log):
    print('Running: lake ' + ' '.join(args), flush=True)
    started = time.monotonic()
    result = subprocess.run([lake, *args], cwd=root, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (root / log).write_text(output)
    if result.returncode:
        print(output)
        raise SystemExit(result.returncode)
    if re.search(r'(?im)^.*\bwarning:', output):
        print(output)
        raise SystemExit('Unexpected build/audit warning; inspect the log.')
    print(f'Passed in {time.monotonic() - started:.1f}s; log: {log}', flush=True)
    return output


version = run(['env', 'lean', '--version'], 'toolchain.log').strip()
run(['build'], 'build.log')
audit = run(['env', 'lean', 'SharpRange/Audit.lean'], 'verification.log')
index = json.loads((root / 'theorem-index.json').read_text())
expected = {x['name'] for x in index}
if len(expected) != len(index):
    raise SystemExit('Duplicate declaration names in theorem-index.json.')
reports = {}
for name, axioms in re.findall(r"(?m)^'([^']+)' depends on axioms: \[([^\]]*)\]$", audit):
    if name in reports:
        raise SystemExit(f'Duplicate axiom report: {name}')
    reports[name] = [x.strip() for x in axioms.split(',') if x.strip()]
for name in re.findall(r"(?m)^'([^']+)' does not depend on any axioms$", audit):
    if name in reports:
        raise SystemExit(f'Duplicate axiom report: {name}')
    reports[name] = []
if set(reports) != expected:
    raise SystemExit(f'Axiom-report mismatch: missing={expected-set(reports)}, extra={set(reports)-expected}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in reports.items():
    unexpected = set(axioms) - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms for {name}: {unexpected}')
required = {'Bipanchromatic.sharp_range', 'Bipanchromatic.sharp_range_witness',
            'Bipanchromatic.model_value', 'Bipanchromatic.universal_lower'}
if not required <= set(reports):
    raise SystemExit('Final theorem reports are missing.')
run(['env', 'leanchecker', '--fresh', '--verbose', 'SharpRange.Full'], 'kernel-replay.log')
files = [root / 'Arithmetic.lean' , root / 'SharpRange.lean',
         *sorted((root / 'SharpRange').glob('*.lean')),
         root / 'lean-toolchain', root / 'lakefile.toml', root / 'lake-manifest.json',
         root / 'theorem-index.json', root / 'verify.py']
summary = {
    'status': 'full_sharp_range_verified',
    'full_hypergraph_range_theorem_proved': True,
    'scope': 'p >= 2, 1 <= a < p, 2*p <= n+a',
    'uniform_witness_with_exact_core_proved': True,
    'fresh_kernel_replay': True,
    'verified_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'lean_version': version,
    'public_proved_declarations_audited': len(reports),
    'allowed_axioms': sorted(allowed),
    'reports': reports,
    'sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
    'unproved_targets': [],
    'final_theorems': ['Bipanchromatic.sharp_range', 'Bipanchromatic.sharp_range_witness'],
}
(root / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k not in {'reports', 'sha256'}}, indent=2))
