#!/usr/bin/env python3
"""Build and audit public computational theorems in a selected target by exact name."""
import argparse
import json
from pathlib import Path
import re
import runpy
import subprocess
from helios_targets import CASE_STUDY, FULL, inventory, module_path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'tmp/computational-audit'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINTS = {
    'ExplainableCrypto.Helios.Computational.' + name for name in (
        'ballotSecrecyGame_proofReuse_success',
        'proofReuse_attack_success',
        'executeRepairedAttack_rejected',
        'repairedHonestPair_decrypts',
        'repairedHonestPair_rejection_le',
        'ElectionSecurityFamily.Family.ballot_secrecy',
    )
}


def run_logged(command, path):
    with path.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Command failed; see {path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=['case-study', 'full'], default='case-study',
                        help='Default retained case study, or full retained + deferred development')
    parser.add_argument('--build-log', type=Path,
                        help='Reuse a completed current-worktree lake build log instead of rebuilding')
    args = parser.parse_args()
    out = OUT / args.scope
    out.mkdir(parents=True, exist_ok=True)
    _, retained, all_modules = inventory()
    modules = retained if args.scope == 'case-study' else all_modules
    target = CASE_STUDY if args.scope == 'case-study' else FULL
    build_log = args.build_log or out / 'lake-build.log'
    if args.build_log is None:
        run_logged(['lake', 'build'] + ([] if args.scope == 'case-study' else ['HeliosExecution']), build_log)
    build = build_log.read_text()
    if 'Build completed successfully' not in build or re.search(r'error:|warning:|sorryAx', build):
        raise RuntimeError(f'Build is not clean and complete: {build_log}')
    declarations = runpy.run_path(str(ROOT / 'scripts/check_helios_claims.py'))['declarations']
    names = sorted({name for module in modules for name in declarations(module_path(module))})
    if not ENDPOINTS <= set(names):
        raise RuntimeError(f'Missing published endpoints: {sorted(ENDPOINTS - set(names))}')
    source = out / 'Audit.lean'
    source.write_text(f'import {target}\n' +
                      ''.join(f'#print axioms {name}\n' for name in names))
    (out / 'expected.txt').write_text('\n'.join(names) + '\n')
    log = out / 'axioms.log'
    run_logged(['lake', 'env', 'lean', str(source)], log)
    text = log.read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
    actual = {name for name, _ in reports} | set(empty)
    axioms = {a.strip() for _, body in reports for a in body.split(',') if a.strip()}
    if actual != set(names) or len(reports) + len(empty) != len(names):
        raise RuntimeError('Axiom reports do not cover the exact public declaration set')
    if not axioms <= ALLOWED or re.search(r'error:|warning:|sorryAx', text):
        raise RuntimeError(f'Unexpected axioms or diagnostics; see {log}')
    summary = dict(scope=args.scope, modules=len(modules), public_theorems=len(names),
                   exact_name_coverage=True, endpoints=sorted(ENDPOINTS), axioms=sorted(axioms))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
