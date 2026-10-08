#!/usr/bin/env python3
"""Check actual default imports against case-study roots, and full target coverage.

Run after lake build (and after lake build HeliosExecution when --full is used).
The Lean environment checks are independent of the source import-graph traversal.
"""
import argparse
import json
import subprocess
import tomllib
from helios_targets import ROOT, FULL, inventory, computational, closure


def environment_modules(module, out):
    source = out / (module.split('.')[-1] + 'Imports.lean')
    source.write_text(f'import {module}\nimport Lean\n' + '''run_elab do
  for name in (← Lean.getEnv).header.moduleNames do
    if "ExplainableCrypto.Helios.Computational.".isPrefixOf name.toString then
      Lean.logInfo m!"COMPUTATIONAL_MODULE {name}"
''')
    result = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (source.with_suffix('.log')).write_text(result.stdout)
    if result.returncode or 'error:' in result.stdout or 'warning:' in result.stdout:
        raise RuntimeError(f'Lean import inspection failed: {source.with_suffix(".log")}')
    return {line.split('COMPUTATIONAL_MODULE ', 1)[1].strip()
            for line in result.stdout.splitlines() if 'COMPUTATIONAL_MODULE ' in line}


def same(actual, expected, label):
    if actual != expected:
        raise RuntimeError(f'{label}: missing {sorted(expected - actual)}; extra {sorted(actual - expected)}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='Also inspect the built optional target')
    args = parser.parse_args()
    out = ROOT / 'tmp/helios-target-split'
    out.mkdir(parents=True, exist_ok=True)
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    libs = {lib['name']: lib for lib in config['lean_lib']}
    if config['defaultTargets'] != ['ExplainableCrypto']:
        raise RuntimeError('Unexpected default targets')
    for name, root in [('ExplainableCrypto', 'ExplainableCrypto'), ('HeliosExecution', FULL)]:
        lib = libs[name]
        if lib.get('roots', [name]) != [root] or lib.get('globs', [root]) != [root]:
            raise RuntimeError(f'{name} must build only its aggregate root and transitive imports')
    roots, retained, all_modules = inventory()
    same(computational(closure(['ExplainableCrypto'])), retained, 'Default source closure')
    same(environment_modules('ExplainableCrypto', out), retained, 'Actual default environment')
    if args.full:
        same(environment_modules(FULL, out), all_modules, 'Actual full environment')
    summary = dict(roots=roots, retained=sorted(retained), deferred=sorted(all_modules-retained),
                   default_environment_verified=True, full_environment_verified=args.full)
    (out / 'inventory.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(f'Targets verified: {len(roots)} explicit roots, {len(retained)} retained modules, '
          f'{len(all_modules-retained)} deferred modules; full environment checked: {args.full}')


if __name__ == '__main__':
    main()
