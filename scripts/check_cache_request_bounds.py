#!/usr/bin/env python3
"""Native refutation gate for the existing request-clock cubic cap.

The clock is evaluated by the actual Lean definition. Python computes the cap
from integer bit lengths independently. The reported fixed probe factor is the
existing code-access constant; no measured runtime is substituted for it.
"""
import json
import random
import subprocess
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'tmp/concrete-helios'
SEEDS = (606, 20260914, 118)
SAMPLES = 200
DRIVER = r'''import ExplainableCrypto.Helios.Computational.CacheRequestMachineRun
open ExplainableCrypto.Helios.Computational

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn s!"FACTOR {TM2TapeRuns.codeAccesses CacheRoutineCode.readCode}"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let xs := line.trimAscii.toString.splitOn " " |>.map String.toNat!
    output.putStrLn (toString (CacheRequestMachine.loadedClock xs[0]! xs[1]! xs[2]! xs[3]! xs[4]! xs[5]!))
    output.flush
'''


def cap(xs, factor, omit=None):
    p, q, k, c, l, slack = xs
    components = [p.bit_length(), q.bit_length(), k, c, l, slack]
    if omit is not None:
        components[omit] = 0
    return 1000000*(factor+1)*(sum(components)+1)**3


def cases():
    result = [('zero', (0, 0, 0, 0, 0, 0))]
    for n in (1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 255, 256, 1023, 1024, 8192):
        result.extend((f'unbalanced_{i}', tuple(n if j == i else 0 for j in range(6))) for i in range(6))
        result.append(('balanced', (n,)*6))
    for width in (1, 2, 3, 8, 32, 64, 256, 1024, 4096, 8192):
        for offset in (-1, 0, 1):
            big = 2**width+offset
            result.extend([('large_p_width', (big, 1, 0, 0, 0, 0)),
                           ('large_q_width', (1, big, 0, 0, 0, 0))])
    result.append(("public_width_kernel_control", (2**4096, 0, 0, 0, 0, 0)))
    for width in (32768, 65536):
        result.append(("large_p_width_omission_control", (2**width, 1, 0, 0, 0, 0)))
    for i in (2, 3, 4):
        for value in (2**20, 2**32, 2**64, 2**256):
            result.append(('large_loaded_length', tuple(value if j == i else 0 for j in range(6))))
    for seed in SEEDS:
        rng = random.Random(seed)
        for _ in range(SAMPLES):
            widths = [rng.choice((0, 1, 2, 3, 7, 8, 31, 64, 256, 1024, 4096)) for _ in range(2)]
            p, q = [rng.getrandbits(w) for w in widths]
            lengths = [rng.choice((0, 1, 2, 7, 16, 255, 1024, 65536, 2**32)) for _ in range(3)]
            result.append((f'seed_{seed}', (p, q, *lengths, rng.choice((0, 1, 3, 16, 255, 1024)))))
    return result


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / 'CacheRequestBoundsNative.lean'
    path.write_text(DRIVER)
    fixtures = cases()
    process = subprocess.Popen(['lake', 'env', 'lean', '--run', str(path)], cwd=ROOT,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
    line = process.stdout.readline().strip()
    if not line.startswith('FACTOR '):
        process.kill()
        raise RuntimeError('Native driver did not start: '+line+'\n'+process.stdout.read())
    factor = int(line.split()[1])
    report = dict(status='failed', cases=len(fixtures), seeds=list(SEEDS), samples_per_seed=SAMPLES,
                  discarded=0, gave_up=0, probe_access_factor=factor, mutants={})
    try:
        for index, (category, xs) in enumerate(fixtures):
            process.stdin.write(' '.join(map(str, xs))+'\n')
            process.stdin.flush()
            actual = int(process.stdout.readline())
            bound = cap(xs, factor)
            if actual > bound:
                report['failure'] = dict(index=index, category=category, input=xs, actual=actual, cap=bound)
                raise AssertionError('Cubic cap refuted: '+json.dumps(report['failure']))
            for name, omitted in [('omit_loaded_key_length', 2), ('omit_public_p_width', 0)]:
                if name not in report['mutants'] and actual > cap(xs, factor, omitted):
                    report['mutants'][name] = dict(index=index, category=category, input=xs,
                        actual=actual, cap=cap(xs, factor, omitted),
                        minimality='first directed/seeded witness; not globally minimized')
        if len(report['mutants']) != 2:
            raise AssertionError('An omission mutant was not detected')
        report['status'] = 'passed'
    finally:
        (OUT / 'cache-request-bounds-native-report.json').write_text(json.dumps(report, indent=2)+'\n')
        process.stdin.close()
        process.wait(timeout=10)
    print(f"Passed {len(fixtures)} actual Lean clock fixtures; seeds={SEEDS}; discards=0; gaveUp=0; A={factor}")
    for name, witness in report['mutants'].items():
        print(f"Detected {name} at fixture {witness['index']} ({witness['category']})")


if __name__ == '__main__':
    main()
