#!/usr/bin/env python3
"""Independent request-prestate checks against the actual Lean observer.

Build CacheRequestPrefixes first. Tests use the existing typed p=23/q=11 keys,
adaptive original sources, and explicit uniform-answer streams. This bounded
native campaign validates capture/erasure fixtures, not computational secrecy.
"""
import ast
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'tmp/concrete-helios'
SEEDS = (118, 198, 20260914)

DRIVER = r'''import ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
import ExplainableCrypto.Helios.Computational.CacheHashCoins
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec
open BallotCacheCodecControls
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
abbrev F := ZMod 11
abbrev G := PrimeGroup 23 11
private def source : List Nat → Nat → BallotOracleComp F G (List Nat)
  | [], _ => pure []
  | op::ops, last => do
    let value ← if op == 2 then
      (fun x : Fin 4 => x.val) <$> liftM ((BallotOracleSpec F G).query (.inl 3))
    else
      let k := if op == 3 then (if last % 2 == 0 then key else otherKey)
        else if op == 0 then key else otherKey
      (fun a : F => a.val) <$> (liftM ((BallotOracleSpec F G).query (.inr k)) : BallotOracleComp F G F)
    let rest ← source ops value
    pure (value::rest)
private def impl (mutation : Nat) : QueryImpl (BallotOracleSpec F G)
    (StateT (CacheRequestPrefixes.State F G) (OracleComp (FiatShamir.Fork.wrappedSpec F))) :=
  if mutation == 0 then CacheRequestPrefixes.impl else fun t s => do
    let out ← (ballotFiniteLoggedImpl t).run s.1
    let skip :=  match t with
      | .inl _ => mutation == 2
      | .inr k => mutation == 1 && (s.1.1.lookup k).isSome
    let captured := if mutation == 3 then out.2 else s.1
    pure (out.1,(out.2,if skip then s.2 else s.2++[(t,captured)]))
private def handler : QueryImpl unifSpec (StateT (List Nat) Id) := fun n tape =>
  (⟨tape.headD 0 % (n+1),Nat.mod_lt _ (by omega)⟩,tape.tail)
private def keyId (k : BallotForkPoint G) : Nat := if k == key then 0 else 1
private def cacheView (c : BallotFiniteCache F G) := c.entries.map (fun e => (keyId e.1,e.2.val))
private def logView (l : List (Unit × BallotForkPoint G)) := l.map (fun e => keyId e.2)
private def eventView (e : CacheRequestPrefixes.Event F G) :=
  ((match e.1 with | .inl _ => 2 | .inr k => keyId k),cacheView e.2.1,logView e.2.2)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "READY"
  stdout.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let parts := line.trimAscii.toString.splitOn " "
    let mutation := parts[0]!.toNat!
    let cacheId := parts[1]!.toNat!
    let logId := parts[2]!.toNat!
    let ops := if parts[3]! == "-" then [] else parts[3]!.toList.map (fun c => c.toNat-48)
    let tape := if parts[4]! == "-" then [] else (parts[4]!.splitOn ",").map String.toNat!
    let c : BallotFiniteCache F G := if cacheId == 0 then ∅
      else if cacheId == 1 then (∅ : BallotFiniteCache F G).insert key 3 else cache
    let l := if logId == 0 then [] else [((),otherKey),((),key)]
    let computation := (simulateQ (impl mutation) (source ops 0)).run ((c,l),[])
    let (out,remaining) := (simulateQ handler (simulateQ CacheHashCoins.exactChallenge computation)).run tape
    stdout.putStrLn ((String.intercalate "|" [reprStr out.1,reprStr (cacheView out.2.1.1),
      reprStr (logView out.2.1.2),reprStr (out.2.2.map eventView),reprStr remaining]).replace "\n" " ")
    stdout.flush
'''


def expected(cache_id, log_id, ops, tape):
    cache = ([], [(0, 3)], [(1, 5), (0, 3)])[cache_id].copy()
    log = [] if log_id == 0 else [1, 0]
    remaining = list(tape)
    answers, events = [], []
    last = 0
    for op in ops:
        request = (last % 2) if op == 3 else op
        events.append((request, cache.copy(), log.copy()))
        if request == 2:
            value = remaining.pop(0) % 4
        else:
            value = next((v for k, v in cache if k == request), None)
            if value is None:
                value = remaining.pop(0) % 11
                cache.insert(0, (request, value))
                log.append(request)
        answers.append(value)
        last = value
    return [answers, cache, log, events, remaining]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    driver = OUT / 'CacheRequestPrefixesNative.lean'
    driver.write_text(DRIVER)
    cases = []
    for length in range(4):
        for ops, cache_id, log_id in itertools.product(itertools.product(range(4), repeat=length), range(3), range(2)):
            cases.append((cache_id, log_id, list(ops), list(range(5, 5+length))))
    for seed in SEEDS:
        rng = random.Random(seed)
        for _ in range(256):
            length = rng.randrange(1, 21)
            cases.append((rng.randrange(3), rng.randrange(2), [rng.randrange(4) for _ in range(length)],
                          [rng.randrange(1000) for _ in range(length)]))
    process = subprocess.Popen(['lake', 'env', 'lean', '--run', str(driver)], cwd=ROOT,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
    try:
        line = process.stdout.readline()
        if line.strip() != 'READY':
            raise RuntimeError('Lean driver failed to start: '+line+process.stdout.read())

        def execute(mutation, case):
            cache_id, log_id, ops, tape = case
            process.stdin.write(f"{mutation} {cache_id} {log_id} {''.join(map(str, ops)) or '-'} {','.join(map(str, tape)) or '-'}\n")
            process.stdin.flush()
            line = process.stdout.readline()
            if not line:
                raise RuntimeError('Native driver stopped before returning a result')
            return [ast.literal_eval(part) for part in line.strip().split('|')]

        for index, case in enumerate(cases):
            actual, wanted = execute(0, case), expected(*case)
            if actual != wanted:
                raise AssertionError(dict(index=index, case=case, expected=wanted, actual=actual))
        mutations = []
        for mutation, name in [(1, 'omit_hit'), (2, 'omit_uniform'), (3, 'record_poststate')]:
            for index, case in enumerate(cases):
                actual, wanted = execute(mutation, case), expected(*case)
                if actual != wanted:
                    mutations.append(dict(name=name, index=index, case=case, expected=wanted, actual=actual))
                    break
            else:
                raise AssertionError('Mutation survived: '+name)
        report = dict(status='passed', cases=len(cases), seeds=SEEDS, samples_per_seed=256,
                      discarded=0, gave_up=0, mutations=mutations,
                      scope='finite original-source prestate snapshots, full final state and unused answer stream')
        (OUT/'cache-request-prefixes-native-report.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k != 'mutations'}, indent=2))
        print('Detected:', ', '.join(m['name'] for m in mutations))
    finally:
        process.stdin.close()
        if process.wait(timeout=30) and sys.exc_info()[0] is None:
            raise RuntimeError('Native driver failed')


if __name__ == '__main__':
    main()
