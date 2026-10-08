#!/usr/bin/env python3
"""Native refutation gate for the actual resident caller entry/return program.

Expected typed cache/log encodings and complete outputs are independently built
in Python. This finite campaign does not establish general source compilation.
Requires the CacheCallerMachine Lean target to have been built.
"""
import json
import random
import sys
from collections import Counter

sys.dont_write_bytecode = True
from check_cache_request_input import ROOT, OUT, Runner, nat_encode, fields_encode

SEEDS = (118, 198, 20260914)
PER_SEED = 64
CAP = 100000

DRIVER = r'''import ExplainableCrypto.Helios.Computational.CacheCallerMachine
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2+1))
  | .hash w => (w,(state.1,state.2+1))
private def localProgram (mutation : Nat) : Code 12 CacheCallerMachine.size 3 := fun label =>
  if mutation == 1 && label.val == 0 then
    .compute (CacheCallerMachine.enter (CacheCallerMachine.copyLabel 0))
  else if mutation == 2 && label.val == 1 then
    .compute (CacheCallerMachine.enter (CacheCallerMachine.requestLabel 0))
  else if mutation == 4 && label == CacheCallerMachine.returnLabel then
    .compute (.load (fun _ => 2) .halt)
  else CacheCallerMachine.localCode label
private def program (mutation : Nat) : Code 13 CacheCallerMachine.size 3 := fun label =>
  if mutation == 0 then CacheCallerMachine.code label
  else if mutation == 3 && label == CacheCallerMachine.returnLabel then
    .compute (.push 12 (fun _ => false)
      (TM2StackFrame.relocate CacheCallerMachine.layout CacheCallerMachine.returnGate))
  else BitOracleStackFrame.code CacheCallerMachine.layout (localProgram mutation) label
private def execute (mutation mode memory : Nat)
    (k c l r previous saved tape : List Bool) :
    Bool × Nat × Nat × Nat × Nat × List (List Bool) × List Bool := Id.run do
  let start := CacheCallerMachine.start k c l r previous saved
  let mut cfg := if mode == 0 then start else
    {start with l := some CacheCallerMachine.returnLabel, var := ⟨memory%3,by omega⟩}
  let mut coins := tape
  let mut queries := 0
  let mut charge := 0
  for steps in [:100000] do
    if cfg.l.isNone then
      return (true,cfg.var.val,steps,charge,queries,List.ofFn cfg.stk,coins)
    let (out,state) := (simulateQ handler (step (program mutation) cfg)).run (coins,queries)
    cfg := out.1
    coins := state.1
    queries := state.2
    charge := charge+out.2
  return (false,cfg.var.val,100000,charge,queries,List.ofFn cfg.stk,coins)
private def bits (word : List Bool) : String :=
  String.ofList (word.map (fun bit => if bit then '1' else '0'))
private def word (text : String) : List Bool :=
  if text == "-" then [] else text.toList.map (· == '1')
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let p := line.trimAscii.toString.splitOn " "
    let (halted,memory,steps,charge,queries,words,coins) := execute
      p[0]!.toNat! p[1]!.toNat! p[2]!.toNat!
      (word p[3]!) (word p[4]!) (word p[5]!) (word p[6]!)
      (word p[7]!) (word p[8]!) (word p[9]!)
    output.putStrLn (String.intercalate "|" [if halted then "halt" else "timeout",
      toString memory,toString steps,toString charge,toString queries,
      String.intercalate "/" (words.map bits),bits coins])
    output.flush
'''


class CallerRunner(Runner):
    def run_case(self, mutation, case):
        values = [mutation, case.get("mode", 0), case.get("initial_memory", 0)]
        values += [case[k] or "-" for k in ("key", "cache", "log", "record", "previous", "saved", "tape")]
        self.process.stdin.write(" ".join(map(str, values))+"\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline().rstrip("\n")
        p = line.split("|")
        if len(p) != 7:
            raise RuntimeError(f"Invalid native response: {line!r}")
        self.calls[mutation] += 1
        return dict(halted=p[0] == "halt", memory=int(p[1]), steps=int(p[2]),
                    charge=int(p[3]), queries=int(p[4]), words=p[5].split("/"),
                    remaining_coins=p[6])


def keys():
    rows = [[1]*8, [pow(2, n, 23) for n in range(1, 9)],
            [pow(2, n, 23) for n in (8, 1, 7, 2, 6, 3, 5, 4)]]
    assert all(0 < x < 23 and pow(x, 11, 23) == 1 for row in rows for x in row)
    return [fields_encode([nat_encode(x) for x in row]) for row in rows]


def cache_encode(entries):
    return fields_encode([fields_encode([key, nat_encode(value)]) for key, value in entries])


def make_case(entries, key, log, slack, previous, saved, tape, category):
    old = next((value for candidate, value in entries if candidate == key), None)
    used = 0 if old is not None else 4+slack
    assert len(tape) >= used
    value = old if old is not None else sum((b == "1") << i for i, b in enumerate(tape[:used])) % 11
    new_entries = entries if old is not None else [(key, value)]+entries
    new_log = log if old is not None else log+[key]
    record = "1"*slack+"0"+nat_encode(11)
    return dict(category=category, branch="hit" if old is not None else "miss",
        key=key, cache=cache_encode(entries), log=fields_encode(log), record=record,
        previous=previous, saved=saved, tape=tape, memory=2, queries=used,
        words=[""]*7+[nat_encode(value), key, cache_encode(new_entries), fields_encode(new_log), record, saved],
        remaining_coins=tape[used:])


def fixtures():
    ks = keys()
    cases = []
    for entries in ([], [(ks[0], 3)], [(ks[1], 0), (ks[0], 10)]):
        for key in ks:
            for log in ([], [ks[2], ks[0]]):
                for slack in (0, 2):
                    for previous, saved in (("", ""), ("0", "1"), ("10110", "00101")):
                        for tape in ("0"*16, "0110101101001011", "1"*16):
                            cases.append(make_case(entries, key, log, slack, previous, saved, tape, "directed"))
    for seed in SEEDS:
        rng = random.Random(seed)
        bits = lambda n: "".join(rng.choice("01") for _ in range(n))
        for _ in range(PER_SEED):
            entries = [(k, rng.randrange(11)) for k in rng.sample(ks, rng.randrange(4))]
            cases.append(make_case(entries, rng.choice(ks), [rng.choice(ks) for _ in range(rng.randrange(5))],
                rng.randrange(4), bits(rng.randrange(13)), bits(rng.randrange(17)), bits(20), f"seed_{seed}"))
    for memory in range(3):
        for previous, saved in (("", ""), ("0", "1"), ("10110", "00101")):
            c = make_case([(ks[0], 3)], ks[0], [ks[2], ks[0]], 2, previous, saved, "101001", "return_gate")
            c.update(mode=1, initial_memory=memory, memory=2 if memory == 2 else 0,
                     words=[""]*7+[previous,c["key"],c["cache"],c["log"],c["record"],saved],
                     queries=0, remaining_coins=c["tape"])
            cases.append(c)
    return cases


def differs(case, actual):
    return not actual["halted"] or any(case[k] != actual[k] for k in
        ("memory", "queries", "words", "remaining_coins"))


def minimize_auxiliary(runner, mutation, case):
    """Shrink old-answer and saved-word only; keep the typed crypto fixture fixed."""
    case = dict(case)
    while True:
        changed = False
        for field in ("previous", "saved"):
            for i in range(len(case[field])):
                candidate = dict(case)
                candidate[field] = case[field][:i]+case[field][i+1:]
                candidate["words"] = list(case["words"])
                candidate["words"][12] = candidate["saved"]
                if case.get("mode", 0):
                    candidate["words"][7] = candidate["previous"]
                if differs(candidate, runner.run_case(mutation, candidate)):
                    case, changed = candidate, True
                    break
            if changed:
                break
        if not changed:
            return case, runner.run_case(mutation, case)


def main():
    cases = fixtures()
    report = dict(status="failed", cases=len(cases), seeds=SEEDS, samples_per_seed=PER_SEED,
        discarded=0, gave_up=0, step_cap=CAP, coverage=dict(Counter(c["category"] for c in cases)),
        branches=dict(Counter(c["branch"] for c in cases if not c.get("mode"))), mutations=[])
    runner = CallerRunner(DRIVER, "CacheCallerEntryNative")
    try:
        maximum = 0
        for i, case in enumerate(cases):
            actual = runner.run_case(0, case)
            maximum = max(maximum, actual["steps"])
            if differs(case, actual):
                report["failure"] = dict(index=i, expected=case, actual=actual)
                raise AssertionError(f"Actual caller entry failed at fixture {i}: {report['failure']}")
            if case.get("mode") and (actual["steps"] != 1 or actual["charge"] != 3):
                raise AssertionError(f"Return gate cost mismatch at {i}: {actual}")
            if (i+1) % 64 == 0:
                print(f"Checked {i+1}/{len(cases)} actual caller-entry fixtures", flush=True)
        report["maximum_steps"] = maximum
        for mutation, name in ((1,"omit_previous_cleanup"),(2,"omit_cache_cleanup"),
                               (3,"corrupt_saved_port"),(4,"force_successful_return")):
            for i, case in enumerate(cases):
                if mutation == 4 and not case.get("mode"):
                    continue
                actual = runner.run_case(mutation, case)
                if differs(case, actual):
                    minimal, actual = minimize_auxiliary(runner, mutation, case)
                    report["mutations"].append(dict(mutation=mutation, name=name, index=i,
                        expected=minimal, actual=actual,
                        minimization="single-bit deletion fixed point in previous/saved words only; typed request/cache/log held fixed"))
                    break
            else:
                raise AssertionError(f"Mutation survived: {name}")
        report["status"] = "passed"
        print(f"Passed {len(cases)} actual caller-entry fixtures; maximum steps={maximum}; cap={CAP}")
        print(f"Coverage={report['coverage']}; branches={report['branches']}; zero discarded/gave-up")
        for m in report["mutations"]:
            print(f"Detected {m['name']} at {m['index']}; minimized previous={m['expected']['previous']!r}, saved={m['expected']['saved']!r}")
    finally:
        report["native_calls"] = dict(runner.calls)
        (OUT / "cache-caller-entry-native-report.json").write_text(json.dumps(report, indent=2)+"\n")
        runner.close()


if __name__ == "__main__":
    main()
