#!/usr/bin/env python3
"""Refute the actual Lean four-field request loader against independent Python codecs.

Requires `lake build ExplainableCrypto.Helios.Computational.CacheRequestInput`.
Runs native Lean with a finite step cap; this is validation, not a proof. No
kernel declarations or native-decide axioms are introduced by the test driver.
The default campaign treats payloads as opaque words and checks framing/routing.
With --wrapper (requiring the CacheRequestMachine build), the additional directed
campaign executes typed Helios request fixtures and malformed framing through
the complete guarded dispatcher. Neither campaign proves general rejection.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "tmp/concrete-helios"
SEEDS = (118, 20260914, 0xC6)
SAMPLES_PER_SEED = 128
STEP_CAP = 20000


def nat_encode(n: int) -> str:
    width = n.bit_length()
    return "1" * width + "0" + "".join(str((n >> i) & 1) for i in range(width))


def fields_encode(fields: list[str]) -> str:
    return nat_encode(len(fields)) + "".join(nat_encode(len(w)) + w for w in fields)


def nat_read(raw: str, position: int) -> tuple[int, int] | None:
    end = position
    while end < len(raw) and raw[end] == "1":
        end += 1
    if end == len(raw):
        return None
    width = end - position
    digits = raw[end + 1 : end + 1 + width]
    if len(digits) != width or (digits and digits[-1] != "1"):
        return None
    value = sum((digit == "1") << i for i, digit in enumerate(digits))
    return value, end + 1 + width


def expected(raw: str) -> list[str] | None:
    """Independent canonical decoder; successful words route to literal ports."""
    header = nat_read(raw, 0)
    if header is None or header[0] != 4:
        return None
    position = header[1]
    fields = []
    for _ in range(4):
        header = nat_read(raw, position)
        if header is None:
            return None
        length, position = header
        if length > len(raw) - position:
            return None
        fields.append(raw[position : position + length])
        position += length
    if position != len(raw):
        return None
    key, cache, log, record = fields
    return [cache, "", "", "", "", "", "", "", key, "", log, record]


DRIVER = r'''import ExplainableCrypto.Helios.Computational.CacheRequestInput
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT Nat Id) := fun r count =>
  match r with
  | .coin => (false,count+1)
  | .hash w => (w,count+1)
private def program (mutation : Nat) : Code 12 49 3 := fun label =>
  if mutation == 1 then
    match CacheRequestInput.code label with
    | .compute stmt => .compute (TM2FiniteCoordinates.translate
        (Equiv.swap (8 : Fin 12) 10) (Equiv.refl _) (Equiv.refl _) stmt)
    | other => other
  else if mutation == 2 && label.val == 11 then
    .compute (.load (fun _ => 0) (.goto (fun _ => 12)))
  else if mutation == 3 && label.val == 12 then
    .compute (.load (fun _ => 2) .halt)
  else CacheRequestInput.code label
private structure Result where
  halted : Bool
  memory : Nat
  steps : Nat
  charge : Nat
  queries : Nat
  words : List (List Bool)
private def execute (mutation : Nat) (raw : List Bool) : Result := Id.run do
  let mut cfg := CacheRequestInput.start raw
  let mut queries := 0
  let mut charge := 0
  for steps in [:STEP_CAP] do
    if cfg.l.isNone then
      return ⟨true,cfg.var.val,steps,charge,queries,List.ofFn cfg.stk⟩
    let (out,count) := (simulateQ handler (step (program mutation) cfg)).run queries
    cfg := out.1
    charge := charge+out.2
    queries := count
  return ⟨false,cfg.var.val,STEP_CAP,charge,queries,List.ofFn cfg.stk⟩
private def bits (word : List Bool) : String :=
  String.ofList (word.map (fun bit => if bit then '1' else '0'))
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let parts := line.trimAscii.toString.splitOn " "
    let mutation := (parts[0]!).toNat!
    let raw := if parts[1]! == "-" then [] else (parts[1]!).toList.map (· == '1')
    let out := execute mutation raw
    output.putStrLn (String.intercalate "|" [if out.halted then "halt" else "timeout",
      toString out.memory,toString out.steps,toString out.charge,toString out.queries,
      String.intercalate "/" (out.words.map bits)])
    output.flush
'''.replace("STEP_CAP", str(STEP_CAP))


class Runner:
    def __init__(self, driver_text: str = DRIVER, name: str = "CacheRequestInputNative") -> None:
        OUT.mkdir(parents=True, exist_ok=True)
        driver = OUT / f"{name}.lean"
        driver.write_text(driver_text)
        self.process = subprocess.Popen(
            ["lake", "env", "lean", "--run", str(driver)], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, bufsize=1,
        )
        assert self.process.stdout is not None
        startup = []
        while True:
            line = self.process.stdout.readline()
            if line.strip() == "READY":
                break
            startup.append(line)
            if not line:
                raise RuntimeError("Lean driver failed to start:\n" + "".join(startup))
        self.calls = Counter()

    def run(self, mutation: int, raw: str, tape: str | None = None) -> dict:
        assert self.process.stdin is not None and self.process.stdout is not None
        extra = "" if tape is None else f" {tape or '-'}"
        self.process.stdin.write(f"{mutation} {raw or '-'}{extra}\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline().rstrip("\n")
        parts = line.split("|")
        if len(parts) not in (6, 7):
            raise RuntimeError(f"Invalid native response: {line!r}")
        self.calls[mutation] += 1
        result = dict(halted=parts[0] == "halt", memory=int(parts[1]), steps=int(parts[2]),
                      charge=int(parts[3]), queries=int(parts[4]), words=parts[5].split("/"))
        if len(parts) == 7:
            result["remaining_coins"] = parts[6]
        return result

    def close(self) -> None:
        if self.process.stdin:
            self.process.stdin.close()
        try:
            self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()


def discrepancy(raw: str, actual: dict) -> bool:
    wanted = expected(raw)
    if not actual["halted"] or actual["queries"] or len(actual["words"]) != 12:
        return True
    if wanted is None:
        return actual["memory"] != 0
    return actual["memory"] != 2 or actual["words"] != wanted


def fixtures() -> list[tuple[str, str]]:
    cases: list[tuple[str, str]] = []

    def valid(category: str, fields: list[str]) -> None:
        raw = fields_encode(fields)
        key, cache, log, record = fields
        direct_ports = [cache, "", "", "", "", "", "", "", key, "", log, record]
        if expected(raw) != direct_ports:
            raise AssertionError("Independent reference codec failed its source-field check")
        cases.append((category, raw))
    # All payload combinations over small words, including nonpalindromes.
    for fields in itertools.product(("", "0", "1", "01", "10"), repeat=4):
        valid("directed_valid", list(fields))
    for seed in SEEDS:
        rng = random.Random(seed)
        for _ in range(SAMPLES_PER_SEED):
            fields = ["".join(rng.choice("01") for _ in range(rng.choice(
                (0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64)))) for _ in range(4)]
            valid(f"seeded_valid_{seed}", fields)
    # Count mismatch is independent of whether enough field frames follow.
    for count in (0, 1, 2, 3, 5, 7, 8, 15, 16):
        for payload in ("", "0000", "".join(nat_encode(len(w))+w for w in ("01", "", "1", "10"))):
            cases.append(("wrong_outer_count", nat_encode(count)+payload))
    # Exhaustive bounded malformed/short byte prefixes, without implication discards.
    for size in range(11):
        for bits in itertools.product("01", repeat=size):
            cases.append(("short_raw", "".join(bits)))
    # Truncation at every bit position covers field header and payload failures.
    for fields in (["", "", "", ""], ["01", "1", "", "100"],
                   ["0"*8, "10"*8, "1"*3, "01"*16]):
        raw = fields_encode(fields)
        for cut in range(len(raw)):
            cases.append(("truncated_record", raw[:cut]))
        for suffix in ("0", "1", "01", "10", "1111"):
            cases.append(("trailing_suffix", raw+suffix))
    # Noncanonical length digits, unfinished unary header, and oversized payload.
    for phase in range(4):
        prefix = nat_encode(4)+"0"*phase
        for bad in ("1", "11", "100", "11000", nat_encode(3)+"01"):
            cases.append(("malformed_field", prefix+bad))
    return cases


def minimize(runner: Runner, mutation: int, raw: str) -> tuple[str, dict]:
    """Reach a fixed point under single-bit deletion and true-to-false changes."""
    while True:
        candidates = [raw[:i]+raw[i+1:] for i in range(len(raw))]
        candidates += [raw[:i]+"0"+raw[i+1:] for i, bit in enumerate(raw) if bit == "1"]
        for candidate in candidates:
            actual = runner.run(mutation, candidate)
            if discrepancy(candidate, actual):
                raw = candidate
                break
        else:
            return raw, runner.run(mutation, raw)


def main() -> None:
    cases = fixtures()
    coverage = Counter(category for category, _ in cases)
    runner = Runner()
    report = dict(seeds=list(SEEDS), samples_per_seed=SAMPLES_PER_SEED,
                  cases=len(cases), discarded=0, gave_up=0, step_cap=STEP_CAP,
                  coverage=dict(coverage), mutations=[], status="failed",
                  timeouts=0, unexpected_oracle_queries=0)
    try:
        maximum_steps = 0
        for index, (category, raw) in enumerate(cases):
            actual = runner.run(0, raw)
            maximum_steps = max(maximum_steps, actual["steps"])
            report["timeouts"] += not actual["halted"]
            report["unexpected_oracle_queries"] += actual["queries"]
            if discrepancy(raw, actual):
                minimal, minimized_actual = minimize(runner, 0, raw)
                report["failure"] = dict(index=index, category=category, raw=raw,
                    actual=actual, expected=expected(raw), minimized_raw=minimal,
                    minimized_actual=minimized_actual, minimized_expected=expected(minimal))
                raise AssertionError(f"Actual loader failure: {json.dumps(report['failure'])}")
        report["maximum_steps"] = maximum_steps
        report["accepted"] = sum(expected(raw) is not None for _, raw in cases)
        report["rejected"] = len(cases)-report["accepted"]
        print(f"Passed {len(cases)} actual-loader fixtures; accepted={report['accepted']}, "
              f"rejected={report['rejected']}, discarded=0, gaveUp=0", flush=True)
        names = {1: "swap_key_log_ports_8_10", 2: "skip_fourth_field_success_guard",
                 3: "ignore_trailing_suffix_guard"}
        for mutation, name in names.items():
            for index, (category, raw) in enumerate(cases):
                actual = runner.run(mutation, raw)
                if discrepancy(raw, actual):
                    minimal, minimized_actual = minimize(runner, mutation, raw)
                    witness = dict(mutation=mutation, name=name, index=index, category=category,
                        first_raw=raw, minimized_raw=minimal, expected=expected(minimal),
                        actual=minimized_actual,
                        minimality="fixed point under single-bit deletion and 1-to-0 substitution")
                    report["mutations"].append(witness)
                    print(f"Detected {name}; first={index}; minimized={minimal or '<empty>'}", flush=True)
                    break
            else:
                raise AssertionError(f"Undetected mutation {name}")
        report["status"] = "passed"
    finally:
        report["native_calls"] = dict(runner.calls)
        (OUT / "cache-request-input-native-report.json").write_text(json.dumps(report, indent=2)+"\n")
        runner.close()
    print(f"Seeds={list(SEEDS)}; maximum steps={report['maximum_steps']}; cap={STEP_CAP}")
    print(f"Report: {OUT / 'cache-request-input-native-report.json'}")


WRAPPER_CAP = 100000
WRAPPER_DRIVER = r'''import ExplainableCrypto.Helios.Computational.CacheRequestMachine
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2+1))
  | .hash w => (w,(state.1,state.2+1))
private def program (mutation : Nat) : Code 12 CacheRequestMachine.size 3 := fun label =>
  if mutation == 1 && label == CacheRequestMachine.gateLabel then
    .compute (.load (fun _ => 0) (.goto (fun _ => CacheRequestMachine.requestLabel 0)))
  else CacheRequestMachine.code label
private structure Result where
  halted : Bool
  memory : Nat
  steps : Nat
  charge : Nat
  queries : Nat
  words : List (List Bool)
  remaining : List Bool
private def execute (mutation : Nat) (raw tape : List Bool) : Result := Id.run do
  let mut cfg := CacheRequestMachine.start raw
  let mut queries := 0
  let mut charge := 0
  let mut coins := tape
  for steps in [:WRAPPER_CAP] do
    if cfg.l.isNone then
      return ⟨true,cfg.var.val,steps,charge,queries,List.ofFn cfg.stk,coins⟩
    let (out,state) := (simulateQ handler (step (program mutation) cfg)).run (coins,queries)
    cfg := out.1
    charge := charge+out.2
    coins := state.1
    queries := state.2
  return ⟨false,cfg.var.val,WRAPPER_CAP,charge,queries,List.ofFn cfg.stk,coins⟩
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
    let parts := line.trimAscii.toString.splitOn " "
    let out := execute (parts[0]!).toNat! (word parts[1]!) (word parts[2]!)
    output.putStrLn (String.intercalate "|" [if out.halted then "halt" else "timeout",
      toString out.memory,toString out.steps,toString out.charge,toString out.queries,
      String.intercalate "/" (out.words.map bits),bits out.remaining])
    output.flush
'''.replace("WRAPPER_CAP", str(WRAPPER_CAP))


def wrapper_fixtures() -> list[dict]:
    # Eight qth-root public coordinates form each typed BallotForkPoint key.
    # The identity and powers of 2 modulo 23 are independently checked members.
    p, q = 23, 11
    coordinates = ([1]*8, [pow(2, e, p) for e in range(1, 9)],
                   [pow(2, e, p) for e in (8, 1, 7, 2, 6, 3, 5, 4)])
    assert all(0 < x < p and pow(x, q, p) == 1 for row in coordinates for x in row)
    keys = [fields_encode([nat_encode(x) for x in row]) for row in coordinates]

    def encode_cache(entries: list[tuple[str, int]]) -> str:
        assert len({key for key, _ in entries}) == len(entries)
        assert all(0 <= value < q for _, value in entries)
        return fields_encode([fields_encode([key, nat_encode(value)]) for key, value in entries])

    caches = ([], [(keys[0], 3)], [(keys[1], 0), (keys[0], 10)])
    cases = []
    for entries, key, log, slack, tape in itertools.product(
        caches, keys, ([], [keys[2], keys[0]]), (0, 2),
        ("0"*16, "0110101101001011", "1"*16),
    ):
        record = "1"*slack+"0"+nat_encode(q)
        cache_word = encode_cache(entries)
        log_word = fields_encode(log)
        raw = fields_encode([key, cache_word, log_word, record])
        old = next((value for candidate, value in entries if candidate == key), None)
        used = 0 if old is not None else q.bit_length()+slack
        value = old if old is not None else sum((b == "1") << i for i, b in enumerate(tape[:used])) % q
        next_entries = entries if old is not None else [(key, value)]+entries
        next_log = log if old is not None else log+[key]
        final = ["", "", "", "", "", "", "", nat_encode(value), key, "",
                 fields_encode(next_log), record]
        final[9] = encode_cache(next_entries)
        cases.append(dict(category="typed_hit" if old is not None else "typed_miss",
                          raw=raw, tape=tape, memory=2, queries=used, words=final,
                          remaining_coins=tape[used:]))
    # Exact rejected states are independently derived: all four fields have
    # loaded, and a suffix remains on port 6 when the final framing guard fails.
    for case in [next(c for c in cases if c["category"] == "typed_hit"),
                 next(c for c in cases if c["category"] == "typed_miss")]:
        for suffix in ("0", "1", "01"):
            ports = expected(case["raw"])
            assert ports is not None
            ports[6] = suffix
            cases.append(dict(category="trailing_suffix", raw=case["raw"]+suffix,
                tape=case["tape"], memory=0, queries=0, words=ports,
                remaining_coins=case["tape"]))
    # Header failure consumes through the first mismatching bit; EOF consumes
    # nothing further. Work ports stay blank and no request is entered.
    for raw in [nat_encode(n) for n in (0, 1, 2, 3, 5, 8)]+[nat_encode(4)[:n] for n in range(7)]:
        position = 0
        for wanted in "1110001":
            if position == len(raw):
                break
            got = raw[position]
            position += 1
            if got != wanted:
                break
        ports = [""]*12
        ports[6] = raw[position:]
        cases.append(dict(category="wrong_or_short_header", raw=raw, tape="101001",
            memory=0, queries=0, words=ports, remaining_coins="101001"))
    return cases


def wrapper_discrepancy(case: dict, actual: dict) -> bool:
    return not actual["halted"] or any(actual[field] != case[field] for field in
        ("memory", "queries", "words", "remaining_coins"))


def wrapper_main() -> None:
    cases = wrapper_fixtures()
    runner = Runner(WRAPPER_DRIVER, "CacheRequestWrapperNative")
    report = dict(status="failed", cases=len(cases), coverage=dict(Counter(c["category"] for c in cases)),
        p=23, q=11, slack=[0, 2], discarded=0, gave_up=0, step_cap=WRAPPER_CAP,
        scope="directed finite wrapper campaign; every final port and remaining coin checked")
    try:
        max_steps = 0
        for index, case in enumerate(cases):
            actual = runner.run(0, case["raw"], case["tape"])
            max_steps = max(max_steps, actual["steps"])
            if wrapper_discrepancy(case, actual):
                report["failure"] = dict(index=index, expected=case, actual=actual)
                raise AssertionError(f"Wrapper failure: {json.dumps(report['failure'])}")
        report["maximum_steps"] = max_steps
        # Try the concrete trailing-suffix witnesses first: their expected
        # rejected states are fully determined, and the loaded cache can hit.
        for index, case in enumerate(cases):
            if case["category"] != "trailing_suffix":
                continue
            actual = runner.run(1, case["raw"], case["tape"])
            if wrapper_discrepancy(case, actual):
                report["mutant"] = dict(name="dispatch_failed_loader", index=index,
                    expected=case, actual=actual,
                    witness_scope="one-bit trailing suffix on a typed hit request; no global minimality claim")
                break
        else:
            raise AssertionError("Wrapper gate mutant was not detected")
        report["status"] = "passed"
        print(f"Passed {len(cases)} actual-wrapper fixtures; coverage={report['coverage']}")
        print(f"Detected dispatch-failed-loader mutation at fixture {report['mutant']['index']}; "
              f"maximum steps={max_steps}; cap={WRAPPER_CAP}")
    finally:
        report["native_calls"] = dict(runner.calls)
        (OUT / "cache-request-wrapper-native-report.json").write_text(json.dumps(report, indent=2)+"\n")
        runner.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wrapper", action="store_true", help="also check the built guarded loader/request wrapper")
    args = parser.parse_args()
    main()
    if args.wrapper:
        wrapper_main()
