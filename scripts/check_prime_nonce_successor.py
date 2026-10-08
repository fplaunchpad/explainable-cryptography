#!/usr/bin/env python3
"""Refute the actual nonce successor code against independent integer fixtures."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT, nat_encode

DRIVER = r'''import ExplainableCrypto.Helios.Computational.PrimeNonceMachine
open ExplainableCrypto.Helios.Computational Turing.TM2 PrimeNonceMachine
private def code (mutation : Nat) (l : Fin 26) :=
  if mutation == 1 && l == prepLabel 10 then program (prepLabel 12)
  else if mutation == 2 && l == 16 then
    Stmt.goto (fun _ : Fin 3 => writeLabel 5)
  else if mutation == 3 && l == 25 then
    Stmt.push (5 : Fin 8) (fun _ : Fin 3 => false) Stmt.halt
  else program l
private def bits (word : List Bool) : String :=
  String.ofList (word.map (fun b => if b then '1' else '0'))
private def word (s : String) : List Bool :=
  if s == "-" then [] else s.toList.map (· == '1')
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let p := line.trimAscii.toString.splitOn " "
    let mutation := p[0]!.toNat!
    let mut cfg := start (word p[1]!) ![word p[2]!,word p[3]!,word p[4]!]
    let mut used := 0
    let mut charge := 0
    for _ in [:10000] do
      match cfg.l with
      | none => break
      | some l =>
        charge := charge + BitOracleMachine.localCost (code mutation l)
        cfg := TM2ReturnLink.tick (code mutation) cfg
        used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,"0",
      String.intercalate "/" ((List.ofFn cfg.stk).map bits)])
    output.flush
'''

def main():
    cases = [(n,"101",["001","110","01"]) for n in range(256)]
    for w in range(1,129):
        for n in (2**w-1,2**w,2**w+1):
            cases.append((n,"",["1","0","101"]))
    for seed in (118,606,20260914):
        rng = random.Random(seed)
        for _ in range(128):
            word = lambda: ''.join(rng.choice('01') for _ in range(rng.randrange(33)))
            cases.append((rng.getrandbits(rng.randrange(257)),word(),[word(),word(),word()]))
    runner = Runner(DRIVER,"PrimeNonceSuccessorNative")
    def run(m,case):
        n,suffix,frame = case
        return runner.run(m,nat_encode(n)+suffix,' '.join(w or '-' for w in frame))
    def good(case,actual):
        n,suffix,frame = case
        cap = 5*n.bit_length()+6*(n+1).bit_length()+16
        return (actual['halted'] and actual['memory']==2 and actual['queries']==0
            and actual['words']==['','','','',nat_encode(n+1)+suffix,*frame]
            and actual['steps']<=cap and actual['charge']<=32*cap)
    report = dict(cases=len(cases),seeds=[118,606,20260914],discarded=0,gaveUp=0,mutants={})
    try:
        # Known defects are checked before the candidate campaign.
        for m,name in ((1,'bypass_increment'),(2,'skip_width_clear'),(3,'corrupt_frame')):
            case = (1,'',['','',''])
            actual=run(m,case)
            assert not good(case,actual), (name,actual)
            # Minimize index; suffix/frame already empty.
            smaller=(0,'',['','',''])
            if not good(smaller,run(m,smaller)):
                case=smaller
                actual=run(m,case)
            report['mutants'][name]=dict(index=case[0],actual=actual)
        for i,case in enumerate(cases):
            actual=run(0,case)
            assert good(case,actual),(i,case,actual)
        report['status']='pass'
    finally:
        runner.close()
        (OUT/'prime-nonce-successor-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
