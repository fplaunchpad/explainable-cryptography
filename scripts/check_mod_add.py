#!/usr/bin/env python3
"""Actual reduced-add controller versus independent modular arithmetic."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.BinaryModAddMachine
open ExplainableCrypto.Helios.Computational BinaryModAddMachine
private def mutated (m : Nat) (l : Fin 42) :=
  if m == 1 && l == 0 then enter 3
  else if m == 2 && l == copyLabel 0 0 then enter (subLabel 1 0)
  else if m == 3 && l == 2 then .push 6 (fun _ => false) (program l)
  else if m == 4 && l == 4 then .load (fun _ => 2) .halt
  else program l
private def word (s : String) := if s == "-" then [] else s.toList.map (· == '1')
private def bits (w : List Bool) := String.ofList (w.map (fun b => if b then '1' else '0'))
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
    let mut cfg := start (word p[1]!) (word p[2]!) (word p[3]!)
    let mut used := 0
    let mut charge := 0
    for _ in [:10000] do
      if cfg.l.isNone then break
      charge := charge+BitOracleMachine.localCost (mutated mutation (cfg.l.getD 0))
      cfg := TM2ReturnLink.tick (mutated mutation) cfg
      used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,"0",
      String.intercalate "/" ((List.ofFn cfg.stk).map bits)])
    output.flush
'''

def bits(n):return bin(n)[2:][::-1] if n else ''

def fixtures():
    cases=[(p,x,r) for p in range(1,17) for x in range(p) for r in range(p)]
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(64):
            p=rng.randrange(1,2**rng.randrange(1,33))
            cases.append((p,rng.randrange(p),rng.randrange(p)))
    for width in (7,8,15,16,31,32,63,64):
        for p in (2**width-1,2**width,2**width+1):
            for x,r in ((0,0),(0,p-1),(p-1,0),(p-1,p-1),(1,p-1)):
                cases.append((p,x,r))
    return cases

def main():
    cases=fixtures();runner=Runner(DRIVER,'ModAddNative')
    def execute(mut,c):
        p,x,r=c
        return runner.run(mut,bits(r),(bits(p-x) or '-')+' '+bits(p))
    def good(c,a):
        p,x,r=c;clock=26*p.bit_length()+24
        return (a['halted'] and a['memory']==2 and a['queries']==0 and
            a['steps']<=clock and a['charge']<=32*clock and
            a['words']==[bits((r+x)%p),bits(p-x),'','','','',bits(p),''])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        witness=(3,1,1)
        for mut,name in ((1,'skip_underflow_path'),(2,'omit_complement_copy'),(3,'corrupt_modulus'),(4,'omit_result_restore')):
            a=execute(mut,witness)
            assert not good(witness,a),(name,a)
            report['mutants'][name]=dict(p=3,x=1,r=1,actual=a)
        for i,c in enumerate(cases):
            a=execute(0,c)
            assert good(c,a),(i,c,a)
            if (i+1)%256==0:print(f'Checked {i+1}/{len(cases)} reduced additions',flush=True)
        report['status']='pass'
    finally:
        runner.close()
        (OUT/'mod-add-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
