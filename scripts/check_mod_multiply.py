#!/usr/bin/env python3
"""Actual loaded multiplier versus independent integer products and bit order."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT
from check_mod_add import bits

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.BinaryModMultiply
open ExplainableCrypto.Helios.Computational BinaryModMultiply
private def mutated (m : Nat) (l : Fin 86) :=
  if m == 1 && l == copyLabel 0 then enter (prepLabel 0)
  else if m == 2 && l == 5 then move 3 0 5 1
  else if m == 3 && l == doubleLabel false 4 then enter (doubleLabel false 0)
  else if m == 3 && l == doubleLabel true 4 then enter (doubleLabel true 0)
  else if m == 4 && l == 8 then .load (fun _ => 2) .halt
  else if m == 5 && l == 0 then enter 1
  else if m == 5 && l == 1 then
    TM2FiniteCoordinates.translate (Equiv.swap (8 : Fin 11) 9) (Equiv.refl _) (Equiv.refl _) (control 1)
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
    for _ in [:200000] do
      if cfg.l.isNone then break
      charge := charge+BitOracleMachine.localCost (mutated mutation (cfg.l.getD 0))
      cfg := TM2ReturnLink.tick (mutated mutation) cfg
      used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,"0",
      String.intercalate "/" ((List.ofFn cfg.stk).map bits)])
    output.flush
'''

def fixtures():
    cases=[(p,x,bits(y)) for p in range(1,9) for x in range(p) for y in range(16)]
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(32):
            p=rng.randrange(1,2**rng.randrange(1,33))
            raw=''.join(rng.choice('01') for _ in range(rng.randrange(17)))
            cases.append((p,rng.randrange(p),raw))
    for width in (7,8,15,16,31,32,63,64):
        for p in (2**width-1,2**width,2**width+1):
            for x,raw in ((0,''),(0,'1011'),(p-1,''),(p-1,'1011'),(p-1,'11110000')):
                cases.append((p,x,raw))
    return cases

def main():
    cases=fixtures();runner=Runner(DRIVER,'ModMultiplyNative')
    def execute(mut,c):
        p,x,raw=c
        return runner.run(mut,bits(x),(raw or '-')+' '+bits(p))
    def good(c,a):
        p,x,raw=c;y=sum(int(b)<<i for i,b in enumerate(raw))
        clock=9*p.bit_length()+11+len(raw)*(34*p.bit_length()+38)
        return (a['halted'] and a['memory']==2 and a['queries']==0 and
            a['steps']<=clock and a['charge']<=32*clock and
            a['words']==[bits(x*y%p),'','','','','',bits(p),'','','',bits(x)])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        witness=(23,4,'1011')
        for mut,name in ((1,'omit_modulus_copy'),(2,'omit_one_bit_addition'),(3,'omit_doubling'),(4,'retain_complement'),(5,'wrong_bit_order')):
            a=execute(mut,witness)
            assert not good(witness,a),(name,a)
            report['mutants'][name]=dict(p=23,x=4,raw='1011',actual=a)
        for i,c in enumerate(cases):
            a=execute(0,c)
            assert good(c,a),(i,c,a)
            if (i+1)%128==0:print(f'Checked {i+1}/{len(cases)} loaded multiplications',flush=True)
        report['status']='pass'
    finally:
        runner.close()
        (OUT/'mod-multiply-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
