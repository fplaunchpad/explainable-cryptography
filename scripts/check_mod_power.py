#!/usr/bin/env python3
"""Actual loaded exponentiation versus independent integer modular powers."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT
from check_mod_add import bits

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.BinaryModPower
open ExplainableCrypto.Helios.Computational BinaryModPower
private def mutated (m : Nat) (l : Fin 192) :=
  if m == 1 && l == 1 then .push 0 (fun _ => false) (enter 2)
  else if m == 2 && l == 2 then
    .peek 12 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (enter 6))
  else if m == 3 && l == 6 then
    .pop 12 (fun _ b => BinaryModuloCode.memory b) (enter 2)
  else if m == 4 && l == 1 then .push 13 (fun _ => false) (control 1)
  else if m == 5 && l == 0 then enter 1
  else if m == 5 && (l == copyLabel 0 0 || l == copyLabel 0 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (8 : Fin 15) 12) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 6 && l == 1 then .push 14 (fun _ => false) (control 1)
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
    let mut cfg := start (word p[1]!) (word p[2]!) (word p[3]!) (word p[4]!)
    let mut used := 0
    let mut charge := 0
    for _ in [:2000000] do
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
    cases=[(p,x,bits(e),'10110') for p in range(2,9) for x in range(p) for e in range(8)]
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(32):
            p=rng.randrange(2,2**rng.randrange(2,25))
            raw=''.join(rng.choice('01') for _ in range(rng.randrange(9)))
            context=''.join(rng.choice('01') for _ in range(rng.randrange(17)))
            cases.append((p,rng.randrange(p),raw,context))
    for width in (7,8,15,16,31,32):
        for p in (2**width-1,2**width,2**width+1):
            for x,raw in ((0,''),(0,'1011'),(p-1,'1011'),(p-2,'11000')):
                cases.append((p,x,raw,'01101'))
    cases.extend([(23,2,'11','101'),(23,4,'11','101'),(23,4,'1011','101')])
    return cases

def main():
    cases=fixtures();runner=Runner(DRIVER,'ModPowerNative')
    def execute(mut,c):
        p,x,raw,context=c
        return runner.run(mut,bits(x),(raw or '-')+' '+bits(p)+' '+(context or '-'))
    def good(c,a):
        p,x,raw,context=c;e=sum(int(b)<<i for i,b in enumerate(raw));w=p.bit_length()
        multiply=9*w+11+w*(34*w+38)
        clock=3*len(raw)+5+len(raw)*(2*multiply+12*w+16)
        return (a['halted'] and a['memory']==2 and a['queries']==0 and
            a['steps']<=clock and a['charge']<=32*clock and
            a['words']==[bits(pow(x,e,p)),'','','','','',bits(p),'','','','',bits(x),'',raw,context])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        for mut,name,c in (
            (1,'zero_initialization',(23,4,'','101')),
            (2,'omit_squaring',(23,4,'1011','101')),
            (3,'omit_one_bit_product',(23,4,'1011','101')),
            (4,'corrupt_saved_exponent',(23,4,'1011','101')),
            (5,'wrong_bit_order',(23,4,'1011','101')),
            (6,'corrupt_saved_context',(23,4,'1011','101'))):
            a=execute(mut,c)
            assert not good(c,a),(name,a)
            report['mutants'][name]=dict(input=c,actual=a)
        for i,c in enumerate(cases):
            a=execute(0,c)
            assert good(c,a),(i,c,a)
    finally:runner.close()
    report['status']='pass'
    (OUT/'mod-power-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
