#!/usr/bin/env python3
"""Actual two-power ciphertext controller versus independent ElGamal coordinates."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT
from check_mod_add import bits

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
open ExplainableCrypto.Helios.Computational PrimeEncryptMachine
private def mutated (m : Nat) (l : Fin 490) :=
  if m == 1 && l == powerLabel 0 (BinaryModPower.copyLabel 0 0) then
    .load (fun _ => 2) (.goto (fun _ => 0))
  else if m == 2 && l == powerLabel 1 (BinaryModPower.copyLabel 0 0) then
    .load (fun _ => 2) (.goto (fun _ => 3))
  else if m == 3 && (l == copyLabel 2 0 || l == copyLabel 2 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (15 : Fin 19) 16) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 4 && l == 4 then enter 8
  else if m == 5 && l == 3 then .push 17 (fun _ => false) (control 3)
  else if m == 6 && l == 3 then .push 13 (fun _ => false) (control 3)
  else if m == 7 && l == 3 then .push 14 (fun _ => false) (control 3)
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
      (word p[6]!) (p[5]! == "1")
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
    cases=[(p,g,pk,bits(r),v,'10110') for p in (3,5,7) for g in (1,p-1)
           for pk in (1,p-1) for r in range(4) for v in (False,True)]
    cases.extend((23,2,4,bits(r),v,'10110') for r in (1,2,3,10) for v in (False,True))
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(32):
            p=rng.randrange(2,2**rng.randrange(2,18))
            raw=''.join(rng.choice('01') for _ in range(rng.randrange(7)))
            context=''.join(rng.choice('01') for _ in range(rng.randrange(17)))
            cases.append((p,rng.randrange(p),rng.randrange(p),raw,bool(rng.randrange(2)),context))
    cases.extend((2,1,1,raw,v,'011') for raw in ('','0','1','101') for v in (False,True))
    cases.extend((2**31-1,2,4,'11',v,'01101') for v in (False,True))
    return cases

def main():
    cases=fixtures();runner=Runner(DRIVER,'PrimeEncryptNative')
    def execute(mut,c):
        p,g,pk,raw,v,context=c
        extra=' '.join((bits(pk) or '-',raw or '-',bits(p),str(int(v)),context or '-'))
        return runner.run(mut,bits(g),extra)
    def good(c,a):
        p,g,pk,raw,v,context=c;r=sum(int(b)<<i for i,b in enumerate(raw));w=p.bit_length()
        multiply=9*w+11+w*(34*w+38)
        power=3*len(raw)+5+len(raw)*(2*multiply+12*w+16)
        clock=2*power+multiply+15*w+20
        alpha=pow(g,r,p);beta=pow(pk,r,p)*(g if v else 1)%p
        return (a['halted'] and a['memory']==2 and a['queries']==0 and
            a['steps']<=clock and a['charge']<=32*clock and
            a['words']==[bits(beta),'','','','','',bits(p),'','','','','','',raw,context,bits(pk),bits(g),bits(alpha),str(int(v))])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        for mut,name in ((1,'omit_first_power'),(2,'omit_second_power'),(3,'reuse_generator_for_key'),
                         (4,'omit_vote_product'),(5,'corrupt_first_coordinate'),
                         (6,'corrupt_saved_nonce'),(7,'corrupt_saved_context')):
            c=(23,2,4,'11',True,'101')
            a=execute(mut,c)
            assert not good(c,a),(name,a)
            report['mutants'][name]=dict(input=c,actual=a)
        for i,c in enumerate(cases):
            a=execute(0,c)
            assert good(c,a),(i,c,a)
    finally:runner.close()
    report['status']='pass'
    (OUT/'prime-encrypt-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
