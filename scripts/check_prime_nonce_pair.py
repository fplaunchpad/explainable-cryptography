#!/usr/bin/env python3
"""Actual two-call nonce controller against independent joint coin fixtures."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT, nat_encode
from check_prime_nonce_sampling import bounds as sample_bounds

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine PrimeNoncePairMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2+1))
  | .hash w => (w,(state.1,state.2+1))
private def mutated (m : Nat) (l : Fin size) :=
  if m == 1 && l == 0 then Command.compute Turing.TM2.Stmt.halt
  else if m == 2 && l == 0 then
    match code l with
    | .compute s => .compute (.push 10 (fun _ => false) s)
    | other => other
  else if m == 3 && l.val >= (secondLabel 0).val then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | other => other
  else if m == 4 && l == 0 then Command.compute
    (.load (fun _ => 0) (.goto (fun _ => secondLabel 0)))
  else code l
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
    let mut cfg := start (word p[1]!) (word p[2]!)
    let mut tape := word p[3]!
    let mut used := 0
    let mut charge := 0
    let mut queries := 0
    for _ in [:40000] do
      if cfg.l.isNone then break
      let (out,state) := (simulateQ handler (step (mutated mutation) cfg)).run (tape,queries)
      cfg := out.1
      charge := charge+out.2
      tape := state.1
      queries := state.2
      used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,toString queries,
      String.intercalate "/" ((List.ofFn cfg.stk).map bits),bits tape])
    output.flush
'''

def bounds(q,slack):
    record_len=slack+2*q.bit_length()+2
    m=(q-1).bit_length();nonce=2*m+1
    entry_clock=2*record_len+3;entry_cost=9*(record_len+1)+2
    middle_clock=3*nonce+m+4+entry_clock
    middle_cost=13*(nonce+1)+4*(m+1)+entry_cost
    sampler_clock,sampler_cost=sample_bounds(q,slack)
    return entry_clock+2*sampler_clock+1+middle_clock,entry_cost+2*sampler_cost+3+middle_cost

def fixtures():
    out=[]
    for q in (2,3,5,7,11,17,31,257):
        for slack in (0,1):
            w=(q-1).bit_length()+slack
            for a,b in (('0','0'),('0','1'),('1','0'),('1','1')):
                out.append((q,slack,'10110',a*w+b*w+'101'))
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(32):
            q=rng.choice((2,3,5,7,11,17,31,127,257));slack=rng.randrange(4)
            word=lambda n: ''.join(rng.choice('01') for _ in range(n))
            out.append((q,slack,word(rng.randrange(17)),
                        word(2*((q-1).bit_length()+slack))+'101'))
    return out

def main():
    cases=fixtures();r=Runner(DRIVER,'PrimeNoncePairNative')
    def run(mut,c):
        q,s,context,t=c
        return r.run(mut,'1'*s+'0'+nat_encode(q),(context or '-')+' '+t)
    def good(c,a):
        q,s,context,t=c;m=q-1;w=m.bit_length()+s
        value=lambda bits: sum(int(b)<<i for i,b in enumerate(bits))%m+1
        n0=value(t[:w]);n1=value(t[w:2*w]);record='1'*s+'0'+nat_encode(q)
        ticks,cost=bounds(q,s)
        return (a['halted'] and a['memory']==2 and a['queries']==2*w and
            a['remaining_coins']==t[2*w:] and a['steps']<=ticks and a['charge']<=cost and
            a['words']==['',bin(m)[2:][::-1],'','','',nat_encode(n1),'','',record,nat_encode(n0),context])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        witness=(5,0,'','000111101')
        for mut,name in ((1,'omit_second_call'),(2,'corrupt_context'),(3,'fixed_second_coins'),(4,'omit_reentry_transport')):
            actual=run(mut,witness)
            assert not good(witness,actual),(name,actual)
            report['mutants'][name]=dict(q=5,slack=0,context='',tape=witness[3],actual=actual)
        for i,c in enumerate(cases):
            a=run(0,c)
            assert good(c,a),(i,c,a)
            if (i+1)%32==0:print(f'Checked {i+1}/{len(cases)} nonce-pair fixtures',flush=True)
        report['status']='pass'
    finally:
        r.close()
        (OUT/'prime-nonce-pair-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
