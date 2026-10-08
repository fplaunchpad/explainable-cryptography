#!/usr/bin/env python3
"""Actual public-input nonce sampler versus independent integer/coin fixtures."""
import json
import random
import sys
sys.dont_write_bytecode = True
from check_cache_request_input import Runner, OUT, nat_encode

SEEDS=(118,606,20260914)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.PrimeNonceSampling
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine PrimeNonceMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2+1))
  | .hash w => (w,(state.1,state.2+1))
private def code (m : Nat) (l : Fin 71) :=
  if m == 1 && l == operandLabel 8 then Command.compute
    (.load (fun _ => 2) (.goto (fun _ => operandLabel 12)))
  else if m == 2 && l == tailLabel 28 then Command.compute Turing.TM2.Stmt.halt
  else if m == 3 && l == tailLabel (responseLabel 25) then Command.compute
    (.push 8 (fun _ => false) Turing.TM2.Stmt.halt)
  else if m == 4 && l == operandLabel 12 then
    match sampleCode l with
    | .compute s => .compute (.push 2 (fun _ => true) s)
    | other => other
  else sampleCode l
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
    let mut cfg := sampleStart (word p[1]!) ![word p[2]!,word p[3]!,word p[4]!]
    let mut tape := word p[5]!
    let mut used := 0
    let mut charge := 0
    let mut queries := 0
    for _ in [:20000] do
      if cfg.l.isNone then break
      let (out,state) := (simulateQ handler (step (code mutation) cfg)).run (tape,queries)
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
    m=q-1;w=m.bit_length()+slack;z=(m-1).bit_length()
    prep=slack+5*q.bit_length()+2*m.bit_length()+9
    sample_clock=4*w+2+w*(8*m.bit_length()+13)+3+3*z+3
    sample_cost=15*w+9+32*(w*(8*m.bit_length()+13)+3)+32*(3*z+3)
    successor=5*z+6*m.bit_length()+16
    return prep+1+sample_clock+1+successor,32*prep+5+sample_cost+3+32*successor

def fixtures():
    out=[]
    for q in (2,3,5,7,11,17,31,257):
        for slack in (0,1):
            w=(q-1).bit_length()+slack
            for b in ('0','1'):
                out.append((q,slack,['1','01','0'],b*w+'101'))
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(32):
            q=rng.choice((2,3,5,7,11,17,31,127,257));slack=rng.randrange(4)
            word=lambda n: ''.join(rng.choice('01') for _ in range(n))
            out.append((q,slack,[word(rng.randrange(13)) for _ in range(3)],
                        word((q-1).bit_length()+slack)+'101'))
    return out

def main():
    cases=fixtures();r=Runner(DRIVER,'PrimeNonceSamplingNative')
    def run(mut,c):
        q,s,f,t=c
        return r.run(mut,'1'*s+'0'+nat_encode(q),' '.join([*(w or '-' for w in f),t or '-']))
    def good(c,a):
        q,s,f,t=c;m=q-1;w=m.bit_length()+s
        n=sum(int(b)<<i for i,b in enumerate(t[:w]))%m+1
        ticks,cost=bounds(q,s)
        return (a['halted'] and a['memory']==2 and a['queries']==w and
            a['remaining_coins']==t[w:] and a['steps']<=ticks and a['charge']<=cost and
            a['words']==['',bin(m)[2:][::-1],'','','',nat_encode(n),'','',*f])
    report=dict(cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    try:
        smallest=(2,0,['','',''],'0101')
        for mut,name in ((1,'omit_decrement'),(2,'omit_successor'),(3,'corrupt_saved'),(4,'stale_width')):
            actual=run(mut,smallest)
            assert not good(smallest,actual),(name,actual)
            report['mutants'][name]=dict(q=2,slack=0,frame=['','',''],tape='0101',actual=actual)
        for i,c in enumerate(cases):
            a=run(0,c)
            assert good(c,a),(i,c,a,bounds(c[0],c[1]))
            if (i+1)%32==0:print(f'Checked {i+1}/{len(cases)} complete nonce fixtures',flush=True)
        report['status']='pass'
    finally:
        r.close()
        (OUT/'prime-nonce-sampling-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
