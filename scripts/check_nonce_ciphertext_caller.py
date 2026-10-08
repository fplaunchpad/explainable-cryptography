#!/usr/bin/env python3
"""Native pair-to-encryption campaign against independent coins and ElGamal.

Build PrimeNonceCiphertextCaller, then run this script. Requires the existing
check_cache_request_input Runner, check_prime_nonce_pair bounds and the test-only
identity adapter. The original native campaign was deliberately stopped at
48/60 canonical cases after kernel 60/60 and the general cost proof passed;
do not cite it as a completed native campaign. Prefer the kernel generator.
New reports go under tmp/concrete-helios/reproduction. Promotion is not a rerun."""
import json
import random
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from check_cache_request_input import Runner, nat_encode
from nonce_ciphertext_gate_support import NATIVE_SNAPSHOT
OUT=ROOT / "tmp/concrete-helios/reproduction"
OUT.mkdir(parents=True,exist_ok=True)
from check_prime_nonce_pair import bounds as pair_bounds
SEEDS=(118,606,20260914)
DRIVER=r'''
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine PrimeNonceCiphertextCaller
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2+1))
  | .hash w => (w,(state.1,state.2+1))
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == pairLabel 0 then .compute
    (.load (fun _ => 2) (.goto (fun _ => routeLabel 0)))
  else if m == 2 && (l == routeLabel (PrimeNonceCiphertextMachine.copyLabel 0) ||
      l == routeLabel (PrimeNonceCiphertextMachine.copyLabel 1)) then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 23) 21)
        (Equiv.refl _) (Equiv.refl _) s)
    | other => other
  else if m == 3 && l == 0 then .compute (.load (fun _ => 2) .halt)
  else if m == 4 && l == encryptLabel 4 then .compute
    (.load (fun _ => 0) (.goto (fun _ => encryptLabel 8)))
  else if m == 5 && l.val >= (pairLabel (PrimeNoncePairMachine.secondLabel 0)).val &&
      l.val < 165 then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | other => other
  else if m == 6 && l == 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | other => other
  else if m == 7 && l == 0 then
    match code l with
    | .compute s => .compute (.push 20 (fun _ => false) s)
    | other => other
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
    let stepCode := routingProgramTable (mutated mutation)
    let mut cfg := start (word p[2]!) (word p[3]!) (word p[4]!) (word p[1]!) (word p[6]!) (p[5]! == "1")
    let mut tape := word p[7]!
    let mut used := 0
    let mut charge := 0
    let mut queries := 0
    for _ in [:100000] do
      if cfg.l.isNone then break
      let (out,state) := (simulateQ handler (step stepCode cfg)).run (tape,queries)
      cfg := routingSnapshot out.1
      charge := charge+out.2
      tape := state.1
      queries := state.2
      used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,toString queries,
      String.intercalate "/" ((List.ofFn cfg.stk).map bits),bits tape])
    output.flush
'''

def bits(n): return ''.join(str((n>>i)&1) for i in range(n.bit_length()))
GROUPS=((2,5,4,4),(3,7,2,4),(5,11,3,9),(11,23,2,4))
def fixtures():
    out=[]
    for q,p,g,pk in GROUPS:
        for slack in (0,1):
            width=(q-1).bit_length()+slack
            for vote in (False,True):
                for a,b in (('0','1'),('1','0')):
                    out.append((p,q,g,pk,slack,vote,'10110',a*width+b*width+'101'))
    for vote in (False,True):
        for a in ('0','1'): out.append((23,11,2,4,0,vote,'011',a*8+'101'))
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(8):
            q,p,g,pk=rng.choice(GROUPS);slack=rng.randrange(3)
            width=(q-1).bit_length()+slack
            word=lambda n: ''.join(rng.choice('01') for _ in range(n))
            out.append((p,q,g,pk,slack,bool(rng.randrange(2)),word(rng.randrange(17)),word(2*width)+'101'))
    return out

def expected(c):
    p,q,g,pk,slack,vote,context,tape=c;w=(q-1).bit_length()+slack
    val=lambda raw: sum(int(b)<<i for i,b in enumerate(raw))%(q-1)+1
    n0=val(tape[:w]);n1=val(tape[w:2*w]);words=['']*23
    words[0]=bits(pow(pk,n0,p)*(g if vote else 1)%p)
    words[6]=bits(p);words[13]=bits(n0);words[14]=context
    words[15]=bits(pk);words[16]=bits(g);words[17]=bits(pow(g,n0,p))
    words[18]=str(int(vote));words[19]='1'*slack+'0'+nat_encode(q)
    words[20]=nat_encode(n0);words[21]=nat_encode(n1);words[22]=bits(q-1)
    return words,tape[2*w:],2*w

def good(c,a):
    p,q,g,pk,slack,vote,context,tape=c
    pair_clock,pair_cost=pair_bounds(q,slack);W=p.bit_length();L=(q-1).bit_length()
    mul=9*W+11+W*(34*W+38);power=3*L+5+L*(2*mul+12*W+16)
    encrypt=2*power+mul+15*W+20;route=7*L+9
    words,coins,queries=expected(c)
    return (a['halted'] and a['memory']==2 and a['words']==words and
            a['queries']==queries and a['remaining_coins']==coins and
            a['steps']<=pair_clock+route+1+encrypt and
            a['charge']<=pair_cost+6*route+3+32*encrypt)

def source():
    return 'import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller\n'+NATIVE_SNAPSHOT+DRIVER

def main():
    cases=fixtures();report=dict(status='failed',cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    r=Runner(source(),'NonceCiphertextCallerNativeReproduction')
    def execute(m,c):
        p,q,g,pk,slack,vote,context,tape=c
        return r.run(m,'1'*slack+'0'+nat_encode(q),
                     ' '.join((bits(g) or '-',bits(pk) or '-',bits(p),str(int(vote)),context or '-',tape)))
    try:
        witness=(23,11,2,4,0,True,'101','00001111101')
        for m,name in ((1,'omit_second_draw'),(2,'wrong_nonce'),(3,'omit_encryption'),
                       (4,'omit_vote_multiplier'),(5,'fixed_second_coins'),(6,'corrupt_context'),(7,'corrupt_first_prefix')):
            a=execute(m,witness); assert not good(witness,a),(name,a)
            report['mutants'][name]=dict(input=witness,actual=a)
            print('detected '+name,flush=True)
        for i,c in enumerate(cases):
            a=execute(0,c); assert good(c,a),(i,c,a,expected(c))
            print(f'checked {i+1}/{len(cases)}',flush=True)
        report['status']='pass'
    finally:
        r.close();(OUT/'nonce-ciphertext-caller-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
