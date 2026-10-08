#!/usr/bin/env python3
"""Native routing campaign against independent scalar-prefix fixtures.

Build PrimeNonceCiphertextMachine, then run `python3 scripts/check_nonce_ciphertext.py`.
Uses the existing check_cache_request_input Runner and the test-only identity
adapter in nonce_ciphertext_gate_support. Kernel reproduction is preferred:
check_nonce_ciphertext_kernel.py. This campaign previously passed 810 canonical
cases and six mutations; promotion is not a new run. Reports go under
`tmp/concrete-helios/reproduction`; historical reports remain unchanged."""
import json
import random
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_cache_request_input import Runner, nat_encode
from nonce_ciphertext_gate_support import NATIVE_SNAPSHOT
OUT=ROOT / "tmp/concrete-helios/reproduction"
OUT.mkdir(parents=True,exist_ok=True)

SEEDS = (118, 606, 20260914)
HEADER = ROOT / 'ExplainableCrypto/Helios/Computational/PrimeNonceCiphertextMachine.lean'
DRIVER = r'''
open ExplainableCrypto.Helios.Computational PrimeNonceCiphertextMachine
private def mutated (m : Nat) (l : Fin 7) :=
  if m == 1 && (l == copyLabel 0 || l == copyLabel 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 23) 21)
      (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 2 && l == 0 then
    .load (fun _ => 0) (.goto (fun _ => parseLabel 0))
  else if m == 3 && l == parseLabel 0 then .load (fun _ => 2) .halt
  else if m == 4 && l == 1 then
    .branch (fun v => v == 2) (.load (fun _ => 2) .halt) (.load (fun _ => 1) .halt)
  else if m == 5 && l == 1 then .push 20 (fun _ => false) (program l)
  else if m == 6 && l == 1 then .push 14 (fun _ => false) (program l)
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
    let stepProgram := routingProgramTable (mutated mutation)
    let mut cfg := start (word p[3]!) (word p[1]!) (word p[2]!) (word p[4]!)
      (word p[5]!) (word p[6]!) (word p[7]!) (word p[8]!) (p[9]! == "1")
    let mut used := 0
    let mut charge := 0
    for _ in [:10000] do
      if cfg.l.isNone then break
      charge := charge + BitOracleMachine.localCost (stepProgram (cfg.l.getD 0))
      cfg := routingSnapshot (TM2ReturnLink.tick stepProgram cfg)
      used := used+1
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,"0",
      String.intercalate "/" ((List.ofFn cfg.stk).map bits)])
    output.flush
'''

def bits(n):
    return ''.join(str((n >> i) & 1) for i in range(n.bit_length()))

def fixture(n, second, q=5, context='10110', vote=True, record='101001'):
    return dict(n=n, first=nat_encode(n), second=nat_encode(second),
                record=record, samplerMod=bits(q-1), context=context,
                modulus=bits(23), g=bits(2), pk=bits(4), vote=vote)

def fixtures():
    result=[fixture(a,b,q,vote=v) for q in (2,3,5,7,11,13)
            for a in range(1,q) for b in range(1,q) for v in (False,True)]
    result += [fixture(n,0,context='',record='') for n in range(16)]
    for seed in SEEDS:
        rng=random.Random(seed)
        for _ in range(64):
            n=rng.getrandbits(rng.choice((1,2,7,8,15,16,31,32,63,64,127,128,255,256)))
            c=fixture(n,rng.getrandbits(64),context=''.join(rng.choice('01') for _ in range(rng.randrange(128))))
            for k in ('record','samplerMod','modulus','g','pk'):
                c[k]=''.join(rng.choice('01') for _ in range(rng.randrange(65)))
            result.append(c)
    return result

def expected(c):
    w=['']*23
    for k,name in ((6,'modulus'),(14,'context'),(15,'pk'),(16,'g'),
                   (19,'record'),(20,'first'),(21,'second'),(22,'samplerMod')):
        w[k]=c[name]
    w[13]=bits(c['n']); w[18]=str(int(c['vote']))
    return w

def good(c,a):
    clock=7*c['n'].bit_length()+9
    return (a['halted'] and a['memory']==2 and a['queries']==0
            and a['words']==expected(c) and a['steps']<=clock and a['charge']<=32*clock)

def main():
    cases=fixtures()
    report=dict(status='failed',cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,mutants={})
    runner=Runner('import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine\n'+NATIVE_SNAPSHOT+DRIVER,'NonceCiphertextNativeReproduction')
    def execute(m,c):
        extra=' '.join(c[k] or '-' for k in ('second','record','samplerMod','context','modulus','g','pk'))
        return runner.run(m,c['first'],extra+' '+str(int(c['vote'])))
    try:
        for m,name in ((1,'wrong_nonce'),(2,'omitted_copy'),(3,'omitted_parser'),
                       (4,'unchecked_suffix'),(5,'corrupted_saved_prefix'),(6,'corrupted_context')):
            c=fixture(1,3)
            if m==4: c['first']+='0'
            a=execute(m,c)
            if m==4:
                baseline=execute(0,c)
                assert baseline['halted'] and baseline['memory']==1,baseline
                assert a['halted'] and a['memory']==2,a
            else: assert not good(c,a),(name,c,a)
            report['mutants'][name]=dict(input=c,actual=a)
            print('detected '+name,flush=True)
        for i,c in enumerate(cases):
            a=execute(0,c)
            assert good(c,a),(i,c,a,expected(c))
            if i%64==0: print(f'checked {i+1}/{len(cases)}',flush=True)
        malformed=['','1','11','100','11000','1010','1011','0'+'1']
        for raw in malformed:
            c=fixture(1,3); c['first']=raw
            a=execute(0,c)
            assert a['halted'] and a['memory']==1,(raw,a)
        report['malformed_cases']=len(malformed)
        report['status']='pass'
    finally:
        runner.close()
        (OUT/'nonce-ciphertext-native.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
