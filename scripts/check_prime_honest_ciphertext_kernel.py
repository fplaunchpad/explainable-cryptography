#!/usr/bin/env python3
"""Bounded original-code kernel gate for raw input through first ciphertext.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine`,
then `python3 scripts/check_prime_honest_ciphertext_kernel.py`. Depends on the
independent input encoder in check_prime_honest_input_kernel.py and existing
check_prime_nonce_pair bounds. Retains five mutations and 12 canonical cases
with three seeds, complete private state, residual coins and derived clock cap.
Reports/logs/generated Lean go under tmp/concrete-helios/reproduction.
This tests the first ciphertext only; it is not a full ballot-secrecy proof."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
from check_prime_honest_input_kernel import fixture,bits,nat,word
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/"tmp/concrete-helios/reproduction"
OUT.mkdir(parents=True,exist_ok=True)
HEADER=ROOT/"ExplainableCrypto/Helios/Computational/PrimeHonestCiphertextMachine.lean"
sys.path.insert(0,str(ROOT/'scripts'))
from check_prime_nonce_pair import bounds as pair_bounds
SEEDS=(118,606,20260914)
BASE=r'''
namespace ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextControls
open PrimeHonestCiphertextMachine OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == inputLabel (PrimeHonestInputMachine.copyLabel 0) then
    .compute (.load (fun _ => 0) (.goto (fun _ => 0)))
  else if m == 2 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => callerLabel callerEntry)))
  else if m == 3 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => callerLabel (PrimeNonceCiphertextCaller.routeLabel 0))))
  else if m == 4 && l == 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | c => c
  else if m == 5 && l == 0 then
    match code l with
    | .compute s => .compute (.push 16 (fun _ => false) s)
    | c => c
  else code l
private def execute (m : Nat) : Nat → Config → (List Bool × Nat × Nat) → Nat → Nat →
    Config × (List Bool × Nat × Nat) × Nat × Nat
  | 0,cfg,state,used,charge => (cfg,state,used,charge)
  | n+1,cfg,state,used,charge => match cfg.l with
    | none => (cfg,state,used,charge)
    | some _ =>
      let out := (simulateQ handler (step (mutated m) cfg)).run state
      execute m n out.1.1 out.2 (used+1) (charge+out.1.2)
private def observed (m fuel : Nat) (raw tape : List Bool) :=
  let out := execute m fuel (start raw) (tape,0,0) 0 0
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1.1,out.2.1.2.1,out.2.1.2.2,out.2.2.1,out.2.2.2)
private def agrees (m fuel bound : Nat) (raw tape : List Bool) (mem : Nat)
    (ws : List (List Bool)) (remaining : List Bool) (coins : Nat) : Prop :=
  let out := observed m fuel raw tape
  out.1 = (none,mem,ws) ∧ out.2.1 = remaining ∧ out.2.2.1 = coins ∧
    out.2.2.2.1 = 0 ∧ out.2.2.2.2.1 ≤ fuel ∧ out.2.2.2.2.2 ≤ bound
'''
def theorem(name,claim):return f'\ntheorem {name} : {claim} := by\n  dsimp only [agrees]\n  decide +kernel\n#print axioms {name}\n'
def fixture_with_tape(**kw):
 tape=kw.pop('tape',None);c=fixture(**kw);w=(c['q']-1).bit_length()+c['slack'];c['tape']=tape or '0'*w+'1'*w+'101';return c

def bounds(c):
 n=len(c['raw']);init=14*n*n+54*n+83;p,q,slack=c['p'],c['q'],c['slack'];w=p.bit_length();l=(q-1).bit_length()
 pair,pcost=pair_bounds(q,slack);mul=9*w+11+w*(34*w+38);power=3*l+5+l*(2*mul+12*w+16);enc=2*power+mul+15*w+20;route=7*l+9
 return init+1+pair+route+1+enc,32*init+3+pcost+6*route+3+32*enc

def expected(c):
 w=(c['q']-1).bit_length()+c['slack'];t=c['tape'];val=lambda z:sum(int(b)<<i for i,b in enumerate(z))%(c['q']-1)+1
 a,b=val(t[:w]),val(t[w:2*w]);p,g,pk=c['p'],c['g'],c['pk'];ws=['']*23
 for k,x in [(0,bits(pow(pk,a,p)*(g if c['vote'] else 1)%p)),(6,bits(p)),(13,bits(a)),(14,c['raw']),(15,bits(pk)),(16,bits(g)),(17,bits(pow(g,a,p))),(18,str(int(c['vote']))),(19,c['record']),(20,nat(a)),(21,nat(b)),(22,bits(c['q']-1))]:ws[k]=x
 return ws,t[2*w:],2*w

def assertion(name,m,c,ws,remaining,coins,mem=2):
 fuel,bound=bounds(c)
 # Changed instructions can cost one extra primitive; use a loose control-only
 # bound for mutants while canonical bounds stay exactly independently derived.
 if m:bound+=fuel
 return theorem(name,f'agrees {m} {fuel} {bound} {word(c["raw"])} {word(c["tape"])} {mem} ['+','.join(word(x) for x in ws)+f'] {word(remaining)} {coins}')

def gate_source(body):
 return 'import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine\n'+BASE+body+'\nend ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextControls\n'
def run_gate(name,body):
 src=gate_source(body);path=OUT/(name+'.lean');path.write_text(src);log=OUT/(name+'.log')
 with log.open('w') as f:r=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
 text=log.read_text();ok=r.returncode==0 and 'error:' not in text and 'sorry' not in text
 return ok,log

def main():
 c=fixture_with_tape();good,rest,count=expected(c);body=''
 # Skip initializer: original raw7 remains, guard rejects before any queries.
 ws=['']*23;ws[7]=c['raw'];body+=assertion('skipped_initializer_counterexample',1,c,ws,c['tape'],0,1)
 # Late malformed outer suffix yields initialized operands but no caller entry.
 bad=fixture_with_tape(saved='',outer_suffix='1');ws,rest,count=expected(bad)
 ws[0]=ws[13]=ws[17]=ws[20]=ws[21]=ws[22]='';ws[7]='1'
 body+=assertion('failed_initializer_guard_control',0,bad,ws,bad['tape'],0,1)
 # Bypassing the guard performs both draws before route rejects the stale suffix.
 ws,rest,count=expected(bad);ws[0]=ws[17]='';ws[7]='1'
 body+=assertion('bypassed_failure_guard_counterexample',2,bad,ws,rest,count,1)
 # Wrong caller entry routes an empty prefix without executing either sampler.
 ws=good.copy();ws[0]=ws[13]=ws[17]=ws[20]=ws[21]=ws[22]=''
 body+=assertion('wrong_caller_entry_counterexample',3,c,ws,c['tape'],0,1)
 ws=good.copy();ws[14]='0'+c['raw'];body+=assertion('corrupted_context_counterexample',4,c,ws,'101',8)
 # Prefix zero doubles canonical generator2 to4 before first nonce1 encryption.
 ws=good.copy();ws[16]=bits(4);ws[17]=bits(4);ws[0]=bits(16)
 body+=assertion('overwritten_generator_counterexample',5,c,ws,'101',8)
 report=dict(status='running',seeds=SEEDS,discarded=0,gaveUp=0,mutation_changes=5,mutation_controls=6,controller_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest())
 ok,log=run_gate('PrimeHonestCiphertextMutationGate',body)
 report['mutations_pass']=ok;(OUT/'prime-honest-ciphertext-kernel-gate.json').write_text(json.dumps(report,indent=2)+'\n')
 if not ok:print(log.read_text());raise SystemExit(1)
 print('mutation gate PASS',flush=True)
 cases=[]
 for vote in (False,True):
  for a,b in (('0','1'),('1','0')):cases.append(fixture_with_tape(vote=vote,tape=a*4+b*4+'101'))
 for vote in (False,True):cases.append(fixture_with_tape(p=5,q=2,g=4,pk=1,vote=vote,saved='',tape='01101'))
 groups=((5,2,4),(7,3,2),(11,5,3),(23,11,2))
 for seed in SEEDS:
  rng=random.Random(seed)
  for _ in range(2):
   p,q,g=rng.choice(groups);slack=rng.randrange(2);w=(q-1).bit_length()+slack
   tape=''.join(rng.choice('01') for _ in range(2*w))+'101'
   cases.append(fixture_with_tape(p=p,q=q,g=g,pk=pow(g,2,p),slack=slack,vote=bool(rng.randrange(2)),saved=''.join(rng.choice('01') for _ in range(rng.randrange(7))),tape=tape))
 positive=''
 for i,c in enumerate(cases):ws,remaining,coins=expected(c);positive+=assertion('canonical_'+str(i),0,c,ws,remaining,coins)
 ok,log=run_gate('PrimeHonestCiphertextPositiveGate',positive)
 report.update(status='pass' if ok else 'failed',canonical_cases=len(cases),max_raw_length=max(len(c['raw']) for c in cases),positive_log=str(log))
 (OUT/'prime-honest-ciphertext-kernel-gate.json').write_text(json.dumps(report,indent=2)+'\n')
 fragment=BASE+body+positive[:positive.index('\ntheorem canonical_4')]
 (OUT/'PrimeHonestCiphertextControlsFragment.lean').write_text('import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine\n'+fragment+'\nend ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextControls\n')
 print(json.dumps(report,indent=2),flush=True)
 if not ok:print(log.read_text());raise SystemExit(1)
if __name__=='__main__':main()
