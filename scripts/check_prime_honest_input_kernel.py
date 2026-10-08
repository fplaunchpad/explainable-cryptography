#!/usr/bin/env python3
"""Independent bounded kernel refutation gate for the original initializer.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine`,
then `python3 scripts/check_prime_honest_input_kernel.py`. Reproduces the seven
sensitive mutations, retained insensitive pk-suffix control, malformed inputs and
28 canonical fixtures with the original three seeds. No native-decide axioms.
Reports/logs/generated Lean go under tmp/concrete-helios/reproduction, preserving
historical artifacts. A canonical parsing theorem does not validate group
membership, parameter primality or the sampler-record contents."""
import hashlib,json,random,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/"tmp/concrete-helios/reproduction"
OUT.mkdir(parents=True,exist_ok=True)
HEADER=ROOT/"ExplainableCrypto/Helios/Computational/PrimeHonestInputMachine.lean"
SEEDS=(118,606,20260914)
def bits(n):return ''.join(str((n>>i)&1) for i in range(n.bit_length()))
def nat(n):return '1'*n.bit_length()+'0'+bits(n)
def frames(ws):return ''.join(nat(len(w))+w for w in ws)
def fields(ws,count=None):return nat(len(ws) if count is None else count)+frames(ws)
def word(w):return '['+','.join('true' if c=='1' else 'false' for c in w)+']'
def fixture(p=23,q=11,g=2,pk=4,slack=0,vote=True,saved='101',**kw):
 record='1'*slack+'0'+nat(q)
 nested=fields([nat(g)+kw.get('g_suffix',''),nat(pk)+kw.get('pk_suffix','')],kw.get('nested_count'))+kw.get('nested_suffix','')
 raw=fields([nat(p)+kw.get('p_suffix',''),nested,record,kw.get('vote_word',str(int(vote))),saved],kw.get('outer_count'))+kw.get('outer_suffix','')
 return dict(p=p,q=q,g=g,pk=pk,slack=slack,vote=vote,saved=saved,record=record,raw=raw)
def expected(c):
 ws=['']*23
 for k,w in [(6,bits(c['p'])),(14,c['raw']),(15,bits(c['pk'])),(16,bits(c['g'])),(18,str(int(c['vote']))),(19,c['record'])]:ws[k]=w
 return '['+','.join(word(w) for w in ws)+']'
def cap(c):n=len(c['raw']);return 14*n*n+54*n+83
BASE=r'''
namespace ExplainableCrypto.Helios.Computational.PrimeHonestInputControls
open PrimeHonestInputMachine Turing.TM2
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def jump (l : Fin 97) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
private def mutated (m : Nat) (l : Fin 97) :=
  if m == 1 && l == copyLabel 0 then jump 0
  else if m == 2 && l.val >= 91 then
    TM2FiniteCoordinates.translate (Equiv.swap (15 : Fin 23) 16) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 3 && l == 4 then .pop 7 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 1) (jump 5) (.load (fun _ => 1) .halt))
  else if m == 4 && l == 13 then .pop 9 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 2) (jump 14) (.load (fun _ => 1) .halt))
  else if m == 5 && l == 18 then .branch (fun v => v == 2)
    (jump (fieldLabel 4 0)) (.load (fun _ => 1) .halt)
  else if m == 6 && l == 20 then .branch (fun v => v == 2)
    (jump (fieldLabel 6 0)) (.load (fun _ => 1) .halt)
  else if m == 7 && l == 22 then .load (fun _ => 2) .halt
  else program l
private def execute (m : Nat) : Nat → Config → Nat → Nat → Config × Nat × Nat
  | 0,cfg,used,charge => (cfg,used,charge)
  | n+1,cfg,used,charge => match cfg.l with
    | none => (cfg,used,charge)
    | some l => execute m n (TM2ReturnLink.tick (mutated m) cfg) (used+1)
        (charge+BitOracleMachine.localCost (mutated m l))
private def observed (m fuel : Nat) (raw : List Bool) :=
  let out := execute m fuel (start raw) 0 0
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1,out.2.2)
private def success (m fuel : Nat) (raw : List Bool) (ws : List (List Bool)) : Prop :=
  let out := observed m fuel raw
  out.1 = (none,2,ws) ∧ out.2.1 ≤ fuel ∧ out.2.2 ≤ 32*fuel
private def rejected (fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed 0 fuel raw
  out.1.1 = none ∧ out.1.2.1 = 1 ∧ out.2.1 ≤ fuel
private def mutationChanges (m fuel : Nat) (raw : List Bool) (ws : List (List Bool)) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1 ≠ (none,2,ws) ∧ out.2.1 ≤ fuel
private def mutationRejects (m fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1.2.1 = 1 ∧ out.2.1 ≤ fuel
private def mutationAccepts (m fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1.2.1 = 2 ∧ out.2.1 ≤ fuel
'''
def theorem(name,claim):return f'\ntheorem {name} : {claim} := by\n  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]\n  decide +kernel\n#print axioms {name}\n'
def gate_source(body):
 return 'import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine\n'+BASE+body+'\nend ExplainableCrypto.Helios.Computational.PrimeHonestInputControls\n'
def run_gate(name,body):
 source=gate_source(body)
 path=OUT/(name+'.lean');path.write_text(source)
 log=OUT/(name+'.log')
 with log.open('w') as f:r=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
 t=log.read_text();ok=r.returncode==0 and 'error:' not in t and 'sorry' not in t
 return ok,log,source

def main():
 report=dict(status='running',seeds=SEEDS,discarded=0,gaveUp=0,controller_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest())
 body='';canonical=fixture()
 mutations=[('omitted_copy',1,canonical,False),('swapped_coordinates',2,canonical,False),('wrong_outer_arity',3,fixture(outer_count=4),True),('wrong_nested_arity',4,fixture(nested_count=3),True),('ignored_pk_suffix',5,fixture(pk_suffix='0'),True),('ignored_nested_suffix',5,fixture(nested_suffix='1'),True),('nonsingleton_vote',6,fixture(vote_word='10'),True),('uncleared_saved',7,canonical,False)]
 for name,m,c,accepts in mutations:
  if accepts:body+=theorem(name+'_baseline_rejects',f'rejected {cap(c)} {word(c["raw"])}')
  claim=f'mutationAccepts {m} {cap(c)} {word(c["raw"])}' if accepts else f'mutationChanges {m} {cap(c)} {word(c["raw"])} {expected(c)}'
  if name=='ignored_pk_suffix':
   claim=f'mutationRejects {m} {cap(c)} {word(c["raw"])}'
   name='bypassed_pk_guard_still_rejects'
  body+=theorem(name+'_counterexample',claim)
 ok,log,_=run_gate('PrimeHonestInputMutationGate',body)
 report['mutation_witnesses']=7;report['ineffective_mutation_fixtures']=1;report['mutations_pass']=ok
 (OUT/'prime-honest-input-kernel-gate.json').write_text(json.dumps(report,indent=2)+'\n')
 if not ok:print(log.read_text());raise SystemExit(1)
 print('mutation gate PASS',flush=True)
 groups=[(5,2,4),(7,3,2),(11,5,3),(23,11,2)]
 cases=[]
 for p,q,g in groups:
  for v in (False,True):cases.append(fixture(p,q,g,pow(g,2,p),0,v,'' if not v else '101'))
 for n in (0,1,2,3,7,8,15,16):cases.append(fixture(23,11,2,4,n%3,bool(n%2),'1'*n))
 for seed in SEEDS:
  rng=random.Random(seed)
  for _ in range(4):
   p,q,gen=rng.choice(groups);g=pow(gen,rng.randrange(q),p);pk=pow(gen,rng.randrange(q),p)
   cases.append(fixture(p,q,g,pk,rng.randrange(4),bool(rng.randrange(2)),''.join(rng.choice('01') for _ in range(rng.randrange(17)))))
 positive=''
 for i,c in enumerate(cases):positive+=theorem('canonical_'+str(i),f'success 0 {cap(c)} {word(c["raw"])} {expected(c)}')
 # Bridge the supplied typed source encoder to an independently computed literal word.
 positive+='''\ndef typedGenerator : PrimeGroup 23 11 := Additive.ofMul (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
 def typedKey : PrimeGroup 23 11 := Additive.ofMul (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))\n'''
 positive+=theorem('typed_source_encoding',f'input typedGenerator typedKey 0 true [true,false,true] = {word(canonical["raw"])}')
 # Generic independent-shape bridge, with no validation claim on p/q or membership.
 positive+='''\ntheorem typed_encoding_shape {p q : Nat} [NeZero p] [NeZero q] (g pk : PrimeGroup p q)
    (slack : Nat) (vote : Bool) (saved : List Bool) :
    input g pk slack vote saved = bitFieldsEncode [uniformNatEncode p,
      bitFieldsEncode [uniformNatEncode (primeGroupCoordinate g).val,uniformNatEncode (primeGroupCoordinate pk).val],
      SamplerOperands.input slack q [],[vote],saved] := rfl
#print axioms typed_encoding_shape\n'''
 malformed=[fixture(p_suffix='0'),fixture(g_suffix='1'),fixture(pk_suffix='1'),fixture(nested_suffix='0'),fixture(outer_suffix='1'),fixture(vote_word=''),fixture(vote_word='00'),fixture(vote_word='11')]
 for i,c in enumerate(malformed):positive+=theorem('malformed_'+str(i),f'rejected {cap(c)} {word(c["raw"])}')
 ok,log,source=run_gate('PrimeHonestInputPositiveGate',positive)
 report.update(status='pass' if ok else 'failed',canonical_cases=len(cases),malformed_cases=len(malformed)+5,source_encoder_checks=2,max_raw_length=max(map(lambda c:len(c['raw']),cases)),positive_log=str(log),classification=None if ok else 'kernel fixture or evaluation failure; inspect log')
 (OUT/'prime-honest-input-kernel-gate.json').write_text(json.dumps(report,indent=2)+'\n')
 # Keep the bounded durable-control candidate separately from the campaign.
 fragment=BASE+body+theorem('literal_true_control',f'success 0 {cap(canonical)} {word(canonical["raw"])} {expected(canonical)}')
 c=fixture(vote=False,saved='');fragment+=theorem('literal_false_empty_saved_control',f'success 0 {cap(c)} {word(c["raw"])} {expected(c)}')
 fragment+=positive[positive.index('\ndef typedGenerator'):positive.index('\ntheorem malformed_0')]
 (OUT/'PrimeHonestInputControlsFragment.lean').write_text('import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine\n'+fragment+'\nend ExplainableCrypto.Helios.Computational.PrimeHonestInputControls\n')
 print(json.dumps(report,indent=2),flush=True)
 if not ok:print(log.read_text());raise SystemExit(1)
if __name__=='__main__':main()
