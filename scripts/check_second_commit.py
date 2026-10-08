#!/usr/bin/env python3
"""Gate the fixed p1 first-commitment relocation against independent arithmetic.

Build PrimeSecondCommitMachine, then run this script. Expected prior59 words
come from the existing independent source fixture grammar and integer equations;
no Lean execution provides expected outputs. Nine directed/seeded cases, eight
localized actual instruction mutants and one guard control compare all65 words,
zero queries, residual101, and the unchanged first-commitment clock/cost.

The 300-second host timeout is an evaluation limit, not a modeled cost bound.
--generate-only writes the imported driver without executing Lean.
"""
from pathlib import Path
import sys,json,copy,hashlib,random
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_sim_commit as first
import check_second_transcript as second
n=first.n
BASE=first.BASE.replace('PrimeSimCommitControls','PrimeSecondCommitControls').replace('open PrimeSimCommitMachine','open PrimeSecondCommitMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 65 size 3 :=
  if m == 1 && 29 <= l.val && l.val < 33 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (50 : Fin 65) 17)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 2 && 522 <= l.val then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (55 : Fin 65) 11)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 3 && 13 <= l.val && l.val < 17 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (56 : Fin 65) 12)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 4 && 45 <= l.val && l.val < 49 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (60 : Fin 65) 61)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 5 && l == 10 then .compute (.goto (fun _ => 11))
  else if (m == 6 || m == 7) && l == 12 then .compute
    (.push (if m == 6 then 48 else 49) (fun _ => false) (program l))
  else if m == 8 && l == 0 then .compute (.load (fun _ => 2) (program l))
  else code l
'''
def source():
 return ('import ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+
         n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSecondCommitControls'))
def make(name,p=7,q=3,g=2,pk=4,r1=1,r2=2,cs=(0,1,2,0),**kwargs):
 slack=kwargs.get('slack',0);width=q.bit_length()+slack
 assert all(0<=v<q for v in cs)
 words=[second.bits(v).ljust(width,'0') for v in cs]
 oldcase=second.make(name,p=p,q=q,g=g,pk=pk,r1=r1,r2=r2,words=words,**kwargs)
 old59=second.expected(oldcase)[0]
 assert len(old59)==59
 return dict(name=name,p=p,q=q,g=g,pk=pk,r1=r1,r2=r2,e=cs[1],z0=cs[2],cs=list(cs),
             kind='numeric_zero_nonce' if r2==0 else 'source_shaped',
             reached=old59+['']*6,initial_mem=2,fresh_tape='101')
def bounds(c):return first.bounds(c)
def expected(c,m=0):
 ws=c['reached'].copy();p,q=c['p'],c['q'];e,z=c['e'],c['z0']
 alpha=pow(c['g'],c['r2'],p)
 if m==1:alpha=pow(c['g'],c['r1'],p)
 if m==2:e=0 # old p0 fixture e0 is independently fixed at zero
 if m==3:z=4%q # old p0 fixture z00 is independently fixed at 4 mod q
 answer=pow(c['g'],z,p)*pow(alpha,q-e,p)%p
 ws[60]=second.bits(answer)
 if m==4:ws[60]='';ws[61]=second.bits(answer)
 if m==5:ws[59]=second.bits(c['e'])
 if m in (6,7):j=48 if m==6 else 49;ws[j]='0'+ws[j]
 return ws,'101',0

def fixtures():
 fs=[make('minimal_q2_zero',p=3,q=2,g=2,pk=1,r1=1,r2=1,cs=(0,0,0,1)),
     make('distinct_second_nonce_fresh_scalars'),
     make('zero_e_uses_q',r2=1,cs=(2,0,2,1),occupied=True),
     make('q11_max_z0',p=23,q=11,g=2,pk=4,r1=3,r2=1,cs=(0,1,10,0)),
     make('q11_zero_e_sticky',p=23,q=11,g=2,pk=4,r1=3,r2=1,cs=(0,0,10,0),bad=True,occupied=True,vote=False),
     make('numeric_zero_nonce',r2=0,cs=(2,1,2,0))]
 for seed in (118,606,20260914):
  rng=random.Random(seed);p,q,g=rng.choice([(7,3,2),(11,5,3),(23,11,2)])
  fs.append(make('seed_'+str(seed),p=p,q=q,g=g,pk=pow(g,2,p),r1=rng.randrange(1,q),r2=rng.randrange(1,q),
    cs=tuple(rng.randrange(q) for _ in range(4)),slack=rng.randrange(2),
    vote=bool(rng.randrange(2)),occupied=bool(rng.randrange(2)),bad=bool(rng.randrange(2))))
 return fs

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSecondCommitNativeGenerated.lean';path.write_text(src)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 report=dict(status='running',host_timeout_seconds=300,seeds=[118,606,20260914],discarded=0,gaveUp=0,
   header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSecondCommitMachine.lean').read_bytes()).hexdigest(),
   driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[],rejections=[])
 path=OUT/'second-commit-native.json';r=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,want):
  assert n.agrees(a,*want),(c['name'],a,want)
  T,C=bounds(c)
  assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a,T,C)
 save()
 try:
  r=n.GateRunner(src,'PrimeSecondCommitNativeReproduction',bounds=bounds,host_timeout=300)
  fs=fixtures()
  for c in fs[:2]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  names=('wrong_first_nonce_alpha','reused_old_e','reused_old_z0','wrong_output_port','omitted_e_digits_cleanup',
         'corrupted_first_proof','corrupted_updated_saved','bypassed_entry_guard')
  for m,name in enumerate(names,1):
   c=copy.deepcopy(fs[1])
   if m==8:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);check(a,c,want)
   baseline=(c['reached'],'101',0,1) if m==8 else expected(c)
   assert not n.agrees(a,*baseline),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));save();print(name+' PASS',flush=True)
  c=copy.deepcopy(fs[1]);c['initial_mem']=1;a=r.execute(0,c)
  check(a,c,(c['reached'],'101',0,1));report['rejections'].append(dict(input=c,actual=a));save()
  for c in fs[2:]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  report.update(status='pass',canonical_cases=len(report['cases']),mutation_cases=len(report['mutants']),guard_rejections=len(report['rejections']))
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({key:val for key,val in report.items() if key not in ('cases','mutants','rejections')},indent=2),flush=True)
if __name__=='__main__':main()
