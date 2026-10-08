#!/usr/bin/env python3
"""Actual p1 one-branch coordinate gate: full states and unchanged numeric caps.

Uses the existing checked native snapshot adapter and independent integer/codec
fixtures. --generate-only emits the imported driver without Lean execution.
"""
from pathlib import Path
import sys,json,hashlib,copy,random
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_second_commit as prior
n=prior.n
PART='second';MOD='PrimeSecondOneSecondMachine';PORTS=70;DEST=69
BASE=prior.BASE.replace('PrimeSecondCommitControls',MOD+'Controls').replace('open PrimeSecondCommitMachine','open '+MOD)
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 70 size 3 :=
  if m == 1 && 522 <= l.val then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (66 : Fin 70) 55) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 2 && 13 <= l.val && l.val < 17 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (57 : Fin 70) 56) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 3 && 17 <= l.val && l.val < 21 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (16 : Fin 70) 15) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 4 && 29 <= l.val && l.val < 33 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (67 : Fin 70) 51) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 5 && 45 <= l.val && l.val < 49 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (69 : Fin 70) 61) (Equiv.refl _) (Equiv.refl _) (program l))
  else if (m == 6 || m == 7) && l == 12 then .compute
    (.push (if m == 6 then 68 else 49) (fun _ => false) (program l))
  else if m == 8 && l == 10 then .compute (.goto (fun _ => 11))
  else code l
'''
def source():
 return 'import ExplainableCrypto.Helios.Computational.'+MOD+'\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls',MOD+'Controls')
def make(name,**kw):
 c=prior.make(name,**kw);p,q=c['p'],c['q'];c0,e,z0,z1=c['cs']
 alpha=pow(c['g'],c['r2'],p);beta=pow(c['pk'],c['r2'],p)
 B=pow(c['pk'],z0,p)*pow(beta,q-e,p)%p;d=(c0+q-e)%q;gamma=beta*pow(c['g'],q-1,p)%p
 ws=prior.expected(c)[0]+[prior.second.bits(B),prior.second.nat(d),prior.second.bits(gamma)]
 C=pow(c['g'],z1,p)*pow(alpha,q-d,p)%p
 if PART=='second':ws.append(prior.second.bits(C))
 c.update(d=d,z1=z1,alpha=alpha,beta=beta,gamma=gamma,oneC=C,reached=ws+[''])
 assert len(c['reached'])==PORTS
 return c
def fixtures():
 fs=[make('minimal_zero_d',p=3,q=2,g=2,pk=1,r1=1,r2=1,cs=(0,0,1,0)),
     make('distinct_operands',p=23,q=11,g=2,pk=4,r1=3,r2=1,cs=(0,1,10,3)),
     make('q3_zero_d',cs=(1,1,0,2),occupied=True,vote=False),
     make('q3_underflow_d',cs=(0,2,1,2),bad=True,occupied=True)]
 for seed in (118,606,20260914):
  rng=random.Random(seed);p,q,g=rng.choice([(7,3,2),(11,5,3),(23,11,2)])
  fs.append(make('seed_'+str(seed),p=p,q=q,g=g,pk=pow(g,2,p),r1=rng.randrange(1,q),r2=rng.randrange(1,q),
    cs=tuple(rng.randrange(q) for _ in range(4)),slack=rng.randrange(2),vote=bool(rng.randrange(2)),occupied=bool(rng.randrange(2)),bad=bool(rng.randrange(2))))
 return fs
def bounds(c):return prior.bounds(c)
def expected(c,m=0):
 ws=c['reached'].copy();p,q=c['p'],c['q'];d,z=c['d'],c['z1']
 base=c['g'] if PART=='first' else c['pk'];a=c['alpha'] if PART=='first' else c['gamma']
 if m==1:d=c['e']
 if m==2:z=c['cs'][2]
 if m==3:base=c['pk'] if PART=='first' else c['g']
 if m==4:a=c['beta']
 answer=pow(base,z,p)*pow(a,q-d,p)%p
 ws[DEST]=prior.second.bits(answer)
 if m==5:ws[DEST]='';ws[61]=prior.second.bits(answer)
 if m==6:j=68;ws[j]='0'+ws[j]
 if m==7:ws[49]='0'+ws[49]
 if m==8:ws[59]=prior.second.bits(c['d'])
 return ws,'101',0

def main():
 src=source();path=OUT/('second-one-'+PART+'-native.json')
 if '--generate-only' in sys.argv:
  f=OUT/(MOD+'NativeGenerated.lean');f.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(f)),indent=2));return
 report=dict(status='running',host_timeout_seconds=300,seeds=[118,606,20260914],discarded=0,gaveUp=0,
  header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational'/(MOD+'.lean')).read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[],rejections=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,want):
  assert n.agrees(a,*want),(c['name'],a,want)
  T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a,T,C)
 r=None;save()
 try:
  r=n.GateRunner(src,MOD+'NativeReproduction',bounds=bounds,host_timeout=300);fs=fixtures()
  for c in fs[:2]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('wrong_d','wrong_z1','wrong_base','wrong_ciphertext','wrong_output','corrupt_prior_coordinate','corrupt_saved','omit_scratch_cleanup'),1):
   c=fs[1];a=r.execute(m,c);want=expected(c,m);check(a,c,want);assert not n.agrees(a,*expected(c)),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));save();print(name+' PASS',flush=True)
  c=copy.deepcopy(fs[1]);c['initial_mem']=1;a=r.execute(0,c);check(a,c,(c['reached'],'101',0,1));report['rejections'].append(dict(input=c,actual=a));save()
  for c in fs[2:]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  report.update(status='pass',canonical_cases=len(report['cases']),mutation_cases=len(report['mutants']),guard_rejections=len(report['rejections']))
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','rejections')},indent=2),flush=True)
if __name__=='__main__':main()
