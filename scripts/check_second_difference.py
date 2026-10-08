#!/usr/bin/env python3
"""Actual p1 scalar-difference relocation: full67 states and original costs.

Build PrimeSecondDifferenceMachine, then run this script. Independent integer
fixtures extend the prior second-commitment fixture by B; they are source-shaped
numeric states, with the explicitly labeled zero-nonce boundary retained.
No raw-election reachability or extra random-campaign claim. --generate-only
writes the production-import driver; reports stay in reproduction/.
"""
from pathlib import Path
import sys,json,copy,hashlib
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_second_commit as prior
import check_scalar_difference as scalar
n=prior.n
NAME='PrimeSecondDifference'
BASE=prior.BASE.replace('PrimeSecondCommitControls',NAME+'Controls').replace('open PrimeSecondCommitMachine','open '+NAME+'Machine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 67 size 3 :=
  if m == 1 && 6 <= l.val && l.val < 10 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (54 : Fin 67) 55)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 2 && l == 2 then .compute (.load (fun _ => 2) (.goto (fun _ => 3)))
  else if m == 3 && l == 4 then .compute
    (.load (fun _ => 0) (.goto (fun _ => ScalarDifferenceMachine.writerEntry)))
  else if (m == 4 || m == 5) && l == 5 then .compute
    (.push (if m == 4 then 48 else 65) (fun _ => false) (program l))
  else if m == 6 && l == 0 then .compute
    (.load (fun _ => 0) (.goto (fun _ => ScalarDifferenceMachine.copyLabel false 0)))
  else code l
'''
def source():return 'import ExplainableCrypto.Helios.Computational.'+NAME+'Machine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls',NAME+'Controls')
def reached_pair(c):
 ws=prior.expected(c)[0];p,q=c['p'],c['q'];beta=pow(c['pk'],c['r2'],p)
 b=pow(c['pk'],c['z0'],p)*pow(beta,q-c['e'],p)%p
 return ws+[prior.second.bits(b)]
def fixtures():
 fs=[]
 for c in prior.fixtures():
  f=copy.deepcopy(c);f.update(reached=reached_pair(c)+[''],c=c['cs'][0]);fs.append(f)
 return fs
bounds=scalar.bounds
def expected(c,m=0):
 ws=c['reached'].copy();q,cv,e=c['q'],c['c'],c['e']
 if c['initial_mem']!=2 and m!=6:return ws,'101',0,1
 d=(cv-e)%q
 if m==1:d=(e-cv)%q
 if m==2:d=cv
 ws[66]=prior.n.k.nat(d)
 if m==3:ws[23]=prior.second.bits(e)
 if m in (4,5):j=48 if m==4 else 65;ws[j]='0'+ws[j]
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  p=OUT/(NAME+'NativeGenerated.lean');p.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(p))));return
 report=dict(status='running',seeds=[118,606,20260914],discarded=0,gaveUp=0,cases=[],mutants=[],rejections=[],
  header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational'/ (NAME+'Machine.lean')).read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 path=OUT/'second-difference-native.json';r=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,want):
  assert n.agrees(a,*want),(c['name'],a,want)
  T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a,T,C)
 save()
 try:
  r=n.GateRunner(src,NAME+'NativeReproduction',bounds=bounds,host_timeout=300);fs=fixtures()
  for c in fs[:2]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('reversed_c_e','omitted_difference','omitted_e_cleanup','corrupted_p0','corrupted_second_B','bypassed_guard'),1):
   c=copy.deepcopy(fs[1])
   if m==6:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);check(a,c,want);assert not n.agrees(a,*expected(c)),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));save();print(name+' PASS',flush=True)
  c=copy.deepcopy(fs[1]);c['initial_mem']=1;a=r.execute(0,c);check(a,c,expected(c));report['rejections'].append(dict(input=c,actual=a));save()
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
