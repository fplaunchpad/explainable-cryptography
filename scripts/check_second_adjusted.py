#!/usr/bin/env python3
"""Actual p1 adjusted-beta relocation: full68 states and original costs.

Build PrimeSecondAdjustedMachine, then run this script. Independent integer
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
import check_second_difference as difference
import check_adjusted_beta as adjusted
n=prior.n
NAME='PrimeSecondAdjusted'
BASE=prior.BASE.replace('PrimeSecondCommitControls',NAME+'Controls').replace('open PrimeSecondCommitMachine','open '+NAME+'Machine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 68 size 3 :=
  if m == 1 && l == 0 then .compute (.load (fun _ => 2) (.goto (fun _ => 1)))
  else if m == 2 && l == 1 then .compute (.load (fun _ => 2) .halt)
  else if m == 3 && 2 <= l.val && l.val < 194 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (16 : Fin 68) 15)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if (m == 4 || m == 5 || m == 6) && l == 1 then .compute
    (.push (if m == 4 then 66 else if m == 5 then 60 else 49) (fun _ => false) (program l))
  else if m == 7 && l == 0 then .compute
    (.load (fun _ => 0) (.goto (fun _ => PrimeAdjustedBetaMachine.powerLabel (BinaryModPower.copyLabel 0 0))))
  else code l
'''
def source():return 'import ExplainableCrypto.Helios.Computational.'+NAME+'Machine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls',NAME+'Controls')
def fixtures():
 fs=[]
 for c in difference.fixtures():
  f=copy.deepcopy(c);f['reached']=difference.expected(c)[0]+[''];fs.append(f)
 return fs
bounds=adjusted.bounds
def expected(c,m=0):
 ws=c['reached'].copy();p,q=c['p'],c['q']
 if c['initial_mem']!=2 and m!=7:return ws,'101',0,1
 beta=pow(c['pk'],c['r2'],p);inv=pow(c['g'],q-1,p)
 gamma=beta*inv%p
 if m==1:gamma=0
 if m==2:ws[23]=prior.second.bits(inv);return ws,'101',0
 if m==3:gamma=beta*pow(c['pk'],q-1,p)%p
 ws[67]=prior.second.bits(gamma)
 if m in (4,5,6):j={4:66,5:60,6:49}[m];ws[j]='0'+ws[j]
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  p=OUT/(NAME+'NativeGenerated.lean');p.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(p))));return
 report=dict(status='running',seeds=[118,606,20260914],discarded=0,gaveUp=0,cases=[],mutants=[],rejections=[],
  header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational'/ (NAME+'Machine.lean')).read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 path=OUT/'second-adjusted-native.json';r=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,want):
  assert n.agrees(a,*want),(c['name'],a,want)
  T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a,T,C)
 save()
 try:
  r=n.GateRunner(src,NAME+'NativeReproduction',bounds=bounds,host_timeout=300);fs=fixtures()
  for c in fs[:2]:
   a=r.execute(0,c);check(a,c,expected(c));report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('omitted_inverse','omitted_product','wrong_generator','corrupted_d','corrupted_A','corrupted_saved','bypassed_guard'),1):
   c=copy.deepcopy(fs[1])
   if m==7:c['initial_mem']=1
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
