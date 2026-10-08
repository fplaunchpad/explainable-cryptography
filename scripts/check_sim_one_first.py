#!/usr/bin/env python3
"""Gate the actual one-branch coordinate through its fixed finite frame.

Build ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine, then run this script.
Four directed p3/q2 and p7/q3 full states cover both votes, zero and wrapped
challenge difference. Six actual instruction mutations check operands, output,
prior-coordinate preservation and scratch cleanup. Full state, zero queries,
residual101 and unchanged numeric clock/charge caps are compared independently.
No random or larger campaign is claimed. Existing checked native identity
adapters leave the original step semantics unchanged.

--generate-only emits a production-import driver without executing Lean.
Reproduction reports use separate paths to retain historical evidence.
"""
from pathlib import Path
import sys,json,hashlib,copy
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_sim_commit_second as prior
n=prior.n;k=prior.k
BASE=prior.BASE.replace('PrimeSimCommitSecondControls','PrimeSimOneFirstControls').replace('open PrimeSimCommitSecondMachine','open PrimeSimOneFirstMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 42 size 3 :=
  if m == 1 || m == 2 || m == 3 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (1 : Fin 42) 11 else
       if m == 2 then Equiv.swap 15 16 else Equiv.swap 17 0)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 4 && l.val >= 45 && l.val < 49 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (40 : Fin 42) 41)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 5 && l == 12 then .compute (.push 3 (fun _ => false) (program l))
  else if m == 6 && l == 10 then .compute (.goto (fun _ => 11))
  else code l
'''
def source():return 'import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimOneFirstControls')
def fixtures():
 import check_sim_one_second as second
 fs=second.fixtures()
 for c in fs:c['reached']=c['reached'][:40]+['','']
 return fs
def bounds(c):return prior.first.bounds(c)
def expected(c,m=0):
 ws=c['reached'].copy();p,q=c['p'],c['q'];z=c['z1'];base=c['g'];a=c['alpha'];d=c['d']
 if m==1:d=c['e']
 elif m==2:base=c['pk']
 elif m==3:a=sum(int(b)<<i for i,b in enumerate(ws[0]))
 ws[40]=k.bits(pow(base,z,p)*pow(a,q-d,p)%p)
 if m==4:ws[40]=''
 if m==5:ws[3]='0'+ws[3]
 if m==6:ws[41]=k.bits(d)
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimOneFirstNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 r=None;path=OUT/'sim-one-first-native.json'
 report=dict(status='running',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,seeds=[],scope='four directed p3q2/p7q3 source-consistent full states; zero and wrapped difference',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimOneFirstMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeSimOneFirstNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures()
  for i in (0,1):
   c=fs[i];a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('wrong_challenge','wrong_generator','wrong_ciphertext_alpha','wrong_output','corrupted_prior_first_A','omitted_scratch_cleanup'),1):
   c=fs[1];a=r.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original mutant caps',a)
   assert not n.agrees(a,*expected(c)),('insensitive',name,a)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  for c in fs[2:]:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
