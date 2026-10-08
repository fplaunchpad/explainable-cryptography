#!/usr/bin/env python3
"""Bounded original-code gate; build ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine.

Eight directed canonical cases, seven actual mutations and one guard rejection.
Full 40-port states preserve both commitments and saved scalar/context words.
No random campaign is claimed.

Use --generate-only to emit the production-import driver without executing Lean.
The fixtures, actual mutations, original clock/charge caps and complete-state
comparators reproduce the retained passing campaign. Outputs use a separate
reproduction directory; historical reports remain unchanged.
"""
from pathlib import Path
import sys,json,hashlib,copy
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_sim_commit_second as old
n=old.n;k=old.k
BASE=old.BASE.replace('PrimeSimCommitSecondControls','PrimeAdjustedBetaControls').replace('open PrimeSimCommitSecondMachine','open PrimeAdjustedBetaMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 40 size 3 :=
  if m == 1 && l == 0 then .compute (.load (fun _ => 2) (.goto (fun _ => 1)))
  else if m == 2 && l == 1 then .compute (.load (fun _ => 2) .halt)
  else if m == 3 && l.val >= 2 && l.val < 194 then
    .compute (TM2FiniteCoordinates.translate (Equiv.swap (16 : Fin 40) 15)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if (m == 4 || m == 5 || m == 6) && l == 1 then
    .compute (.push (if m == 4 then 14 else if m == 5 then 3 else 38)
      (fun _ => false) (program l))
  else if m == 7 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => powerLabel (BinaryModPower.copyLabel 0 0))))
  else code l
'''
def source():return 'import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeAdjustedBetaControls')
def fixtures():
 fs=[]
 for f in old.fixtures():
  c=f['input'].copy();ws=f['expected39'].copy();ws[1]=k.nat((c['c']-c['e'])%c['q'])
  c.update(name=f['name'],reached=ws+[''],fresh_tape='101',initial_mem=2);fs.append(c)
 c=copy.deepcopy(fs[-1]);c['name']='nonempty_extra_frame'
 for j,w in ((4,'101'),(5,'01'),(8,'110'),(9,'1')):c['reached'][j]=w
 fs.append(c);return fs
def bounds(c):
 P=c['p'].bit_length();L=(c['q']-1).bit_length();M=9*P+11+P*(34*P+38)
 T=3*L+5+L*(2*M+12*P+16)+M+2;return T,32*T
def expected(c,m=0):
 ws=c['reached'].copy()
 if c['initial_mem']!=2 and m!=7:return ws,'101',0,1
 p,q=c['p'],c['q'];beta=sum(int(b)<<i for i,b in enumerate(ws[0]));inverse=pow(c['g'],q-1,p)
 ans=beta*inverse%p
 if m==1:ans=0
 elif m==2:ws[23]=k.bits(inverse);return ws,'101',0,2
 elif m==3:ans=beta*pow(c['pk'],q-1,p)%p
 ws[39]=k.bits(ans)
 if m in (4,5,6):j={4:14,5:3,6:38}[m];ws[j]='0'+ws[j]
 return ws,'101',0,2
def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeAdjustedBetaNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 runner=None;path=OUT/'adjusted-beta-native.json'
 report=dict(status='running',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,seeds=[],scope='eight directed full-state fixtures; no random campaign',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeAdjustedBetaMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  runner=n.GateRunner(src,'PrimeAdjustedBetaNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures()
  for i in (2,0):
   c=fs[i];a=runner.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('omitted_power','omitted_product','wrong_generator','corrupted_context','corrupted_first_A','corrupted_second_B','bypassed_entry_guard'),1):
   c=copy.deepcopy(fs[0])
   if m==7:
    c['initial_mem']=1;a=runner.execute(0,c);assert n.agrees(a,*expected(c)),('guard baseline',a);report['guard_rejection']=dict(input=c,actual=a)
   a=runner.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original mutant cap',a)
   assert not n.agrees(a,*expected(c)),('insensitive',name,a)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  for i in (1,3,4,5,6,7):
   c=fs[i];a=runner.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report.update(status='pass',guard_rejections=1)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
