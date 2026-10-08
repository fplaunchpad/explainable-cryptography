#!/usr/bin/env python3
"""Actual second zero-branch commitment coordinate: seven cases and mutations.

Build ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine, then
run `python3 scripts/check_prime_sim_commit_second.py`. Seven directed fixtures
retain the first coordinate and all original words, while comparing the new
coordinate against independent integer arithmetic. All 39 ports, zero queries,
residual101, original clock and charge are checked. Seven actual instruction
mutations cover operand selection, both result locations, context and cleanup.

This is a bounded directed campaign; no random campaign is claimed. Fixture
construction uses existing independent encoders and the first-coordinate Python
oracle, never Lean readouts. Native snapshot/table adapters are proved identical
to their original objects. The host response allowance is120seconds.
--generate-only writes a production-import driver without executing Lean.
Historical artifacts remain untouched; reproduction outputs have distinct names.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_sim_commit as first
n=first.n;k=first.k
BASE=first.BASE.replace('PrimeSimCommitControls','PrimeSimCommitSecondControls').replace('open PrimeSimCommitMachine','open PrimeSimCommitSecondMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 39 size 3 :=
  if (m == 1 && l.val >= 17 && l.val < 21) || (m == 2 && l.val >= 29 && l.val < 33) ||
      (m == 5 && l.val >= 45 && l.val < 49) then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate
        (if m == 1 then Equiv.swap (15 : Fin 39) 16 else if m == 2 then Equiv.swap 0 17 else Equiv.swap 38 3)
        (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if (m == 3 || m == 6) && l == 12 then
    match code l with
    | .compute s => .compute (.push (if m == 3 then 3 else 14) (fun _ => false) s)
    | c => c
  else if m == 4 && l == 0 then .compute (.load (fun _ => 2) .halt)
  else if m == 7 && l == 6 then .compute (.goto (fun _ => 7))
  else code l
'''
def source():return 'import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimCommitSecondControls')
def fixtures():
 cases=[('q3_true_distinct',dict()),('q3_false_distinct',dict(vote=False,z0=2)),
  ('q2_true_distinct',dict(p=3,q=2,g=2,pk=1,c=0,e=1,z0=1,z1=0)),
  ('q11_zero',dict(p=23,q=11,g=2,pk=4,c=0,e=0,z0=0,z1=10)),
  ('q11_true_distinct',dict(p=23,q=11,g=2,pk=4,c=2,e=1,z0=3,z1=4)),
  ('q11_false_distinct',dict(p=23,q=11,g=2,pk=4,c=2,e=1,z0=3,z1=4,vote=False)),
  ('q11_reverse_distinct',dict(p=23,q=11,g=2,pk=4,c=2,e=3,z0=6,z1=4,order=True))]
 out=[]
 value=lambda word:sum(int(bit)<<i for i,bit in enumerate(word))
 for name,kwargs in cases:
  c=first.make(**kwargs);before=first.expected(c)[0];alpha=value(before[17]);beta=value(before[0])
  p,q,e,z=c['p'],c['q'],c['e'],c['z0'];A=value(before[3])
  B=pow(c['pk'],z,p)*pow(beta,q-e,p)%p
  assert pow(c['g'],q,p)==pow(c['pk'],q,p)==pow(alpha,q,p)==pow(beta,q,p)==1
  initial=before+[''];expected=initial.copy();expected[38]=k.bits(B)
  out.append(dict(name=name,input=c,initial39=initial,expected39=expected,first_coordinate=A,
   second_coordinate=B,alpha=alpha,beta=beta,power_base=c['pk'],second_exponent=q-e,
   clock=first.bounds(c)[0],charge_bound=first.bounds(c)[1],coins=0,hashes=0,remaining='101',
   status='independently staged; no controller campaign run'))
 return out

def case(f):return dict(f['input'],reached=f['initial39'],fresh_tape='101',initial_mem=2)
def expected(f,m=0):
 ws=f['expected39'].copy();c=f['input'];p,q,z,e=c['p'],c['q'],c['z0'],c['e']
 if m==1:ws[38]=k.bits(pow(c['g'],z,p)*pow(f['beta'],q-e,p)%p)
 if m==2:ws[38]=k.bits(pow(c['pk'],z,p)*pow(f['alpha'],q-e,p)%p)
 if m==3:ws[3]='0'+ws[3]
 if m==4:ws=f['initial39'].copy()
 if m==5:ws[3]=ws[38];ws[38]=''
 if m==6:ws[14]='0'+ws[14]
 if m==7:ws[29]=k.bits(p)
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimCommitSecondNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 report=dict(status='running',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,seeds=[],scope='seven directed independent fixtures; no random or larger campaign claimed',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimCommitSecondMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 path=OUT/'prime-sim-commit-second-native.json';runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=n.GateRunner(src,'PrimeSimCommitSecondNativeReproduction',bounds=first.bounds,host_timeout=120)
  fs=fixtures()
  for index in [2,0]:
   f=fs[index];a=runner.execute(0,case(f));assert n.agrees(a,*expected(f)),(f,a,expected(f))
   report['cases'].append(dict(name=f['name'],input=f,actual=a));report['canonical_cases']+=1;save();print(f['name']+' PASS',flush=True)
  f=fs[0]
  for m,name in enumerate(['wrong_generator_base','wrong_alpha_for_beta','overwritten_first_A','skipped_second_coordinate','wrong_output_port','corrupted_context','uncleared_workspace_modulus'],1):
   a=runner.execute(m,case(f));original_clock,original_cost=first.bounds(f['input'])
   assert a['steps']<=original_clock and a['charge']<=original_cost,(name,'original cap exceeded',a)
   want=expected(f,m);assert n.agrees(a,*want),(name,f,a,want)
   assert not n.agrees(a,*expected(f)),(name,'insensitive')
   report['mutants'].append(dict(name=name,input=f,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  for index in [1,3,4,5,6]:
   f=fs[index];a=runner.execute(0,case(f));assert n.agrees(a,*expected(f)),(f,a,expected(f))
   report['cases'].append(dict(name=f['name'],input=f,actual=a));report['canonical_cases']+=1;save();print(f['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
