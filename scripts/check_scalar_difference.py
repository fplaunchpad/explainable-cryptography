#!/usr/bin/env python3
"""Bounded original-code gate; build ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine.

26 canonical cases, six actual mutations and one original guard rejection.
Seeds 118, 606 and 20260914; full ten-port states and zero-query tape preservation.

Use --generate-only to emit the production-import driver without executing Lean.
The fixtures, actual mutations, original clock/charge caps and complete-state
comparators reproduce the retained passing campaign. Outputs use a separate
reproduction directory; historical reports remain unchanged.
"""
from pathlib import Path
import sys,json,random,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_honest_transcript_native as n
k=n.k
BASE=k.BASE.split('private def replaceRecord')[0].replace('PrimeHonestTranscriptControls','ScalarDifferenceControls').replace('open PrimeHonestTranscriptMachine','open ScalarDifferenceMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 10 size 3 :=
  if m == 1 && l.val >= 6 && l.val < 10 then
    .compute (TM2FiniteCoordinates.translate (Equiv.swap (1 : Fin 10) 2)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 2 && l == 2 then .compute (.load (fun _ => 2) (.goto (fun _ => 3)))
  else if m == 3 && l == 4 then .compute (.load (fun _ => 0) (.goto (fun _ => writerEntry)))
  else if (m == 4 || m == 5) && l == 5 then
    .compute (.push (if m == 4 then 1 else 2) (fun _ => false) (program l))
  else if m == 6 && l == 0 then .compute (.load (fun _ => 0) (.goto (fun _ => copyLabel false 0)))
  else code l
'''
def source():
 return 'import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','ScalarDifferenceControls')
def make(q,c,e,mem=2):
 assert 0<=c<q and 0<=e<q
 return dict(q=q,c=c,e=e,reached=[k.bits(q),k.nat(c),k.nat(e)]+['']*7,fresh_tape='101',initial_mem=mem)
def bounds(f):
 Q=f['q'].bit_length();T=(f['q']-1).bit_length();clock=18*T+26*Q+47;return clock,32*clock
def expected(f,m=0):
 q,c,e=f['q'],f['c'],f['e'];ws=f['reached'].copy()
 if f['initial_mem']!=2 and m!=6:return ws,'101',0,1
 ans=(c-e)%q
 if m==1:ans=(e-c)%q
 elif m==2:ans=c
 ws[3]=k.nat(ans)
 if m==3:ws[4]=k.bits(e)
 if m==4:ws[1]='0'+ws[1]
 if m==5:ws[2]='0'+ws[2]
 return ws,'101',0,2
def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'ScalarDifferenceNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 r=None;path=OUT/'scalar-difference-native.json'
 report=dict(status='running',seeds=[118,606,20260914],discarded=0,gaveUp=0,cases=[],mutants=[],header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/ScalarDifferenceMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'ScalarDifferenceNativeReproduction',bounds=bounds,host_timeout=90)
  f=make(1,0,0);a=r.execute(0,f);assert n.agrees(a,*expected(f)),(f,a,expected(f));report['cases'].append(dict(input=f,actual=a));save();print('minimal q1 zero PASS',flush=True)
  f=make(3,1,2);a=r.execute(0,f);assert n.agrees(a,*expected(f)),(f,a,expected(f));report['cases'].append(dict(input=f,actual=a));save();print('q3 modular underflow PASS',flush=True)
  for m,name in enumerate(('reversed_operands','skipped_difference','omitted_digit_cleanup','corrupted_c_prefix','corrupted_e_prefix','bypassed_entry_guard'),1):
   f=make(3,1,2,1 if m==6 else 2)
   if m==6:
    a=r.execute(0,f);assert n.agrees(a,*expected(f)),('guard baseline',a,expected(f));report['guard_rejection']=dict(input=f,actual=a)
   a=r.execute(m,f);want=expected(f,m);assert n.agrees(a,*want),(name,f,a,want)
   clock,cost=bounds(f);assert a['steps']<=clock and a['charge']<=cost,('original mutant cap',a)
   assert not n.agrees(a,*expected(f)),('insensitive',name,a)
   report['mutants'].append(dict(name=name,input=f,actual=a,independent_expected=want));save();print('detected '+name,flush=True)
  cases=[make(q,c,e) for q in (2,3,11,17,256) for c,e in ((0,q-1),(q-1,0),(q-1,q-1))]
  for seed in report['seeds']:
   rng=random.Random(seed)
   for _ in range(3):
    q=rng.randrange(2,258);cases.append(make(q,rng.randrange(q),rng.randrange(q)))
  for i,f in enumerate(cases):
   a=r.execute(0,f);assert n.agrees(a,*expected(f)),(f,a,expected(f));report['cases'].append(dict(input=f,actual=a));save();print('canonical '+str(i)+' PASS',flush=True)
  report.update(status='pass',canonical_cases=len(report['cases']),mutation_cases=len(report['mutants']),guard_rejections=1)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
