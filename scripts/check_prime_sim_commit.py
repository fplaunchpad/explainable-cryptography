#!/usr/bin/env python3
"""Actual first simulated-commitment coordinate: nine cases, eight mutations.

Build ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine, then run
`python3 scripts/check_prime_sim_commit.py`. Independent integer arithmetic,
full 38-port preservation/cleanup, zero queries, residual tape and expanded
clock/charge bounds are checked. Fixed seeds 118, 606, 20260914; includes zero,
maximal scalar values, both votes/orders and distinct p/q.

Existing native snapshot/table adapters are proved equal to original objects
inside the driver. This bounded gate is separate from the general run theorem.
The retained initial mutant-oracle failure concerned the unconsumed port31
when multiplication is skipped; its corrected full-state oracle is included.

--generate-only writes a production-import driver without executing Lean.
Artifacts use tmp/concrete-helios/reproduction; historical reports are retained.
"""
import sys,json,hashlib,random
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_honest_transcript_native as n
k=n.k
BASE=k.BASE.split('private def replaceRecord')[0].replace('PrimeHonestTranscriptControls','PrimeSimCommitControls').replace('open PrimeHonestTranscriptMachine','open PrimeSimCommitMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 38 size 3 :=
  if m == 1 && l == powerLabel 0 (BinaryModPower.copyLabel 0 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 3)))
  else if m == 2 && l == powerLabel 1 (BinaryModPower.copyLabel 0 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 4)))
  else if m == 3 && l == multiplyLabel (BinaryModMultiply.copyLabel 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 5)))
  else if m == 4 && l.val >= 33 && l.val < 37 then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (9 : Fin 38) 1)
      (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 5 && l == 0 then
    .compute (.load (fun _ => 2) (.goto (fun _ => 1)))
  else if (m == 6 || m == 7) && l == 12 then
    match code l with
    | .compute s => .compute (.push (if m == 6 then 10 else 14) (fun _ => false) s)
    | c => c
  else if m == 8 && l == 6 then .compute (.goto (fun _ => 7))
  else code l
'''
def source():
 return 'import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimCommitControls')
def make(p=7,q=3,g=2,pk=4,c=0,e=1,z0=1,z1=2,**kw):
 f=k.make(p=p,q=q,g=g,pk=pk,**kw)
 ws=f['reached'].copy();ws[2]=k.bits(q)
 for j,v in [(10,c),(11,e),(12,z0),(7,z1)]:
  assert 0<=v<q;ws[j]=k.nat(v)
 f.update(reached=ws+['']*15,fresh_tape='101',c=c,e=e,z0=z0,z1=z1)
 return f
def bounds(f):
 p,q=f['p'],f['q'];P=p.bit_length();Q=q.bit_length()
 mult=lambda width:9*P+11+width*(34*P+38)
 power=lambda width:3*width+5+width*(2*mult(P)+12*P+16)
 comp=10*(q-1).bit_length()+5*Q+17
 ticks=comp+2*power(Q)+mult(P)+22*P+13*Q+54
 return ticks,32*ticks
def expected(f,m=0):
 p,q,g,e,z=f['p'],f['q'],f['g'],f['e'],f['z0'];ws=f['reached'].copy()
 alpha=sum(int(b)<<i for i,b in enumerate(ws[17]));a=pow(g,z,p);b=pow(alpha,q-e,p)
 ans=a*b%p
 if m in (1,2,3):ans=0
 elif m==4:ans=a*pow(alpha,e,p)%p
 elif m==5:ans=a
 ws[3]=k.bits(ans)
 if m==3:ws[31]=k.bits(b) # skipped multiplier never consumes its raw operand
 if m==6:ws[10]='0'+ws[10]
 if m==7:ws[14]='0'+ws[14]
 if m==8:ws[29]=k.bits(p)
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimCommitNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 report=dict(status='running',seeds=[118,606,20260914],discards=0,gaveUp=0,header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimCommitMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 path=OUT/'prime-sim-commit-native.json';runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=n.GateRunner(src,'PrimeSimCommitNativeReproduction',bounds=bounds,host_timeout=120)
  minimal=make(p=3,q=2,g=2,pk=1,c=0,e=0,z0=0,z1=1)
  a=runner.execute(0,minimal);assert n.agrees(a,*expected(minimal)),(minimal,a,expected(minimal));report['cases'].append(dict(name='minimal_zero',input=minimal,actual=a));save();print('minimal q2 zero PASS',flush=True)
  witness=make();a=runner.execute(0,witness);assert n.agrees(a,*expected(witness)),(witness,a,expected(witness));report['cases'].append(dict(name='nontrivial_sign',input=witness,actual=a));save();print('q3 nontrivial sign PASS',flush=True)
  for m,name in enumerate(['omit_first_power','omit_second_power','omit_product','positive_exponent','skip_complement','corrupt_c_prefix','corrupt_context','omit_p_cleanup'],1):
   a=runner.execute(m,witness);want=expected(witness,m);assert n.agrees(a,*want),(name,witness,a,want)
   assert not n.agrees(a,*expected(witness)),(name,'insensitive')
   report['mutants'].append(dict(name=name,input=witness,actual=a,independent_expected=want));save();print('detected '+name,flush=True)
  bad=make(initial_mem=1);a=runner.execute(0,bad);assert n.agrees(a,bad['reached'],'101',0,1),(bad,a);report['guard_rejection']=dict(input=bad,actual=a);save()
  cases=[make(p=3,q=2,g=2,pk=1,c=1,e=1,z0=1,z1=0,vote=False,order=True,saved=''),make(p=23,q=11,g=2,pk=4,c=10,e=0,z0=10,z1=1),make(p=23,q=11,g=2,pk=4,c=0,e=10,z0=0,z1=10,vote=False,order=True),make(p=23,q=11,g=2,pk=4,c=2,e=3,z0=6,z1=4,vote=False)]
  for seed in (118,606,20260914):
   rng=random.Random(seed);p,q,g=rng.choice([(7,3,2),(11,5,3),(23,11,2)])
   cases.append(make(p=p,q=q,g=g,pk=pow(g,2,p),c=rng.randrange(q),e=rng.randrange(q),z0=rng.randrange(q),z1=rng.randrange(q),vote=bool(rng.randrange(2)),order=bool(rng.randrange(2)),saved='10101',slack=1))
  for i,f in enumerate(cases):
   a=runner.execute(0,f);assert n.agrees(a,*expected(f)),(i,f,a,expected(f));report['cases'].append(dict(name=str(i),input=f,actual=a));save();print('canonical '+str(i)+' PASS',flush=True)
  report.update(status='pass',canonical_cases=len(report['cases']),mutation_cases=len(report['mutants']),guard_rejections=1)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({key:val for key,val in report.items() if key not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
