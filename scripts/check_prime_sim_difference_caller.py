#!/usr/bin/env python3
"""Check the actual raw-input caller through both zero-branch commitments and canonical challenge difference.

Build ExplainableCrypto.Helios.Computational.PrimeSimDifferenceCaller, then run
python3 scripts/check_prime_sim_difference_caller.py. The bounded campaign uses
one original 73-bit p3/q2 raw record and one actual skipped-difference
mutation. Independent integer expectations cover all 39 words, both coordinates and canonical difference prefix,
ten consumed coins, zero hash queries, residual 101, and original tick/charge
caps. The per-response host allowance is 600 seconds. No larger raw campaign is
claimed; prior larger raw-prefix resource failures remain unpassed.

--generate-only writes the production-import driver without executing Lean.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_sim_commit_pair_caller as prior
n=prior.n;k=prior.k
BASE=prior.BASE.replace('PrimeSimCommitPairCallerControls','PrimeSimDifferenceCallerControls').replace('open PrimeSimCommitPairCaller','open PrimeSimDifferenceCaller')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 39 size 3 :=
  if m == 1 && l == differenceLabel 0 then .compute (.load (fun _ => 2) .halt)
  else code l
'''
def source():
 driver=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimDifferenceCallerControls')
 driver=driver.replace('let mut cfg : Config := ⟨some 0,⟨p[2]!.toNat! % 3,by omega⟩,fun n => words[n.val]!⟩','let mut cfg : Config := start (inputWord p[4]!)').replace('    let words := (p.drop 4).map inputWord\n','')
 return 'import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceCaller\n'+n.NATIVE_SNAPSHOT+BASE+MUT+driver

def bounds(c):
 a,b=prior.bounds(c);q=c['q'];x=18*(q-1).bit_length()+26*q.bit_length()+47;return a+x,b+32*x

def fixture():return prior.fixture()
def expected(c,m=0):
 ws,left,coins=prior.expected(c)
 if not m:
  challenge,e=(sum(int(b)<<i for i,b in enumerate(c['challenge_words'][j]))%c['q'] for j in (0,1))
  ws[1]=k.nat((challenge-e)%c['q'])
 return ws,left,coins

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimDifferenceCallerNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 path=OUT/'prime-sim-difference-caller-native.json';runner=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,host_timeout_seconds=600,scope='one actual p3/q2 raw record, followed by skipped-difference mutation; no larger raw campaign claimed',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimDifferenceCaller.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  runner=n.GateRunner(src,'PrimeSimDifferenceCallerNativeReproduction',bounds=bounds,host_timeout=600)
  c=fixture();raw=dict(c,reached=[c['raw']]+['']*38,fresh_tape=c['tape'][:-3]+''.join(c['challenge_words'])+'101')
  a=runner.execute(0,raw);want=expected(c);assert n.agrees(a,*want),(c,a,want)
  report['cases'].append(dict(input=c,actual=a,independent_expected=want));report['canonical_cases']=1;save();print('small raw challenge-difference PASS',flush=True)
  a=runner.execute(1,raw);want=expected(c,1);assert n.agrees(a,*want),(c,a,want)
  original_clock,original_cost=bounds(c);assert a['steps']<=original_clock and a['charge']<=original_cost,('mutant original cap exceeded',a)
  assert not n.agrees(a,*expected(c)),('insensitive skip-difference mutant',c,a)
  report['mutants'].append(dict(name='skipped_challenge_difference',input=c,actual=a,independent_expected=want));report.update(status='pass',mutation_cases=1);save();print('detected skipped challenge difference PASS',flush=True)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
