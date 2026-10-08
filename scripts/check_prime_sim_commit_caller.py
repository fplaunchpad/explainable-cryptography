#!/usr/bin/env python3
"""Bounded actual raw-input connection to the first commitment coordinate.

Build ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller, then run
`python3 scripts/check_prime_sim_commit_caller.py`. One minimal p3/q2 record
runs the original initializer, two nonce draws, first ciphertext, four full-field
scalar draws and the first commitment coordinate. A second execution of the
same raw input skips the final coordinate, and must fail the original output
comparison. All 38 ports, ten coins, no hashes, residual101 and the unchanged
independent bounds are checked. The host response allowance is300 seconds.

This gate claims no larger raw campaign. Earlier q11 raw-prefix resource
failures retain their original status. Uses the same independent encoder and
checked native identity adapters as the previously passed component gates.
--generate-only writes a production-import driver without executing Lean.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_honest_transcript_caller_native as previous
import check_prime_sim_commit as local
n=previous.f.n;k=n.k
BASE=local.BASE.replace('PrimeSimCommitControls','PrimeSimCommitCallerControls').replace('open PrimeSimCommitMachine','open PrimeSimCommitCaller')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 38 size 3 :=
  if m == 1 && l == commitLabel 0 then .compute (.load (fun _ => 2) .halt)
  else code l
'''
def source():
 driver=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimCommitCallerControls')
 driver=driver.replace('let mut cfg : Config := ⟨some 0,⟨p[2]!.toNat! % 3,by omega⟩,fun n => words[n.val]!⟩','let mut cfg : Config := start (inputWord p[4]!)').replace('    let words := (p.drop 4).map inputWord\n','')
 return 'import ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller\n'+n.NATIVE_SNAPSHOT+BASE+MUT+driver

def bounds(c):
 a,b=previous.bounds(c);x,y=local.bounds(c);return a+x,b+y

def fixture():return previous.small_fixtures()[0]
def expected(c,m=0):
 ws,left,coins=previous.f.expected(c);ws+=['']*15
 if not m:
  e,z=(sum(int(b)<<i for i,b in enumerate(c['challenge_words'][j]))%c['q'] for j in (1,2))
  alpha=sum(int(b)<<i for i,b in enumerate(ws[17]))
  ws[3]=k.bits(pow(c['g'],z,c['p'])*pow(alpha,c['q']-e,c['p'])%c['p'])
 return ws,left,2*((c['q']-1).bit_length()+c['slack'])+coins

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimCommitCallerNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 path=OUT/'prime-sim-commit-caller-native.json';runner=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,host_timeout_seconds=300,scope='one actual p3/q2 raw record, followed by skipped-commit mutation; no larger raw campaign claimed',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimCommitCaller.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=n.GateRunner(src,'PrimeSimCommitCallerNativeReproduction',bounds=bounds,host_timeout=300)
  c=fixture();raw=dict(c,reached=[c['raw']]+['']*37,fresh_tape=c['tape'][:-3]+''.join(c['challenge_words'])+'101')
  a=runner.execute(0,raw);want=expected(c);assert n.agrees(a,*want),(c,a,want)
  report['cases'].append(dict(input=c,actual=a,independent_expected=want));report['canonical_cases']=1;save();print('small raw first-coordinate PASS',flush=True)
  a=runner.execute(1,raw);want=expected(c,1);assert n.agrees(a,*want),(c,a,want)
  assert not n.agrees(a,*expected(c)),('insensitive skip-commit mutant',c,a)
  report['mutants'].append(dict(name='skipped_first_commit_coordinate',input=c,actual=a,independent_expected=want));report.update(status='pass',mutation_cases=1);save();print('detected skipped first coordinate PASS',flush=True)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
