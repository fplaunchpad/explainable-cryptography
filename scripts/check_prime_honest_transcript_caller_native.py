#!/usr/bin/env python3
"""Bounded raw-input gate through the actual four simulator draws.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller`,
then `python3 scripts/check_prime_honest_transcript_caller_native.py`. The checked
DEFAULT is two smaller p3/q2 records with both votes and pair coin orders, plus
the same skip-transcript and context-corruption instruction mutations. It runs
the baseline and decisive mutations before the second canonical case. Expected
ciphertext, scalar words, full private state and stream are independent.

`--larger` preserves the original p5/q2 and p23/q11 campaign exactly. Its recorded
q11 attempt did not pass: it reached the 300-second host response timeout after
the q2 case passed. The earlier 90-second timeout and inspect.getsource startup
failure also remain recorded. The default small campaign is separate evidence;
it does not retrospectively pass the larger one or weaken the general theorem.

Reuses the native original-step loop and checked identity adapters. The raw
word is the only initial input port; no host initializer computes its state.
Full state, coin/hash counts, remaining stream, and unchanged independent
machine tick/charge caps are checked. The 300-second HOST allowance is not a
protocol bound. Both q2 nonces are necessarily one; coin-order coverage is not
a claim of distinct q2 nonce values. No complete constructor or secrecy claim.

`--generate-only` writes the production-import driver without executing Lean.
Artifacts use tmp/concrete-helios/reproduction and Reproduction driver names.
Default and larger reports have separate filenames. Relocation does not rerun
the historical native campaigns.
"""
import json,hashlib,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction'
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_transcript_draws_native as f
import check_prime_honest_ciphertext_kernel as b
def bounds(c):
 a,d=f.bounds(c);x,y=b.bounds(c);return a+x,d+y
BASE=f.BASE.replace('PrimeTranscriptDrawControls','PrimeHonestTranscriptCallerControls').replace('open PrimeTranscriptDraws','open PrimeHonestTranscriptCaller')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == drawLabel (PrimeTranscriptDraws.sampleLabel 0 0) then
    .compute (.load (fun _ => 2) .halt)
  else if m == 2 && l == drawLabel (PrimeTranscriptDraws.sampleLabel 0 0) then
    match code l with
    | .compute t => .compute (.push 14 (fun _ => false) t)
    | c => c
  else code l
'''
def driver_source():
 driver=f.n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeHonestTranscriptCallerControls')
 driver=driver.replace('let mut cfg : Config := ⟨some 0,⟨p[2]!.toNat! % 3,by omega⟩,fun n => words[n.val]!⟩','let mut cfg : Config := start (inputWord p[4]!)')
 # The shared input format is retained, but actual initialization consumes only raw input.
 driver=driver.replace('    let words := (p.drop 4).map inputWord\n','')
 return 'import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller\n'+f.n.NATIVE_SNAPSHOT+BASE+MUT+driver
def larger_main():
 source=driver_source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeHonestTranscriptCallerNativeGenerated.lean';path.write_text(source)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest()),indent=2));return
 report=dict(status='running',canonical_cases=0,mutants=[],cases=[],discarded=0,gaveUp=0,driver_sha256=hashlib.sha256(source.encode()).hexdigest());path=OUT/'prime-honest-transcript-caller-larger-native.json';r=None
 try:
  r=f.n.GateRunner(source,'PrimeHonestTranscriptCallerNativeReproduction',bounds=bounds,host_timeout=300)
  fixtures=[f.make(p=5,q=2,g=4,pk=1,words=['00']*4),f.make(words=['1111','0010','0000','1011'],order=True,vote=True)]
  for i,c in enumerate(fixtures):
   ws,left,coins=f.expected(c);paircoins=2*((c['q']-1).bit_length()+c['slack']);raw=dict(c,reached=[c['raw']]+['']*22,fresh_tape=c['tape'][:-3]+''.join(c['challenge_words'])+'101')
   a=r.execute(0,raw);assert f.n.agrees(a,ws,left,paircoins+coins),(i,c,a,ws,left,paircoins+coins)
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;print('raw canonical',i,'PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  c=fixtures[1];ws,left,coins=f.expected(c);paircoins=2*((c['q']-1).bit_length()+c['slack']);raw=dict(c,reached=[c['raw']]+['']*22,fresh_tape=c['tape'][:-3]+''.join(c['challenge_words'])+'101')
  for m,name in [(1,'skipped_transcript'),(2,'corrupted_context_at_transcript_entry')]:
   expected=c['reached'].copy() if m==1 else ws.copy();remaining=''.join(c['challenge_words'])+'101' if m==1 else left;count=paircoins if m==1 else paircoins+coins
   if m==2:expected[14]='0'+expected[14]
   a=r.execute(m,raw);assert f.n.agrees(a,expected,remaining,count),(name,a,expected,remaining,count)
   assert not f.n.agrees(a,ws,left,paircoins+coins)
   report['mutants'].append(dict(name=name,actual=a));print('detected',name,flush=True)
  report.update(status='pass',mutation_cases=2)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  path.write_text(json.dumps(report,indent=2)+'\n')
 print({k:v for k,v in report.items() if k not in ('cases','mutants')},flush=True)
def small_fixtures():
 return [f.make(p=3,q=2,g=2,pk=1,words=['00','10','01','11'],vote=True,order=False,saved=''),f.make(p=3,q=2,g=2,pk=1,words=['11','01','10','00'],vote=False,order=True,saved='')]

def small_main():
 source=driver_source();report=dict(status='running',canonical_cases=0,mutants=[],cases=[],discarded=0,gaveUp=0,host_timeout_seconds=300,scope='two smaller p3/q2 raw fixtures, both votes and pair coin orders; earlier q11 attempt remains unpassed',driver_sha256=hashlib.sha256(source.encode()).hexdigest())
 path=OUT/'prime-honest-transcript-caller-small-native.json';runner=None
 def raw(c):return dict(c,reached=[c['raw']]+['']*22,fresh_tape=c['tape'][:-3]+''.join(c['challenge_words'])+'101')
 def wanted(c):
  ws,left,coins=f.expected(c);return ws,left,2*((c['q']-1).bit_length()+c['slack'])+coins
 try:
  runner=f.n.GateRunner(source,'PrimeHonestTranscriptCallerSmallNativeReproduction',bounds=bounds,host_timeout=300)
  cases=small_fixtures();c=cases[0];ws,left,coins=wanted(c);actual=runner.execute(0,raw(c));assert f.n.agrees(actual,ws,left,coins),(c,actual,ws,left,coins)
  report['cases'].append(dict(input=c,actual=actual));report['canonical_cases']=1;print('small raw baseline PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  for m,name in [(1,'skipped_transcript'),(2,'corrupted_context_at_transcript_entry')]:
   expected=c['reached'].copy() if m==1 else ws.copy();remaining=''.join(c['challenge_words'])+'101' if m==1 else left;count=2*((c['q']-1).bit_length()+c['slack']) if m==1 else coins
   if m==2:expected[14]='0'+expected[14]
   actual=runner.execute(m,raw(c));assert f.n.agrees(actual,expected,remaining,count),(name,c,actual,expected,remaining,count)
   assert not f.n.agrees(actual,ws,left,coins),(name,'insensitive')
   report['mutants'].append(dict(name=name,input=c,actual=actual));print('detected '+name,flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  c=cases[1];ws,left,coins=wanted(c);actual=runner.execute(0,raw(c));assert f.n.agrees(actual,ws,left,coins),(c,actual,ws,left,coins)
  report['cases'].append(dict(input=c,actual=actual));report.update(status='pass',canonical_cases=2,mutation_cases=2);print('small raw reversed order/false vote PASS',flush=True)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  path.write_text(json.dumps(report,indent=2)+'\n')
 print({k:v for k,v in report.items() if k not in ('cases','mutants')},flush=True)

def main():
 if '--larger' in sys.argv or '--generate-only' in sys.argv:
  larger_main()
 else:
  small_main()
if __name__=='__main__':main()
