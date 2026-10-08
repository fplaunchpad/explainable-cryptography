#!/usr/bin/env python3
"""One complete resident proof-request integration case and broken-return mutant.

Build PrimeProofRequest. Uses its actual four-stage code with direct lookup,
original step and checked snapshots. A p3/q2 zero nonce with vote=true draws
four fresh scalars, computes commitments/key, updates empty resident state and
returns independently encoded proof and successor saved state. All50 words,
coin/hash counts, remaining101, and original phase-sum caps are checked.
This is one integration fixture, not a broader attacker or secrecy theorem.
--generate-only writes the driver without executing Lean.
"""
import hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_commit_request as suffix
import check_prime_request_draws as prefix
import check_cache_programmed_insert as ins
import check_programmed_history as hist
import check_program_output as output
from check_cache_request_input import fields_encode,nat_encode
OUT=suffix.OUT
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeProofRequest.lean'
BASE=suffix.BASE.replace('PrimeCommitRequestGate','PrimeProofRequestGate').replace('open PrimeCommitRequest','open PrimeProofRequest')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 50 size 3 :=
  if m == 1 && l == programLabel (PrimeProgramMachine.tailLabel 8) then
    .compute (.load (fun _ => 2) .halt)
  else code l
'''
def source():
 d=prefix.f.n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeProofRequestGate').replace('let mut cfg : Config := ⟨some 0,','let mut cfg : Config := ⟨some (drawLabel PrimeRequestDraws.entry),').replace('let stepCode := routingProgramTable (mutated m)','let stepCode := mutated m')
 checks='\nexample : PrimeRequestDraws.clock 0 3 2 + PrimeCommitRequest.clock 3 2 + PrimeProgramMachine.clock 3 2 1 + PrimeProgramOutputMachine.clock 3 2 1 = 215066 := by decide +kernel\nexample : PrimeRequestDraws.cost 0 3 2 + PrimeCommitRequest.cost 3 2 + PrimeProgramMachine.cost 3 2 1 + PrimeProgramOutputMachine.cost 3 2 1 = 6877229 := by decide +kernel\n'
 return 'import ExplainableCrypto.Helios.Computational.PrimeProofRequest\n'+prefix.f.n.NATIVE_SNAPSHOT+BASE+checks+MUT+d

def fixture():
 ws=['']*50
 for j,w in {6:'11',14:'101',15:'1',16:'01',18:'1',19:'0'+nat_encode(2),20:nat_encode(0),21:nat_encode(2),22:'1',44:'0',45:'0',46:'0',47:'0'}.items():ws[j]=w
 return dict(p=3,q=2,g=2,pk=1,n=0,vote=True,slack=0,challenge_words=['00','10','00','10'],alpha=1,beta=2,c=0,e=1,z0=0,z1=1,reached=ws,fresh_tape='00100010101',initial_mem=2,N=1)

def bounds(c):
 dt,dc=prefix.bounds(c);kt,kc=suffix.bounds(c);p,q,N=c['p'],c['q'],1
 G=lambda v:2*(v-1).bit_length()+1
 key=9+8*(2*G(p).bit_length()+1+G(p))
 I=ins.insertion_cost(N,N,p,q);H=1+3*N+key+G(q)
 prep=3*N+4;core=I+3*(H+I*ins.A)+5
 ht,hc=hist.bounds(dict(p=p,reached=['']*47+['0']))
 ot,oc=output.bounds(dict(p=p,q=q,N=1))
 return dt+kt+prep+core+ht+ot,dc+kc+32*(prep+core)+hc+oc

def expected(c,broken=False):
 drawn,_,_=prefix.expected(c)
 stage=dict(c,reached=drawn)
 ws,_,_=suffix.expected(stage)
 statement=output.statement([2,1,1,2])
 ws[44]=fields_encode([fields_encode([ws[43],nat_encode(0)])])
 ws[47]=fields_encode([statement])
 if not broken:
  ws,_,_=output.expected(dict(reached=ws))
 return ws,'101',8

class ExactRunner(suffix.ExactRunner):bounds=staticmethod(bounds)

def main():
 src=source()
 if '--generate-only' in sys.argv:
  p=OUT/'PrimeProofRequestNativeGenerated.lean';p.write_text(src);print(p);return
 report=dict(status='running',scope='one p3/q2 zero-nonce resident request and one broken program/output return',code_lookup='direct',canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,seeds=[],header_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),host_timeout_seconds=300,cases=[],mutants=[])
 path=OUT/'prime-proof-request-native.json';runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=ExactRunner(src,'PrimeProofRequestNativeReproduction');c=fixture()
  a=runner.execute(0,c);want=expected(c);assert prefix.f.n.agrees(a,*want),(c,a,want)
  report['cases'].append(dict(input=c,actual=a));report['canonical_cases']=1;save();print('complete zero-nonce request PASS',flush=True)
  a=runner.execute(1,c);want=expected(c,True);assert prefix.f.n.agrees(a,*want),(c,a,want)
  assert not prefix.f.n.agrees(a,*expected(c)),('insensitive return mutant',a)
  report['mutants'].append(dict(name='broken_program_to_output_return',input=c,actual=a));report.update(status='pass',mutation_cases=1);print('detected broken program/output return',flush=True)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
