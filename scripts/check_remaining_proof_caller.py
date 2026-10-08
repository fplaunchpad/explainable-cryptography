#!/usr/bin/env python3
"""One raw p3/q2 three-request integration, two instruction controls.

Build PrimeRemainingProofCaller, then run this script. The same complete
request code runs p1 and total after p0 raw execution. --generate-only writes
the production-import driver without running Lean.
Uses direct code lookup and the existing original-step runner. Full58 state,
26 coin calls, no hashes, residual101 and component-sum caps are independent.
No random campaign or submission continuation is claimed.
"""
import hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_proof_request as req
import check_prime_honest_transcript_caller_native as rawdraw
import check_programmed_state_input as extraction
import check_proof_request_reentry as reentry
from check_cache_request_input import fields_encode as F,nat_encode as U
n=req.prefix.f.n;bits=req.prefix.bits;OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeRemainingProofCaller.lean'
BASE=req.BASE.replace('PrimeProofRequestGate','PrimeRemainingProofCallerGate').replace('open PrimeProofRequest','open PrimeRemainingProofCaller')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 58 size 3 :=
  if m == 1 && l == prepareTotalLabel 1 then .compute (.load (fun _ => 2) .halt)
  else if m == 2 && l == p1Label (PrimeProofRequest.programLabel 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ =>
      p1Label (PrimeProofRequest.outputLabel (PrimeProgramOutputMachine.natLabel 0 0)))))
  else code l
'''
P1=list(range(50));TOTAL=list(range(50))
for k,v in {0:55,17:54,18:51,20:50,48:52}.items():P1[k]=v
for k,v in {0:57,17:56,18:51,20:50,48:53}.items():TOTAL[k]=v

def fixture():
 saved=F([F(['0',F(['0','0'])]),'0'])
 c=rawdraw.f.make(p=3,q=2,g=2,pk=1,words=['00']*4,vote=True,order=False,saved=saved)
 c['draw_reached']=c['reached'].copy()
 c.update(initial_mem=0,fresh_tape=c['tape'][:-3]+'00'*12+'101',reached=[c['raw']]+['']*57)
 return c

def program(ws,entries,history):
 key=ws[43];occupied=any(k==key for k,v in entries)
 if not occupied:entries=[(key,0)]+entries
 history=[req.output.statement([bits_value(ws[j]) for j in (16,15,17,0)])]+history
 ws[44]=F([F([k,U(v)]) for k,v in entries]);ws[46]=str(int(ws[46]=='1' or occupied));ws[47]=F(history)
 return ws,entries,history

def bits_value(w):return sum(int(b)<<i for i,b in enumerate(w))

def complete(c,ws,nonce,vote,entries,history,skip=False):
 kwargs=dict(c,n=nonce,vote=vote,reached=ws,alpha=pow(c['g'],nonce,c['p']),beta=pow(c['pk'],nonce,c['p'])*(c['g'] if vote else 1)%c['p'],c=0,e=0,z0=0,z1=0)
 ws,_,_=req.prefix.expected(kwargs)
 ws,_,_=req.suffix.expected(dict(kwargs,reached=ws))
 if not skip:ws,entries,history=program(ws,entries,history)
 ws,_,_=req.output.expected(dict(reached=ws))
 return ws,entries,history

def states(c,m=0):
 ws=rawdraw.f.expected(dict(c,reached=c['draw_reached']))[0]+['']*27
 ws[44:48]=['0','0','0','0']
 # p0 draw state is already supplied by the independent raw initializer oracle.
 ws,es,hs=complete(c,ws,1,True,[],[])
 old0=ws+['']*8
 w=old0.copy()
 for j in reentry.CLEAR:w[j]=''
 w[50]=U(1);w[51]='0'
 local=[w[j] for j in P1]
 local,es,hs=complete(c,local,1,False,es,hs,skip=m==2)
 for j,v in zip(P1,local):w[j]=v
 old1=w.copy()
 if m==1:return old0,old1,old1
 for j in reentry.CLEAR:w[j]=''
 w[50]=U(0);w[51]='1'
 local=[w[j] for j in TOTAL]
 local,es,hs=complete(c,local,0,True,es,hs)
 for j,v in zip(TOTAL,local):w[j]=v
 return old0,old1,w

def program_bounds(c,N):
 p,q=c['p'],c['q'];G=lambda v:2*(v-1).bit_length()+1
 key=9+8*(2*G(p).bit_length()+1+G(p));I=req.ins.insertion_cost(N,N,p,q);H=1+3*N+key+G(q)
 prep=3*N+4;core=I+3*(H+I*req.ins.A)+5
 ht,hc=req.hist.bounds(dict(p=p,reached=['']*47+['0'*N]))
 return prep+core+ht,32*(prep+core)+hc

def caps(c):
 old0,old1,_=states(c);N=len(c['raw'])
 a,b=rawdraw.bounds(c);x,y=req.suffix.bounds(c);a+=x;b+=y
 x,y=extraction.bounds(dict(reached=['']*14+[c['raw']]));a+=x;b+=y
 x,y=program_bounds(c,N);a+=x;b+=y
 x,y=req.output.bounds(dict(p=3,q=2,N=N));a+=x;b+=y
 pieces=[dict(kind='p0',ticks=a,charge=b)]
 for index,old in enumerate((old0,old1)):
  M=max(map(len,old));x,y=reentry.bounds(dict(q=2,N=M));a+=x;b+=y
  pieces.append(dict(kind='reentry',N=M,ticks=x,charge=y))
  inp=max(len(old[44]),len(old[45]),len(old[47]));out=index+1
  x,y=req.prefix.bounds(c);u,v=req.suffix.bounds(c);x+=u;y+=v
  u,v=program_bounds(c,inp);x+=u;y+=v
  u,v=req.output.bounds(dict(p=3,q=2,N=out));x+=u;y+=v
  a+=x;b+=y;pieces.append(dict(kind='request',inputN=inp,outputN=out,ticks=x,charge=y))
 return a,b,pieces

def bounds(c):return caps(c)[:2]
def expected(c,m=0):return states(c,m)[2],('00'*4+'101') if m==1 else '101',18 if m==1 else 26

def source():
 c=fixture();T,C,pieces=caps(c)
 # The numeric envelope is independently computed, then checked against the
 # existing component cap declarations, without executing a theorem as oracle.
 raw='['+','.join('true' if b=='1' else 'false' for b in c['raw'])+']'
 tick=f'PrimeProgramOutputCaller.clock {raw} 0 3 2'
 cost=f'PrimeProgramOutputCaller.cost {raw} 0 3 2'
 for z in pieces[1:]:
  if z['kind']=='reentry':tick+=f"+PrimeProofRequestReentry.clock 2 {z['N']}";cost+=f"+PrimeProofRequestReentry.cost 2 {z['N']}"
  else:
   tick+=f"+PrimeRequestDraws.clock 0 3 2+PrimeProofRequest.tailClock 3 2 {z['inputN']} {z['outputN']}"
   cost+=f"+PrimeRequestDraws.cost 0 3 2+PrimeProofRequest.tailCost 3 2 {z['inputN']} {z['outputN']}"
 checks=f'\nexample : {tick} = {T} := by decide +kernel\nexample : {cost} = {C} := by decide +kernel\n'
 d=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeRemainingProofCallerGate').replace('let stepCode := routingProgramTable (mutated m)','let stepCode := mutated m')
 d=d.replace('let mut cfg : Config := ⟨some 0,⟨p[2]!.toNat! % 3,by omega⟩,fun n => words[n.val]!⟩','let mut cfg : Config := start (inputWord p[4]!)').replace('    let words := (p.drop 4).map inputWord\n','')
 return 'import ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller\n'+n.NATIVE_SNAPSHOT+BASE+checks+MUT+d

class ExactRunner(req.ExactRunner):bounds=staticmethod(bounds)
def main():
 src=source()
 if '--generate-only' in sys.argv:
  p=OUT/'PrimeRemainingProofCallerNativeGenerated.lean';p.write_text(src);print(p);return
 c=fixture();T,C,pieces=caps(c)
 report=dict(status='running',scope='one raw p3/q2 zero-sum three-request constructor prefix, two controls',code_lookup='direct',host_timeout_seconds=300,canonical_cases=0,mutation_cases=0,seeds=[],discarded=0,gaveUp=0,header_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),original_ticks=T,original_charge=C,components=pieces,cases=[],mutants=[])
 path=OUT/'remaining-proof-caller-native.json';runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  runner=ExactRunner(src,'PrimeRemainingProofCallerNativeReproduction')
  for m,name in [(0,'original'),(1,'broken_total_return'),(2,'stale_state_skips_p1_program')]:
   a=runner.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,a,want)
   if m:
    assert not n.agrees(a,*expected(c)),('insensitive',name)
    report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1
   else:report['cases'].append(dict(input=c,actual=a,independent_expected=want));report['canonical_cases']+=1
   save();print(name+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants')},indent=2),flush=True)
if __name__=='__main__':main()
