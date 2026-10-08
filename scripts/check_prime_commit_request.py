#!/usr/bin/env python3
"""Small full-state gate of unchanged existing key caller at resident entry966.

Build PrimeCommitRequestRun first. Default: one p3/q2 arbitrary-statement fixture with underflow difference,
plus skipped-A/context mutations and original guard rejection. --larger retains
the original two p7/q3 fixtures; its first case timed out at300s and is unpassed. No raw initializer, nonce sampling or fresh queries.
The default uses direct original-code lookup. --eager-table reproduces the
identity-table adapter whose p7/q3 and p3/q2 attempts hit the300s response limit.
Every actual trace obeys the unchanged suffix clock/charge; host allowance300s.
--generate-only writes the original-code identity-adapter driver, no execution.
"""
import hashlib,json,select,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_request_draws as prior
from check_cache_request_input import Runner,fields_encode,nat_encode
OUT=prior.OUT
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeCommitRequestRun.lean'
BASE=prior.BASE.replace('PrimeRequestDrawsGate','PrimeCommitRequestGate').replace('open PrimeHonestTranscriptCaller','open PrimeCommitRequest')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 48 size 3 :=
  if m == 1 && l == aLabel 0 then .compute (.load (fun _ => 2) (.goto (fun _ => bLabel 0)))
  else if m == 2 && l == aLabel 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | c => c
  else code l
'''
def source():
 d=prior.f.n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeCommitRequestGate').replace('let mut cfg : Config := ⟨some 0,','let mut cfg : Config := ⟨some (aLabel 0),')
 if '--eager-table' not in sys.argv:d=d.replace('let stepCode := routingProgramTable (mutated m)','let stepCode := mutated m')
 return 'import ExplainableCrypto.Helios.Computational.PrimeCommitRequestRun\n'+prior.f.n.NATIVE_SNAPSHOT+BASE+MUT+d

def bounds(c):
 p,q=c['p'],c['q'];P,Q,L=p.bit_length(),q.bit_length(),(q-1).bit_length()
 mul=9*P+11+P*(34*P+38)
 power=lambda w:3*w+5+w*(2*mul+12*P+16)
 K=10*L+5*Q+17+2*power(Q)+mul+22*P+13*Q+54
 diff=18*L+26*Q+47;gamma=power(L)+mul+2
 W=(p-1).bit_length();N=2*W+1
 field=5*W+8+N*(2*N.bit_length()+5)+3*N.bit_length()+5
 ticks=4*K+diff+gamma+8*field+1
 return ticks,32*ticks

def fixture(zero=False):
 c=dict(p=7,q=3,g=2,pk=4,alpha=1 if zero else 4,beta=4 if zero else 2,c=1 if zero else 0,e=1,z0=0 if zero else 1,z1=0 if zero else 2,initial_mem=2,fresh_tape='101')
 ws=['']*48
 for j,n in [(0,c['beta']),(2,3),(6,7),(15,4),(16,2),(17,c['alpha']),(22,2)]:ws[j]=prior.bits(n)
 for j,k in [(7,'z1'),(10,'c'),(11,'e'),(12,'z0')]:ws[j]=nat_encode(c[k])
 for j,w in zip((13,14,18,19,20,21,44,45,46,47),('10','101','011','1','10101','00','110','0101','11','1001')):ws[j]=w
 c['reached']=ws;return c

def small_fixture():
 c=fixture();c.update(p=3,q=2,pk=1,alpha=2,beta=1,z1=1)
 for j,v in [(0,1),(2,2),(6,3),(15,1),(17,2),(22,1)]:c['reached'][j]=prior.bits(v)
 c['reached'][7]=nat_encode(1)
 return c

def expected(c,m=0):
 p,q=c['p'],c['q'];g,pk,a,b=c['g'],c['pk'],c['alpha'],c['beta'];e,z0,z1=c['e'],c['z0'],c['z1'];d=(c['c']-e)%q
 A=pow(g,z0,p)*pow(a,q-e,p)%p;B=pow(pk,z0,p)*pow(b,q-e,p)%p
 gamma=b*pow(g,q-1,p)%p;C=pow(g,z1,p)*pow(a,q-d,p)%p;D=pow(pk,z1,p)*pow(gamma,q-d,p)%p
 if m==1:A=0
 ws=c['reached'].copy()
 for j,v in [(3,A),(38,B),(39,gamma),(40,C),(42,D)]:ws[j]=prior.bits(v)
 ws[1]=nat_encode(d);ws[43]=fields_encode([nat_encode(v) for v in (g,pk,a,b,A,B,C,D)])
 if m==2:ws[14]='0'+ws[14]
 return ws,'101',0

class ExactRunner(Runner):
 bounds=staticmethod(bounds)
 def execute(self,m,c):
  fuel,cap=self.bounds(c);fields=[str(m),c['fresh_tape'],str(c['initial_mem']),str(fuel)]+[w or '-' for w in c['reached']]
  self.process.stdin.write(' '.join(fields)+'\n');self.process.stdin.flush()
  if not select.select([self.process.stdout],[],[],300)[0]:
   self.process.kill();self.process.wait();raise TimeoutError('300s host response timeout; killed child')
  line=self.process.stdout.readline();s=line.rstrip('\n').split('|')
  if len(s)!=8:raise RuntimeError((line,self.process.poll()))
  a=dict(halted=s[0]=='halt',memory=int(s[1]),steps=int(s[2]),charge=int(s[3]),coins=int(s[4]),hashes=int(s[5]),words=s[6].split('/'),remaining=s[7],fuel=fuel,bound=cap)
  assert a['steps']<=fuel and a['charge']<=cap,('original_caps',c,a)
  return a

def main():
 src=source();larger='--larger' in sys.argv
 if '--generate-only' in sys.argv:
  p=OUT/'PrimeCommitRequestNativeGenerated.lean';p.write_text(src);print(p);return
 report=dict(status='running',code_lookup='eager_table' if '--eager-table' in sys.argv else 'direct',scope='original p7/q3 campaign, previously timed out' if larger else 'separate smallest p3/q2 fixture; original p7/q3 remains unpassed',entry=966,canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,seeds=[],cases=[],mutants=[],header_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),host_timeout_seconds=300)
 path=OUT/('prime-commit-request-'+('larger' if larger else 'small')+('-eager' if '--eager-table' in sys.argv else '-direct')+'-native.json');runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=ExactRunner(src,'PrimeCommitRequestNativeReproduction');c=fixture() if larger else small_fixture()
  a=runner.execute(0,c);assert prior.f.n.agrees(a,*expected(c)),(c,a,expected(c))
  report['cases'].append(dict(input=c,actual=a));report['canonical_cases']=1;save();print('arbitrary statement underflow baseline PASS',flush=True)
  for m,name in [(1,'skipped_first_coordinate'),(2,'corrupted_retained_context')]:
   a=runner.execute(m,c);assert prior.f.n.agrees(a,*expected(c,m)),(name,c,a,expected(c,m))
   assert not prior.f.n.agrees(a,*expected(c)),(name,'insensitive')
   report['mutants'].append(dict(name=name,input=c,actual=a));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  if larger:
   c=fixture(True);a=runner.execute(0,c);assert prior.f.n.agrees(a,*expected(c)),(c,a,expected(c))
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']=2;save();print('zero difference/response PASS',flush=True)
  c=fixture() if larger else small_fixture();c['initial_mem']=1;a=runner.execute(0,c)
  assert prior.f.n.agrees(a,c['reached'],'101',0,1),(c,a)
  report['guard']=dict(input=c,actual=a);report['status']='pass';print('original guard PASS',flush=True)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard')},indent=2),flush=True)
if __name__=='__main__':main()
