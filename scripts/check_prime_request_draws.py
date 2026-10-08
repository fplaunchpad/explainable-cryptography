#!/usr/bin/env python3
"""Gate existing 966-label code at resident entry 99, without raw initialization.

Build PrimeHonestTranscriptCaller, then run this script. Six independent
full-state fixtures include nonce zero, both votes and three fixed seeds.
Four actual instruction mutations check nonce routing, fresh coins, context
and entry guard. Every trace must obey the unchanged request clock and charge.
The 300s host allowance is separate. --generate-only does not execute Lean.
"""
import hashlib,json,random,select,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_transcript_draws_native as f
from check_cache_request_input import Runner,nat_encode
OUT=ROOT/'tmp/concrete-helios/reproduction'
OUT.mkdir(parents=True,exist_ok=True)
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeHonestTranscriptCaller.lean'
SEEDS=(118,606,20260914)
bits=f.k.bits
BASE=f.BASE.replace('PrimeTranscriptDrawControls','PrimeRequestDrawsGate').replace('open PrimeTranscriptDraws','open PrimeHonestTranscriptCaller')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && 99 <= l.val && l.val < 106 then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate
        (Equiv.swap (20 : Fin 23) 21) (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 2 then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | c => c
  else if m == 3 && l.val == 99 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | c => c
  else if m == 4 && l.val == 99 then
    match code l with
    | .compute s => .compute (.load (fun _ => 2) s)
    | c => c
  else code l
'''
def driver_source():
 d=f.n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeRequestDrawsGate').replace('let mut cfg : Config := ⟨some 0,','let mut cfg : Config := ⟨some 99,')
 return 'import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller\n'+f.n.NATIVE_SNAPSHOT+BASE+MUT+d

def bounds(c):
 p,q=c['p'],c['q'];W=p.bit_length();L=(q-1).bit_length()
 mul=9*W+11+W*(34*W+38)
 power=3*L+5+L*(2*mul+12*W+16)
 enc=2*power+mul+15*W+20;route=7*L+9
 dt,dc=f.bounds(c)
 return route+1+enc+dt,6*route+3+32*enc+dc

def make(n=0,vote=False,slack=0,words=None):
 p,q,g,pk=7,3,2,4;W=q.bit_length()+slack
 if words is None:words=['11','10','01','00']
 assert len(words)==4 and all(len(w)==W for w in words)
 ws=['']*23
 for k,v in {6:bits(p),14:'101',15:bits(pk),16:bits(g),18:str(int(vote)),19:'1'*slack+'0'+nat_encode(q),20:nat_encode(n),21:nat_encode(2),22:bits(q-1)}.items():ws[k]=v
 return dict(p=p,q=q,g=g,pk=pk,n=n,vote=vote,slack=slack,challenge_words=words,reached=ws,fresh_tape=''.join(words)+'101',initial_mem=2)

def expected(c,n=None,fixed=False):
 n=c['n'] if n is None else n;ws=c['reached'].copy()
 ws[0]=bits(pow(c['pk'],n,c['p'])*(c['g'] if c['vote'] else 1)%c['p'])
 ws[17]=bits(pow(c['g'],n,c['p']));ws[13]=bits(n);ws[2]=bits(c['q'])
 for k,w in zip((10,11,12,7),c['challenge_words']):
  value=0 if fixed else sum(int(b)<<i for i,b in enumerate(w))%c['q']
  ws[k]=nat_encode(value)
 return ws,c['fresh_tape'] if fixed else '101',0 if fixed else sum(map(len,c['challenge_words']))

class ExactRunner(Runner):
 def execute(self,m,c):
  fuel,cap=bounds(c)
  fields=[str(m),c['fresh_tape'] or '-',str(c['initial_mem']),str(fuel)]+[w or '-' for w in c['reached']]
  self.process.stdin.write(' '.join(fields)+'\n');self.process.stdin.flush()
  if not select.select([self.process.stdout],[],[],300)[0]:
   self.process.kill();self.process.wait();raise TimeoutError('300s host response timeout; killed child')
  line=self.process.stdout.readline();s=line.rstrip('\n').split('|')
  if len(s)!=8:raise RuntimeError((line,self.process.poll()))
  a=dict(halted=s[0]=='halt',memory=int(s[1]),steps=int(s[2]),charge=int(s[3]),coins=int(s[4]),hashes=int(s[5]),words=s[6].split('/'),remaining=s[7],fuel=fuel,bound=cap)
  assert a['steps']<=fuel and a['charge']<=cap,('original_caps',c,a)
  return a

def main():
 source=driver_source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeRequestDrawsNativeGenerated.lean';path.write_text(source);print(path);return
 report=dict(status='running',entry=99,seeds=SEEDS,canonical_cases=0,mutation_cases=0,discarded=0,gaveUp=0,cases=[],mutants=[],header_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(source.encode()).hexdigest(),host_timeout_seconds=300)
 path=OUT/'prime-request-draws-native.json';runner=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 try:
  runner=ExactRunner(source,'PrimeRequestDrawsNativeReproduction')
  cases=[make(),make(vote=True),make(n=1,vote=True)]
  for seed in SEEDS:
   r=random.Random(seed);slack=r.randrange(2);W=2+slack
   cases.append(make(n=r.randrange(3),vote=bool(r.randrange(2)),slack=slack,words=[''.join(r.choice('01') for _ in range(W)) for _ in range(4)]))
  c=cases[0];a=runner.execute(0,c);assert f.n.agrees(a,*expected(c)),(c,a,expected(c))
  report['cases'].append(dict(input=c,actual=a));report['canonical_cases']=1;save();print('resident entry99 n0 false baseline PASS',flush=True)
  for m,name in [(1,'stale_nonce_source'),(2,'fixed_fresh_coins'),(3,'corrupted_context'),(4,'bypassed_success_guard')]:
   c=cases[0].copy();wanted=expected(c)
   if m==1:wanted=expected(c,n=2)
   elif m==2:wanted=expected(c,fixed=True)
   elif m==3:wanted[0][14]='0'+wanted[0][14]
   else:
    c['initial_mem']=1
    a=runner.execute(0,c);assert f.n.agrees(a,c['reached'],c['fresh_tape'],0,1),(c,a)
    report['guard']=dict(input=c,actual=a)
   a=runner.execute(m,c);assert f.n.agrees(a,*wanted),(name,c,a,wanted)
   baseline=(c['reached'],c['fresh_tape'],0,1) if m==4 else (*expected(c),2)
   assert not f.n.agrees(a,*baseline),(name,'insensitive')
   report['mutants'].append(dict(name=name,input=c,actual=a));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  for i,c in enumerate(cases[1:],1):
   a=runner.execute(0,c);assert f.n.agrees(a,*expected(c)),(i,c,a,expected(c))
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print('canonical '+str(i)+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if runner is None else runner.process.poll());raise
 finally:
  if runner:runner.close();report['final_child_returncode']=runner.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard')},indent=2),flush=True)
if __name__=='__main__':main()
