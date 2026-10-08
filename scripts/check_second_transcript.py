#!/usr/bin/env python3
"""Gate the resident second-nonce ciphertext and four transcript draws.

Expected old and new words come from integer cryptographic equations and an
independent counted-record grammar. No output is obtained from the Lean program.
Full-state observation is private proof instrumentation, not protocol leakage.
"""
from pathlib import Path
import hashlib,json,random,sys,copy
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_honest_transcript_native as n
import check_prime_transcript_draws_native as draws
k=n.k
BASE=k.BASE.split('private def replaceRecord')[0].replace('PrimeHonestTranscriptControls','PrimeSecondTranscriptControls').replace('open PrimeHonestTranscriptMachine','open PrimeSecondTranscriptMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 59 size 3 :=
  if m == 1 && 2 <= l.val && l.val < 9 then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 59) 21)
        (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 2 && l == 0 then .compute (.branch (fun v => v == 2)
    (.push 53 (fun _ => true) (.goto (fun _ => routeLabel 0)))
    (.load (fun _ => 1) .halt))
  else if (m == 3 || m == 4 || m == 5 || m == 8) && l == 1 then
    match code l with
    | .compute s => .compute (.push (if m == 3 then 14 else if m == 4 then 48 else if m == 5 then 49 else 46)
        (fun _ => false) s)
    | c => c
  else if m == 6 && l == 0 then
    match code l with
    | .compute s => .compute (.load (fun _ => 2) s)
    | c => c
  else if m == 7 && l == 1 then .compute (.load (fun _ => 2)
    (.goto (fun _ => drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))))
  else if m == 9 then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | c => c
  else code l
'''
def bits(v):return ''.join(str(v>>i&1) for i in range(v.bit_length()))
def nat(v):return '1'*v.bit_length()+'0'+bits(v)
def fields(ws):return nat(len(ws))+''.join(nat(len(w))+w for w in ws)
def pair(a,b):return fields([a,b])
def statement(g,pk,a,b):return pair(pair(nat(g),nat(pk)),pair(nat(a),nat(b)))
def make(name,p=23,q=11,g=2,pk=4,r1=3,r2=1,slack=0,vote=True,occupied=False,bad=False,words=None,kind='source-shaped'):
 width=q.bit_length()+slack
 if words is None:words=[bits(v).ljust(width,'0') for v in [0,1,q-1,q]]
 assert len(words)==4 and all(len(w)==width for w in words)
 c,e,z0,z1=[v%q for v in (2,0,4,0)];d=(c-e)%q
 a=pow(g,r1,p);b=pow(pk,r1,p)*(g if vote else 1)%p
 adjusted=b*pow(g,-1,p)%p
 A=pow(g,z0,p)*pow(a,-e,p)%p;B=pow(pk,z0,p)*pow(b,-e,p)%p
 C=pow(g,z1,p)*pow(a,-d,p)%p;D=pow(pk,z1,p)*pow(adjusted,-d,p)%p
 key=fields([nat(x) for x in [g,pk,a,b,A,B,C,D]])
 stmt=statement(g,pk,a,b);empty=fields([])
 prior=fields([pair(key,nat(c))]) if occupied else empty
 history=fields([stmt,stmt]) if occupied else empty
 live=fields([pair(key,nat((c+1)%q))])
 oldsaved=pair(pair(prior,pair(str(int(bad)),history)),live)
 record='1'*slack+'0'+nat(q)
 raw=fields([nat(p),pair(nat(g),nat(pk)),record,str(int(vote)),oldsaved])
 updated=prior if occupied else fields([pair(key,nat(c))])
 nextHistory=fields([stmt,stmt,stmt]) if occupied else fields([stmt])
 flag=str(int(bad or occupied))
 proof=pair(pair(pair(nat(A),nat(B)),pair(nat(e),nat(z0))),pair(pair(nat(C),nat(D)),pair(nat(d),nat(z1))))
 saved=pair(pair(updated,pair(flag,nextHistory)),live)
 ws=[bits(b),nat(d),bits(q),bits(A),'','',bits(p),nat(z1),'','',nat(c),nat(e),nat(z0),bits(r1),raw,bits(pk),bits(g),bits(a),str(int(vote)),record,nat(r1),nat(r2),bits(q-1)]
 ws+=['']*15+[bits(B),bits(adjusted),bits(C),'',bits(D),key,updated,live,flag,nextHistory,proof,saved]
 assert len(ws)==50
 return dict(name=name,p=p,q=q,g=g,pk=pk,r1=r1,r2=r2,slack=slack,vote=vote,kind=kind,reached=ws+['']*9,initial_mem=2,challenge_words=words,fresh_tape=''.join(words)+'101')
def expected(c,m=0):
 ws=c['reached'].copy();r=c['r1'] if m==1 else c['r2'];p=c['p'];vote=m==2
 vals=[sum(int(b)<<i for i,b in enumerate(w))%c['q'] for w in c['challenge_words']]
 if m==9:vals=[0]*4
 ws[50:]=[bits(pow(c['g'],r,p)),bits(pow(c['pk'],r,p)*(c['g'] if vote else 1)%p),bits(r),str(int(vote))]+[nat(x) for x in vals]+[bits(c['q'])]
 if m==7:ws[50]=ws[51]=''
 if m in (3,4,5,8):j={3:14,4:48,5:49,8:46}[m];ws[j]='0'+ws[j]
 return ws,c['fresh_tape'] if m==9 else '101',0 if m==9 else sum(map(len,c['challenge_words']))
def bounds(c):
 p,q=c['p'],c['q'];w=p.bit_length();nw=(q-1).bit_length()
 mul=9*w+11+w*(34*w+38)
 power=3*nw+5+nw*(2*mul+12*w+16)
 enc=2*power+mul+15*w+20;route=7*nw+9
 dt,dc=draws.bounds(c)
 return 2+route+enc+dt,6+6*route+32*enc+dc

def main():
 header=ROOT/'ExplainableCrypto/Helios/Computational/PrimeSecondTranscriptMachine.lean'
 src='import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSecondTranscriptControls')
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSecondTranscriptNativeGenerated.lean';path.write_text(src);print(path);return
 seeded_only='--seeded-only' in sys.argv
 path=OUT/('second-transcript-seeded-native.json' if seeded_only else 'second-transcript-native.json');r=None
 report=dict(status='running',scope='seeded-only' if seeded_only else 'complete',host_timeout_seconds=300,fixture_scope='source-shaped arbitrary initial typed states; zero_nonce is numeric-only',canonical_cases=[],mutants=[],rejections=[],seeds=[118,606,20260914],discarded=0,gaveUp=0,header_sha256=hashlib.sha256(header.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,want):
  assert n.agrees(a,*want),(c['name'],a,want)
  T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a)
 save()
 try:
  r=n.GateRunner(src,'PrimeSecondTranscriptNativeReproduction',bounds=bounds,host_timeout=300)
  baseline=make('distinct_second_nonce')
  if not seeded_only:
   a=r.execute(0,baseline);check(a,baseline,expected(baseline));report['canonical_cases'].append(dict(input=baseline,actual=a));save();print('distinct_second_nonce PASS',flush=True)
  names=['selected_first_nonce','wrong_component_vote','corrupted_original_raw','corrupted_first_proof','corrupted_updated_saved','bypassed_entry_guard','skipped_encryption','corrupted_sticky_flag','fixed_fresh_coins']
  for m,name in ([] if seeded_only else enumerate(names,1)):
   c=copy.deepcopy(baseline)
   if m==6:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);check(a,c,want)
   original=(c['reached'],c['fresh_tape'],0,1) if m==6 else expected(c)
   assert not n.agrees(a,*original),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));save();print(name+' PASS',flush=True)
  if not seeded_only:
   c=copy.deepcopy(baseline);c['initial_mem']=1;a=r.execute(0,c);check(a,c,(c['reached'],c['fresh_tape'],0,1));report['rejections'].append(dict(input=c,actual=a));save()
  cases=[] if seeded_only else [make('nonzero_nonces_zero_sum',p=7,q=3,g=2,pk=4,r1=1,r2=2,occupied=True),make('singleton_nonce_zero_draws',p=5,q=2,g=4,pk=1,r1=1,r2=1,words=['00']*4),make('zero_numeric_nonce',p=7,q=3,g=2,pk=4,r1=1,r2=0,kind='numeric-boundary-only'),make('sticky_and_original_false',vote=False,occupied=True,bad=True)]
  for seed in report['seeds']:
   rng=random.Random(seed);p,q,g=rng.choice([(7,3,2),(11,5,3),(23,11,2)]);slack=rng.randrange(2);width=q.bit_length()+slack
   cases.append(make('seed_'+str(seed),p=p,q=q,g=g,pk=pow(g,2,p),r1=rng.randrange(1,q),r2=rng.randrange(1,q),slack=slack,vote=bool(rng.randrange(2)),occupied=bool(rng.randrange(2)),bad=bool(rng.randrange(2)),words=[''.join(rng.choice('01') for _ in range(width)) for _ in range(4)]))
  for c in cases:
   a=r.execute(0,c);check(a,c,expected(c));report['canonical_cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:report.update(status='failed',failure_type=type(e).__name__,failure=repr(e));raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:len(v) if k in ('canonical_cases','mutants','rejections') else v for k,v in report.items()},indent=2),flush=True)
if __name__=='__main__':main()
