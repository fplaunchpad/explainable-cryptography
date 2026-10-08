#!/usr/bin/env python3
"""Bounded original-code sticky programmed insertion gate.

Build CacheProgrammedInsertMachine, then run this script. Nine complete-state
canonical fixtures use independent Python cache encodings, including all four
sticky-flag/freshness combinations, agreeing occupied values and retained tails.
Eleven actual code mutations and three rejection fixtures test cleanup, retention,
collision policy and singleton/entry guards. Seeds118,606,20260914; zero discards.
The driver kernel-checks typed key/cache fixtures, local cost32, code accesses5,
and both pre-existing test-only snapshot/table identities. Host timeout120seconds
is a test budget, not a protocol cost theorem. --generate-only emits the driver.
Historical evidence remains under tmp/concrete-helios; reproduction has its own
output directory. No general computational secrecy claim follows from this gate.
"""
from pathlib import Path
import sys,json,hashlib,copy,random
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_honest_transcript_native as n
A=5 # Source code-access constant; kernel-certified against unchanged insertCode in driver.
def bits(x):return ''.join(str(x>>i&1) for i in range(x.bit_length()))
def nat(x):return '1'*x.bit_length()+'0'+bits(x)
def fields(xs):return nat(len(xs))+''.join(nat(len(x))+x for x in xs)
def key(xs):return fields([nat(x) for x in xs])
def cache(es):return fields([fields([k,nat(v)]) for k,v in es])
def lw(w):return '['+','.join('true' if b=='1' else 'false' for b in w)+']'
K=key([2,1,2,1,1,2,2,1]);OTHER=key([1,2,2,1,1,2,2,1])
def make(name,es,bad=False,proposed=0,keyword=K,live='10110',history='011101'):
 c=cache(es);ws=[c,'','','','','','1' if bad else '0',nat(proposed),keyword,'',live,history]
 occupied=any(k==keyword for k,v in es);out=cache(es if occupied else [(keyword,proposed)]+es)
 expected=['','','','','','','1' if bad or occupied else '0',nat(proposed),keyword,out,live,history]
 return dict(name=name,entries=es,bad=bad,proposed=proposed,reached=ws,expected=expected,initial_mem=2,fresh_tape='101')
def fixtures():
 fs=[make('fresh_false',[],False),make('fresh_true',[],True),make('occupied_false',[(K,1)],False),make('occupied_true',[(K,1)],True),make('occupied_agreeing',[(K,1)],False,1),make('occupied_retained_tail',[(K,1),(OTHER,0)],False)]
 for seed in [118,606,20260914]:
  r=random.Random(seed);kw=key([r.choice([1,2]) for _ in range(8)]);fs.append(make('seed_'+str(seed),[(OTHER,0)],bool(r.getrandbits(1)),r.randrange(2),kw,live=bits(seed),history=bits(seed+1)))
 return fs
def insertion_cost(N,W,p=3,q=2):
 size=int.bit_length;G=lambda p:2*size(p-1)+1;K=9+8*(2*size(G(p))+1+G(p));Aq=G(q);E=5+2*size(K)+1+K+2*size(Aq)+1+Aq
 FW=lambda n:n*(2*size(n)+5)+3*size(n)+5
 entry=3*size(K)+3*size(Aq)+26+K*(2*size(K)+4)+Aq*(2*size(Aq)+3)+2*K
 field=3*size(E)+7+E*(2*size(E)+3)
 iteration=field+entry+Aq+2*size(N)+6
 builder=5*size(N)+3*size(N+1)+2*Aq+2*K+FW(Aq)+FW(K)+FW(E)+21
 return 2*W+3*size(N)+N*iteration+9+builder
def bounds(c):
 I=insertion_cost(len(c['entries']),len(c['reached'][0]));H=1+sum(len(c['reached'][i]) for i in [0,7,8,10,11]);T=I+3*(H+I*A)+5;return T,32*T
BASE=n.k.BASE.split('private def replaceRecord')[0].replace('PrimeHonestTranscriptControls','CacheProgrammedInsertGate').replace('open PrimeHonestTranscriptMachine','open CacheProgrammedInsertMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 12 size 3 :=
  if m == 1 && l == 1 then .compute (.load (fun _ => 2) (program l))
  else if m == 2 && l == 1 then .compute (.pop 6 (fun v _ => v) (.push 6 (fun _ => false) (program l)))
  else if m == 3 && l == 3 then .compute (.load (fun _ => 0) (.goto (fun _ => 4)))
  else if m == 4 && l == 2 then .compute (.load (fun _ => 0) (.goto (fun _ => 3)))
  else if m == 5 && l == 4 then .compute (.load (fun _ => 2) .halt)
  else if (m == 6 || m == 7 || m == 8) && l == 1 then
    .compute (.push (if m == 6 then 8 else if m == 7 then 10 else 11) (fun _ => false) (program l))
  else if m == 9 && l == 0 then .compute (.load (fun _ => 0) (.goto (fun _ => insertEntry)))
  else if m == 10 && l == 1 then .compute (.load (fun _ => 0) (.goto (fun _ => 2)))
  else if m == 11 && l == 0 then .compute (.load (fun _ => 2) (.goto (fun _ => 1)))
  else code l
'''
def typed_controls():
 return r'''private def coord (n : Nat) (h : (n : ZMod 3)^2 = 1) : PrimeGroup 3 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (n : ZMod 3) h)
private def literalKey : BallotForkPoint (PrimeGroup 3 2) :=
  (⟨coord 2 (by decide),coord 1 (by decide),coord 2 (by decide),coord 1 (by decide)⟩,
   (coord 1 (by decide),coord 2 (by decide)),(coord 2 (by decide),coord 1 (by decide)))
''' + f'''example : (ballotKeyBitCodec 3 2).encode literalKey = {lw(K)} := by decide +kernel
example : (ballotCacheBitCodec 3 2).encode
  ((∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2)).insert literalKey 1) = {lw(cache([(K,1)]))} := by decide +kernel
example : ∀ l, localCost (program l) ≤ 32 := by decide +kernel
'''
def source():
 header='import ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine\n'
 return header+n.NATIVE_SNAPSHOT+BASE+f'example : TM2TapeRuns.codeAccesses CacheRoutineCode.insertCode = {A} := by decide +kernel\n'+typed_controls()+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','CacheProgrammedInsertGate')
def good(a,c):return n.agrees(a,c['expected'],'101',0)
def main():
 assert A>0
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'CacheProgrammedInsertNativeGenerated.lean';path.write_text(src);print(path);return
 report=dict(status='running',canonical_cases=[],mutants=[],rejections=[],seeds=[118,606,20260914],discards=0,gaveUp=0,header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/CacheProgrammedInsertMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest());r=None;path=OUT/'cache-programmed-insert-native.json'
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'CacheProgrammedInsertNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures()
  for c in fs[:6]:
   a=r.execute(0,c);assert good(a,c),(c,a);report['canonical_cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for m,idx in [(1,4),(2,1),(3,2),(4,5),(5,2),(6,0),(7,0),(8,0),(11,0)]:
   c=fs[idx];a=r.execute(m,c);T,C=bounds(c);assert a['halted'] and a['steps']<=T and a['charge']<=C and not good(a,c),(m,c,a);report['mutants'].append(dict(mutation=m,input=c,actual=a));save();print('mutant '+str(m)+' detected',flush=True)
  for j,flag in enumerate(['','10']):
   c=copy.deepcopy(fs[0]);c['reached'][6]=flag;a=r.execute(0,c);assert a['halted'] and a['memory']==1 and a['coins']==a['hashes']==0 and a['remaining']=='101',(c,a);report['rejections'].append(dict(input=c,actual=a))
   if j==1:
    a=r.execute(10,c);assert a['halted'] and a['memory']==2,(c,a);report['mutants'].append(dict(mutation=10,input=c,actual=a))
  c=copy.deepcopy(fs[0]);c['initial_mem']=1;a=r.execute(0,c);assert n.agrees(a,c['reached'],'101',0,1),(c,a);report['rejections'].append(dict(input=c,actual=a));a=r.execute(9,c);assert good(a,c),(c,a);report['mutants'].append(dict(mutation=9,input=c,actual=a));save()
  for c in fs[6:]:
   a=r.execute(0,c);assert good(a,c),(c,a);report['canonical_cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for block in ['canonical_cases','mutants','rejections']:
   for item in report[block]:
    a=item['actual'];T,C=bounds(item['input']);assert a['halted'] and a['steps']<=T and a['charge']<=C and a['coins']==a['hashes']==0 and a['remaining']=='101'
  report['original_caps_and_query_policy_postaudit']='pass for every original, mutant and rejection'
  report['status']='pass'
 except BaseException as e:report.update(status='failed',failure=repr(e));raise
 finally:
  if r:r.close();report['child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:(len(v) if isinstance(v,list) and k in ['canonical_cases','mutants','rejections'] else v) for k,v in report.items()},indent=2))
if __name__=='__main__':main()
