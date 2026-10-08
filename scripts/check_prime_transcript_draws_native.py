#!/usr/bin/env python3
"""Small native gate for the actual four full-field simulator draws.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws`,
then `python3 scripts/check_prime_transcript_draws_native.py`. Eight canonical
cases and four actual mutations preserve the prior statement and nonce pair,
checking all 23 ports, exact coin/hash counts, residual stream and the independent
four-sample/three-save clock and charge bound. Three fixed seeds and zero-valued
samples are included. This is not the simulated commitment or full constructor.

Reuses the first-challenge driver and fixture helper. The omitted-modulus-clear
mutant is detected by a bounded live trace/additional queries; no eventual
nontermination claim is made. No native-decide axioms are introduced.

`--generate-only` writes the production-import driver without executing Lean.
New artifacts use tmp/concrete-helios/reproduction and native driver names have
a Reproduction suffix. Relocation does not rerun the historical passing campaign."""
import hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction'
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_honest_transcript_native as n
k=n.k;local_bounds=k.bounds
FOUR=ROOT/'ExplainableCrypto/Helios/Computational/PrimeTranscriptDraws.lean'
BASE=k.BASE.split('private def mutated')[0].replace('PrimeHonestTranscriptControls','PrimeTranscriptDrawControls').replace('open PrimeHonestTranscriptMachine','open PrimeTranscriptDraws')
# Drop the first-c-only fixed-record replacement helper; no evaluator changes.
BASE=BASE.split('private def replaceRecord')[0]
MUTATIONS=r'''
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == sampleLabel 1 0 then
    .compute (.load (fun _ => 2) (.goto (fun _ => saveLabel 1 0)))
  else if m == 2 && l.val >= 201 && l.val < 205 then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (7 : Fin 23) 10)
        (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 3 && l.val >= 199 && l.val < 206 then
    BitOracleReturnLink.command (saveLabel 1) (some (saveReturn 1))
      (TranscriptScalarSave.code 0 ⟨(l.val-199)%7,by omega⟩)
  else if m == 4 && (l == saveLabel 0 1 || l == saveLabel 1 1 || l == saveLabel 2 1) then
    .compute (.goto (fun _ => if l == saveLabel 0 1 then saveLabel 0 2
      else if l == saveLabel 1 1 then saveLabel 1 2 else saveLabel 2 2))
  else code l
'''
def bounds(c):
 a,b=local_bounds(c);q=c['q'];save=3*(2*(q-1).bit_length()+1)+q.bit_length()+7
 return 4*a+3*save,4*b+15*save

def make(words=None,**kw):
 c=k.make(**kw);width=c['q'].bit_length()+c['slack']
 if words is None:words=['0'*width]*4
 assert len(words)==4 and all(len(w)==width for w in words)
 c['challenge_words']=words;c['fresh_tape']=''.join(words)+'101';return c

def expected(c):
 ws=c['reached'].copy();vals=[sum(int(b)<<i for i,b in enumerate(w))%c['q'] for w in c['challenge_words']]
 ws[2]=k.bits(c['q'])
 for j,a in zip((10,11,12,7),vals):ws[j]=k.nat(a)
 return ws,'101',sum(map(len,c['challenge_words']))
def driver_source():
 header='import ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws\n'
 driver=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeTranscriptDrawControls')
 return header+n.NATIVE_SNAPSHOT+BASE+MUTATIONS+driver
def main():
 src=driver_source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeTranscriptDrawsNativeGenerated.lean';path.write_text(src)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path),source_sha256=hashlib.sha256(src.encode()).hexdigest()),indent=2));return
 report=dict(status='running',discarded=0,gaveUp=0,seeds=k.SEEDS,cases=[],mutants=[],driver_sha256=hashlib.sha256(src.encode()).hexdigest(),four_header_sha256=hashlib.sha256(FOUR.read_bytes()).hexdigest())
 path=OUT/'prime-transcript-draws-native.json';r=None
 try:
  r=n.GateRunner(src,'PrimeTranscriptDrawsNativeReproduction',bounds=bounds)
  z=make(p=5,q=2,g=4,pk=1,words=['00']*4);a=r.execute(0,z);assert n.agrees(a,*expected(z)),(z,a,expected(z));report['minimal_zero']=dict(input=z,actual=a);print('four q2 zero draws PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  c=make(words=['0000','1000','1100','0101']);baseline=expected(c)
  for m,name in [(1,'skipped_second_draw'),(2,'reused_stored_first_challenge'),(3,'wrong_save_phase'),(4,'uncleared_sampler_modulus')]:
   a=r.execute(m,c);assert not n.agrees(a,*baseline),(name,c,a,'insensitive')
   report['mutants'].append(dict(name=name,input=c,actual=a,expected_original=dict(words=baseline[0],remaining=baseline[1],coins=baseline[2])));print('detected '+name,flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  cases=[make(words=['0000','1000','1100','0101'],vote=False),make(words=['1111','0010','0000','1011'],order=True,vote=True),make(p=7,q=3,g=2,pk=4,words=['11','10','01','00'],vote=False),make(p=5,q=2,g=4,pk=1,words=['10','00','11','01'],vote=False,order=True)]
  for seed in k.SEEDS:
   rng=k.random.Random(seed);q=11 if seed%2 else 3;p,g=(23,2) if q==11 else (7,2);slack=rng.randrange(2);width=q.bit_length()+slack
   cases.append(make(p=p,q=q,g=g,pk=pow(g,2,p),slack=slack,words=[''.join(rng.choice('01') for _ in range(width)) for _ in range(4)],vote=bool(rng.randrange(2)),order=bool(rng.randrange(2)),saved='10'))
  for i,c in enumerate(cases):
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(i,c,a,expected(c));report['cases'].append(dict(input=c,actual=a));print('canonical '+str(i)+' PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  report.update(status='pass',canonical_cases=1+len(cases),mutation_cases=4)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  path.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({a:b for a,b in report.items() if a not in ('cases','mutants','minimal_zero')},indent=2),flush=True)
if __name__=='__main__':main()
