#!/usr/bin/env python3
"""Small native gate for the actual first full-field simulator draw.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine`,
then `python3 scripts/check_prime_honest_transcript_native.py`. Eleven canonical
cases (one saved-frame regression), eight mutations and a rejecting guard case
use three fixed seeds. Full state, coin/hash counts, residual stream and
independently derived clock/charge are checked. The private vote/nonces/context
in this complete-state test observation are not public protocol outputs.

Uses existing check_cache_request_input.Runner and the checked test-only native
identity adapters in nonce_ciphertext_gate_support. Independent fixture/mutation
support is in prime_transcript_gate_fixtures. A prior concatenated-header kernel
campaign failed on interpreter memory; this validated native campaign has its
own explicit scope and is not a claim that the abandoned campaign passed.

`--generate-only` writes the production-import driver without executing Lean.
Reports and generated source go under tmp/concrete-helios/reproduction; native
Runner files have a Reproduction suffix. Historical reports stay untouched.
The 90-second host response cap is a test limit, not a protocol cost theorem."""
import hashlib,json,select,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction'
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
from check_cache_request_input import Runner
from nonce_ciphertext_gate_support import NATIVE_SNAPSHOT
import prime_transcript_gate_fixtures as k
DRIVER=r'''
private def inputWord (s : String) := if s == "-" then [] else s.toList.map (· == '1')
private def outputWord (w : List Bool) := String.ofList (w.map (fun b => if b then '1' else '0'))
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "READY"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let p := line.trimAscii.toString.splitOn " "
    let m := p[0]!.toNat!
    let stepCode := routingProgramTable (mutated m)
    let words := (p.drop 4).map inputWord
    let mut cfg : Config := ⟨some 0,⟨p[2]!.toNat! % 3,by omega⟩,fun n => words[n.val]!⟩
    let mut state := (inputWord p[1]!,0,0)
    let mut used := 0
    let mut charge := 0
    for _ in [:p[3]!.toNat!] do
      if cfg.l.isNone then break
      let (out,next) := (simulateQ handler (step stepCode cfg)).run state
      cfg := routingSnapshot out.1
      state := next
      used := used+1
      charge := charge+out.2
    output.putStrLn (String.intercalate "|" [if cfg.l.isNone then "halt" else "timeout",
      toString cfg.var.val,toString used,toString charge,toString state.2.1,
      toString state.2.2,String.intercalate "/" ((List.ofFn cfg.stk).map outputWord),outputWord state.1])
    output.flush
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptControls
def main : IO Unit := ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptControls.main
'''
class GateRunner(Runner):
 def __init__(self,driver_text,name,*,bounds=k.bounds,host_timeout=90):
  self.bounds=bounds
  self.host_timeout=host_timeout
  super().__init__(driver_text,name)
 def execute(self,m,c):
  fuel,bound=self.bounds(c)
  if m:fuel+=64;bound+=4096
  fields=[str(m),c['fresh_tape'] or '-',str(c['initial_mem']),str(fuel)]+[w or '-' for w in c['reached']]
  self.process.stdin.write(' '.join(fields)+'\n');self.process.stdin.flush()
  if not select.select([self.process.stdout],[],[],self.host_timeout)[0]:
   self.process.kill();self.process.wait();raise TimeoutError(f'{self.host_timeout}s host response timeout; process killed')
  line=self.process.stdout.readline();parts=line.rstrip('\n').split('|')
  if len(parts)!=8:raise RuntimeError(f'bad driver response {line!r}; returncode={self.process.poll()}')
  return dict(halted=parts[0]=='halt',memory=int(parts[1]),steps=int(parts[2]),charge=int(parts[3]),coins=int(parts[4]),hashes=int(parts[5]),words=parts[6].split('/'),remaining=parts[7],fuel=fuel,bound=bound)
def agrees(a,ws,rest,coins,mem=2):
 return a['halted'] and a['memory']==mem and a['words']==ws and a['remaining']==rest and a['coins']==coins and a['hashes']==0 and a['steps']<=a['fuel'] and a['charge']<=a['bound']
def driver_source():
 return 'import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine\n'+NATIVE_SNAPSHOT+k.BASE+DRIVER
def main():
 src=driver_source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeHonestTranscriptNativeGenerated.lean';path.write_text(src)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path),source_sha256=hashlib.sha256(src.encode()).hexdigest()),indent=2));return
 report=dict(status='running',seeds=k.SEEDS,discarded=0,gaveUp=0,header_sha256=hashlib.sha256(k.HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 path=OUT/'prime-honest-transcript-native.json';r=None
 try:
  r=GateRunner(src,'PrimeHonestTranscriptNativeReproduction')
  c=k.make(p=5,q=2,g=4,pk=1,challenge='00');want=k.expected(c);a=r.execute(0,c);assert agrees(a,*want),(c,a,want)
  report['minimal_zero']=dict(input=c,actual=a);print('minimal q2 zero PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  c=k.make(challenge='1011');ws,rest,coins=k.expected(c);ws[19]='0'+k.nat(10);ws[2]=k.bits(10);ws[7]=k.nat(3)
  mutations=[('wrong_nonce_modulus',1,c,ws,rest,coins,2)]
  z=k.make(p=5,q=2,g=4,pk=1,challenge='00');ws,rest,coins=k.expected(z);ws[7]=k.nat(1);mutations.append(('zero_forced_nonzero',2,z,ws,rest,coins,2))
  ws,_,_=k.expected(c);ws[7]=k.nat(0);mutations.append(('fixed_fresh_coins',3,c,ws,c['fresh_tape'],0,2))
  for m,j,name in [(4,17,'corrupted_alpha'),(5,0,'corrupted_beta'),(6,14,'corrupted_context'),(8,10,'corrupted_saved_challenge')]:
   ws,rest,coins=k.expected(c);ws[j]='0'+ws[j];mutations.append((name,m,c,ws,rest,coins,2))
  bad=k.make(challenge='1011',initial_mem=1);a=r.execute(0,bad);assert agrees(a,bad['reached'],bad['fresh_tape'],0,1),(bad,a)
  report['guard_baseline']=dict(input=bad,actual=a)
  ws,rest,coins=k.expected(bad);mutations.append(('bypassed_previous_success_guard',7,bad,ws,rest,coins,2))
  for name,m,c,ws,rest,coins,mem in mutations:
   a=r.execute(m,c);assert agrees(a,ws,rest,coins,mem),(name,c,a,ws,rest,coins)
   baseline=(c['reached'],c['fresh_tape'],0,1) if c['initial_mem'] != 2 else (*k.expected(c),2)
   assert not agrees(a,*baseline),(name,'insensitive mutant')
   report['mutants'].append(dict(name=name,input=c,actual=a));print('detected '+name,flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  cases=[k.make(p=5,q=2,g=4,pk=1,challenge='10',vote=False,saved=''),k.make(p=7,q=3,g=2,pk=4,challenge='11')]
  for vote in (False,True):
   for order in (False,True):cases.append(k.make(vote=vote,order=order,challenge='1111' if order else '0000'))
  cases.append(k.make(challenge='1011',extra=('10','011','1')))
  for seed in k.SEEDS:
   rng=k.random.Random(seed);p,q,g=rng.choice(((5,2,4),(7,3,2),(11,5,3),(23,11,2)));slack=rng.randrange(2)
   cases.append(k.make(p=p,q=q,g=g,pk=pow(g,2,p),slack=slack,challenge=''.join(rng.choice('01') for _ in range(q.bit_length()+slack)),vote=bool(rng.randrange(2)),order=bool(rng.randrange(2)),saved='10'))
  for i,c in enumerate(cases):
   a=r.execute(0,c);assert agrees(a,*k.expected(c)),(i,c,a,k.expected(c));report['cases'].append(dict(input=c,actual=a));print('canonical '+str(i)+' PASS',flush=True);path.write_text(json.dumps(report,indent=2)+'\n')
  report.update(status='pass',canonical_cases=1+len(cases),reached_state_cases=len(cases),saved_frame_cases=1,mutation_cases=len(mutations),guard_rejections=1)
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  path.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({a:b for a,b in report.items() if a not in ('cases','mutants','minimal_zero','guard_baseline')},indent=2),flush=True)
if __name__=='__main__':main()
