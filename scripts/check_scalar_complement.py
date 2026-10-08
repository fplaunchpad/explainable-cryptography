#!/usr/bin/env python3
"""Reproduce the scalar-complement 44-case/six-mutation kernel gate.

Build ExplainableCrypto.Helios.Computational.ScalarComplementMachine first.
Then run python3 scripts/check_scalar_complement.py. The actual pure controller
is reduced in the Lean kernel, preserving the full eight-port state. Expected
binary words and q-e are generated independently in Python. The six actual
instruction mutations precede canonical cases; seeds are 118,606,20260914.
The e=0 counterexample excludes interpreting q-e as canonical ZMod negation.

No empirical aggregate-charge check is claimed: the separate general charged
proof derives that bound from the executed controller's local costs.
--generate-only creates the exact fixtures without executing Lean. Reports go
to tmp/concrete-helios/reproduction, preserving the historical passed campaign.
"""
from pathlib import Path
import random,json,sys,subprocess,hashlib
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'tmp/concrete-helios/reproduction'
P.mkdir(parents=True,exist_ok=True)
seeds=[118,606,20260914]
def bits(n):
 return [(n>>i)&1 for i in range(n.bit_length())]
def word(a):return '['+','.join('true' if b else 'false' for b in a)+']'
def scalar(n):return [1]*n.bit_length()+[0]+bits(n)
def args(q,e):return word(bits(q))+' '+word(scalar(e))
def expected(q,e):return '(none,2,['+','.join(map(word,[bits(q),scalar(e),[],[],[],bits(e),[],bits(q-e)]))+'])'
header='import ExplainableCrypto.Helios.Computational.ScalarComplementMachine\n'
base='''
namespace ExplainableCrypto.Helios.Computational.ScalarComplementControls
open Turing.TM2 ScalarComplementMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def mutated (m : Nat) (l : Fin 21) :=
  if m == 1 && l == 1 then .load (fun _ => 0) (.goto (fun _ => subLabel 0))
  else if m == 2 && l.val >= 10 then
    TM2FiniteCoordinates.translate (Equiv.swap (2 : Fin 8) 5) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 3 && l == 1 then
    .peek 5 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (program l))
  else if m == 4 && l == 0 then .push 1 (fun _ => false) (program l)
  else if m == 5 && l == 2 then .push 3 (fun _ => false) (program l)
  else if m == 6 && l == 0 then .load (fun _ => 0) (.goto (fun _ => copyLabel false 0))
  else program l
private def observe (m fuel : Nat) (cfg : Config) :=
  let cfg := (TM2ReturnLink.tick (mutated m))^[fuel] cfg
  (cfg.l,cfg.var.val,List.ofFn cfg.stk)
theorem complement_is_not_canonical_negation :
    2-(0 : ZMod 2).val = 2 ∧ (-(0 : ZMod 2)).val = 0 ∧ 2-(0 : ZMod 2).val ≠ (-(0 : ZMod 2)).val := by decide +kernel
'''
mutants=[]
for m,q,e in [(1,11,3),(2,11,3),(3,2,0),(4,11,3),(5,11,3)]:
 mutants.append(f'theorem mutation_{m} : observe {m} (clock {q}) (start {args(q,e)}) ≠ {expected(q,e)} := by decide +kernel\n#print axioms mutation_{m}\n')
mutants.append(f'theorem failure_guard : observe 0 (clock 11) ({{start {args(11,3)} with var := 1}}) = (none,1,[{word(bits(11))},{word(scalar(3))},[],[],[],[],[],[]]) := by decide +kernel\n')
mutants.append(f'theorem bypassed_failure_guard : observe 6 (clock 11) ({{start {args(11,3)} with var := 1}}) = {expected(11,3)} := by decide +kernel\n#print axioms failure_guard\n#print axioms bypassed_failure_guard\n')
ending='\nend ExplainableCrypto.Helios.Computational.ScalarComplementControls\n'
(P/'ScalarComplementGateMutations.lean').write_text(header+base+''.join(mutants)+ending)
cases=[(1,0),(4,2),(8,0),(8,7),(2,0),(2,1),(3,0),(3,1),(3,2),(11,0),(11,1),(11,3),(11,10),(17,8)]
for seed in seeds:
 rng=random.Random(seed)
 for _ in range(10):
  q=rng.choice([2,3,5,7,11,13,17,31]);cases.append((q,rng.randrange(q)))
canonical=[]
for i,(q,e) in enumerate(cases):
 canonical.append(f'theorem canonical_{i} : observe 0 (clock {q}) (start {args(q,e)}) = {expected(q,e)} := by decide +kernel\n#print axioms canonical_{i}\n')
(P/'ScalarComplementGateCanonical.lean').write_text(header+base+''.join(canonical)+ending)
report=dict(status='generated',lean_executed=False,seeds=seeds,cases=cases,
 canonical_cases=len(cases),mutation_cases=6,gaveUp=0,discarded=0,
 header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/ScalarComplementMachine.lean').read_bytes()).hexdigest(),
 cost_scope='No empirical aggregate charge check; separate general charged theorem',
 counterexample='q2/e0 complement2 differs from canonical negation0')
report_path=P/'scalar-complement-gate-manifest.json'
def save():report_path.write_text(json.dumps(report,indent=2)+'\n')
save()
if '--generate-only' not in sys.argv:
 report.update(status='running',lean_executed=True);save()
 for suffix in ('Mutations','Canonical'):
  stem='ScalarComplementGate'+suffix
  with (P/(stem+'.log')).open('w') as log:
   result=subprocess.run(['lake','env','lean',str(P/(stem+'.lean'))],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
  report[suffix.lower()+'_exit_code']=result.returncode
  if result.returncode:
   report.update(status='failed',failed_batch=suffix);save()
   raise SystemExit(result.returncode)
  save()
 report['status']='pass';save()
print(json.dumps(report,indent=2))
