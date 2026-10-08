#!/usr/bin/env python3
"""Generate the independent 60-fixture caller kernel campaign.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerControls`,
then `python3 scripts/check_nonce_ciphertext_caller_kernel.py`, then
`lake env lean tmp/concrete-helios/reproduction/NonceCiphertextCallerKernelGate.lean`.
The Python command only generates fixtures/source; it never reports a Lean pass.
Imported controls retain three positives and seven actual-code mutations.
Fixture semantics, three seeds and full-state/coin observations are unchanged.
Promotion does not rerun the historical terminal kernel campaign."""
import runpy,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'tmp/concrete-helios/reproduction'
OUT.mkdir(parents=True,exist_ok=True)
d=runpy.run_path(str(ROOT/'scripts/check_nonce_ciphertext_caller.py'))
def word(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def listwords(ws):return '['+','.join(word(w) for w in ws)+']'
imports=['import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerControls']
body=[]
preamble='''
namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerKernelGate
open OracleComp OracleSpec BitOracleMachine PrimeNonceCiphertextCaller
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def checked (fuel : Nat) (g pk modulus record context : List Bool)
    (vote : Bool) (tape : List Bool) :=
  let out := (simulateQ handler (Prod.fst <$> run code fuel
    (start g pk modulus record context vote))).run (tape,0,0)
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1,out.2.2.1,out.2.2.2)
private def commandCost (l : Fin size) : Nat :=
  match code l with
  | .compute t => localCost t
  | _ => 0
theorem local_cost_32 (l : Fin size) : commandCost l ≤ 32 := by
  fin_cases l <;> decide +kernel
#print axioms local_cost_32
'''
tests=[];cases=[]
for i,c in enumerate(d['fixtures']()):
 p,q,g,pk,slack,vote,context,tape=c;w=p.bit_length();L=(q-1).bit_length();pairclock,paircost=d['pair_bounds'](q,slack)
 mul=9*w+11+w*(34*w+38);power=3*L+5+L*(2*mul+12*w+16);encrypt=2*power+mul+15*w+20;route=7*L+9
 fullclock=pairclock+route+1+encrypt;cost=paircost+6*route+3+32*encrypt;fuel=min(4000,fullclock)
 ws,left,coins=d['expected'](c);record='1'*slack+'0'+d['nat_encode'](q)
 tests.append(f'''theorem fixture_{i:02d} : {fuel} ≤ clock {slack} {p} {q} ∧
    checked {fuel} {word(d['bits'](g))} {word(d['bits'](pk))} {word(d['bits'](p))}
      {word(record)} {word(context)} {str(vote).lower()} {word(tape)} =
      ((none,2,{listwords(ws)}),{word(left)},{coins},0) := by decide +kernel
#print axioms fixture_{i:02d}
''')
 cases.append(dict(input=c,fuel=fuel,clock=fullclock,cost=cost,expected_words=ws,remaining_coins=left,coins=coins))
text='\n'.join(imports+body)+'\n'+preamble+'\n'.join(tests)+'\nend ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerKernelGate\n'
(OUT/'NonceCiphertextCallerKernelGate.lean').write_text(text)
(OUT/'nonce-ciphertext-caller-kernel-fixtures.json').write_text(json.dumps(dict(status='generated',cases=cases,seeds=d['SEEDS'],discarded=0,gaveUp=0,controls_first=10),indent=2)+'\n')
print('Generated',len(cases),'kernel fixtures with imports of 10 existing controls; full state, coins, hash absence, residual stream and clock. No Lean execution.')
