"""Independent fixtures and exact instruction mutations for transcript gates.

No expected value is read from a Lean execution. The prior ciphertext is
computed by integer exponentiation and independent encoders; new challenges
use chronological little-endian values modulo q, including zero. The abandoned
full-state kernel campaign is not part of this helper or claimed as passed.
"""
import random
from pathlib import Path
from check_prime_honest_input_kernel import fixture,bits,nat,word
from check_prime_honest_ciphertext_kernel import expected as prefix_expected
ROOT=Path(__file__).resolve().parents[1]
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeHonestTranscriptMachine.lean'
SEEDS=(118,606,20260914)
BASE = r'''
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptControls
open PrimeHonestTranscriptMachine OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def replaceRecord (s : Turing.TM2.Stmt (fun _ : Fin 23 => Bool) (Fin 48) (Fin 3)) :=
  let next := ([false,true,true,true,true,false,false,true,false,true] : List Bool).reverse.foldr
    (fun b next => Turing.TM2.Stmt.push 19 (fun _ => b) next) s
  (List.range 10).foldr (fun _ next => Turing.TM2.Stmt.pop 19 (fun v _ => v) next) next
private def mutated (m : Nat) (l : Fin 48) : Command 23 48 3 :=
  if m == 1 && l == 0 then
    match code l with
    | .compute s => .compute (replaceRecord s)
    | c => c
  else if m == 2 && l == 39 then
    match code l with
    | .compute s => .compute (.push 1 (fun _ => true) s)
    | c => c
  else if m == 3 then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | c => c
  else if m == 4 && l == 0 then
    match code l with
    | .compute s => .compute (.push 17 (fun _ => false) s)
    | c => c
  else if m == 5 && l == 0 then
    match code l with
    | .compute s => .compute (.push 0 (fun _ => false) s)
    | c => c
  else if m == 6 && l == 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | c => c
  else if m == 7 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => sampleLabel 0)))
  else if m == 8 && l == 0 then
    match code l with
    | .compute s => .compute (.push 10 (fun _ => false) s)
    | c => c
  else code l
'''

def make(p=23,q=11,g=2,pk=4,slack=0,vote=True,saved='101',order=False,challenge=None,extra=('','',''),initial_mem=2):
 c=fixture(p=p,q=q,g=g,pk=pk,slack=slack,vote=vote,saved=saved)
 nwidth=(q-1).bit_length()+slack;c['tape']=('1' if order else '0')*nwidth+('0' if order else '1')*nwidth+'101'
 reached,_,_=prefix_expected(c)
 for k,w in zip((10,11,12),extra):reached[k]=w
 width=q.bit_length()+slack
 c.update(reached=reached,challenge=('0'*width if challenge is None else challenge),extra=extra,initial_mem=initial_mem)
 assert len(c['challenge'])==width
 c['fresh_tape']=c['challenge']+'101'
 return c

def expected(c):
 ws=c['reached'].copy();n=sum(int(b)<<i for i,b in enumerate(c['challenge']))%c['q']
 ws[2]=bits(c['q']);ws[7]=nat(n)
 return ws,'101',len(c['challenge'])

def bounds(c):
 q,slack=c['q'],c['slack'];w=q.bit_length()+slack;size=q.bit_length();recordlen=slack+1+2*size+1
 prep=slack+5*size+8
 writer=3*(q-1).bit_length()+3
 scalar=(4*w+2)+(w*(8*size+13)+3)+writer
 scost=15*w+9+32*(w*(8*size+13)+3)+32*writer
 return 1+(2*recordlen+2)+(1+prep+1+scalar),3+5*(2*recordlen+2)+2+32*prep+5+scost
