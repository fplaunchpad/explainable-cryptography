#!/usr/bin/env python3
"""Check the actual Lean dispatcher against independent cache/log fixtures.

Requires a built Lean project. This runs in the Lean CI job, not the Python-only
fixture job. The bounded native campaign is validation, not the general proof.
"""
from pathlib import Path
import runpy,contextlib,io,itertools,os,subprocess
ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
OUT = ROOT / 'tmp/concrete-helios'
OUT.mkdir(parents=True, exist_ok=True)
with contextlib.redirect_stdout(io.StringIO()):
    ref=runpy.run_path('scripts/check-helios-cache-hash.py')
def word(xs): return '['+','.join('true' if x else 'false' for x in xs)+']'
def words(xs): return '['+','.join(map(word,xs))+']'
def enc(n): return [True]*n.bit_length()+[False]+[bool((n>>i)&1) for i in range(n.bit_length())]
pre='''import ExplainableCrypto.Helios.Computational.CacheHashDispatch
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash w => (w,tape)
private def execute (program : Code 12 CacheHashDispatch.size 3) (k c l r tape : List Bool) : Option (List (List Bool) × List Bool) := Id.run do
  let mut cfg := CacheHashDispatch.start k c l r
  let mut coins := tape
  for _ in [:20000] do
    if cfg.l.isNone then
      return if cfg.var == 2 then some (List.ofFn cfg.stk,coins) else none
    let (out,rest) := (simulateQ handler (step program cfg)).run coins
    cfg := out.1
    coins := rest
  return none
private def fixtures : List ((List Bool × List Bool × List Bool × List Bool × List Bool) × (List (List Bool) × List Bool)) := [
'''
rows=[]
for q,slack,variant,k,log in itertools.product([1,3,11],[0,2],range(3),[[],[False],[True,False]],[[],[[True,False]]]):
    entries=[[],[([], min(1,q-1))],[([False],min(2,q-1)),([True,False],0)]][variant]
    for tape in [[False]*8,[False,True,True,False,True,False,True,False],[True]*8]:
        old=next((v for key,v in entries if key==k),None)
        used=0 if old is not None else q.bit_length()+slack
        a=old if old is not None else sum(int(b)<<i for i,b in enumerate(tape[:used]))%q
        nextcache=entries if old is not None else [(k,a)]+entries
        nextlog=log if old is not None else log+[k]
        record=[True]*slack+[False]+enc(q)
        args=[k,ref['encode_cache'](entries),ref['log_append']['encode'](log),record,tape]
        expected=[[],[],[],[],[],[],[],enc(a),k,ref['encode_cache'](nextcache),ref['log_append']['encode'](nextlog),record]
        rows.append('('+ '('+','.join(map(word,args))+'),('+words(expected)+','+word(tape[used:])+'))')
post='''\n]
def main : IO Unit := do
  let mut passed := 0
  for (args,expected) in fixtures do
    let actual := execute CacheHashDispatch.code args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2
    if actual != some expected then
      throw (IO.userError s!"dispatch fixture {passed} failed: actual={actual}; expected={expected}")
    passed := passed+1
  IO.println s!"Passed {passed} actual fixed-dispatcher fixtures"
  for mutation in [:3] do
    let program : Code 12 CacheHashDispatch.size 3 := fun label =>
      if mutation == 0 && label.val == 1 then .compute (CacheHashDispatch.control 4)
      else if mutation == 1 && label.val == 9 then .compute CacheHashDispatch.success
      else if mutation == 2 && label.val == 11 then .compute (CacheHashDispatch.clear 9 11 CacheHashDispatch.success)
      else CacheHashDispatch.code label
    let mut detected := false
    let mut index := 0
    for (args,expected) in fixtures do
      let actual := execute program args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2
      if actual != some expected then
        IO.println s!"Detected mutation {mutation} at fixture {index}"
        detected := true
        break
      index := index+1
    if !detected then throw (IO.userError s!"undetected mutation {mutation}")
'''
fixture = OUT / 'DispatchFixtures.lean'
fixture.write_text(pre+',\n'.join(rows)+post)
subprocess.run(['lake','env','lean','--run',str(fixture)],check=True,timeout=300)
