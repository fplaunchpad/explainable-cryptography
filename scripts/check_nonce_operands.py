#!/usr/bin/env python3
"""Native predecessor-preparation fixtures and actual-code mutation gate."""
import json,random,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; OUT=ROOT/'tmp/concrete-helios'
OUT.mkdir(parents=True, exist_ok=True)
DRIVER=r'''import ExplainableCrypto.Helios.Computational.NonceOperands
open ExplainableCrypto.Helios.Computational OracleComp OracleSpec BitOracleMachine
private def handler : QueryImpl spec Id := fun r => match r with | .coin => false | .hash w => w
private def modified (mutation : Nat) : NonceOperands.Label → Turing.TM2.Stmt
    (fun _ : Fin 8 => Bool) NonceOperands.Label (Option Bool) := fun l =>
  if mutation == 1 && l == .parsed false then
    .goto (fun _ => .ready)
  else if mutation == 2 then match l with
    | .increment _ => SamplerOperands.program l
    | _ => NonceOperands.program l
  else if mutation == 3 && l == .ready then
    .push 5 (fun _ => false) (NonceOperands.program l)
  else NonceOperands.program l
private def program (mutation : Nat) : Code 8 15 3 :=
  if mutation == 0 then NonceOperands.code else fun l => .compute
    (TM2FiniteCoordinates.program (Equiv.refl _) SamplerOperands.labels BinaryModuloCode.memory
      (modified mutation) l)
private def bits (w : List Bool) := String.ofList (w.map (fun b => if b then '1' else '0'))
private def word (s : String) := if s == "-" then [] else s.toList.map (· == '1')
def main : IO Unit := do
 let input ← IO.getStdin; let output ← IO.getStdout
 output.putStrLn "READY"; output.flush
 repeat
  let line ← input.getLine
  if line.isEmpty then break
  let p := line.trimAscii.toString.splitOn " "
  let mutation := p[0]!.toNat!
  let cap := p[1]!.toNat!
  let mut cfg := SamplerOperands.present (SamplerOperands.start false (word p[2]!)
    ![word p[3]!,word p[4]!,word p[5]!])
  let mut steps := 0
  for _ in [:cap] do
   if cfg.l.isNone then break
   let out := simulateQ handler (step (program mutation) cfg)
   cfg := out.1
   steps := steps+1
  output.putStrLn (String.intercalate "|" [toString cfg.l.isNone,toString cfg.var.val,toString steps,
    String.intercalate "/" ((List.ofFn cfg.stk).map bits)])
  output.flush
'''
(OUT/'NonceOperandsNative.lean').write_text(DRIVER)
def enc(n):
 w=n.bit_length();return '1'*w+'0'+''.join(str((n>>i)&1) for i in range(w))
def case(q,s,suffix,frame):
 return dict(q=q,slack=s,raw='1'*s+'0'+enc(q)+suffix,frame=frame,
  expected=["",''.join(str(((q-1)>>i)&1) for i in range((q-1).bit_length())) if q else "",
   '1'*((q-1).bit_length()+s) if q>=2 else '1'*s,"",suffix]+frame,
  memory=0 if q>=2 else 1)
cases=[]
for q in (0,1,2,3,4,7,8,15,16,31,32,255,256,257,65536):
 for s in (0,1,7):
  for suf,f in (('', ['','','']),('011',['101','001','11010'])):
   cases.append(case(q,s,suf,f))
seeds=(118,198,20260914)
for seed in seeds:
 r=random.Random(seed)
 for _ in range(64):
  b=lambda n:''.join(r.choice('01') for _ in range(n))
  cases.append(case(r.randrange(2,2**64),r.randrange(17),b(r.randrange(9)),[b(r.randrange(9)) for _ in range(3)]))
proc=subprocess.Popen(['lake','env','lean','--run',str(OUT/'NonceOperandsNative.lean')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
startup=[]
while True:
 line=proc.stdout.readline()
 if line.strip()=='READY':break
 startup.append(line)
 if not line:raise RuntimeError(''.join(startup))
def execute(m,c):
 cap=10000
 proc.stdin.write(' '.join(map(str,[m,cap,c['raw']]+[w or '-' for w in c['frame']]))+'\n');proc.stdin.flush()
 p=proc.stdout.readline().strip().split('|')
 if len(p)!=4:raise RuntimeError(p)
 return dict(halted=p[0]=='true',memory=int(p[1]),steps=int(p[2]),words=p[3].split('/'))
def bad(c,a):return not a['halted'] or a['words']!=c['expected'] or a['memory']!=c['memory']
report=dict(cases=len(cases),seeds=seeds,per_seed=64,discarded=0,gave_up=0,mutations=[])
try:
 for m in (1,2,3):
  for i,c in enumerate(cases):
   if c['q']<2:continue
   a=execute(m,c)
   if bad(c,a):
    report['mutations'].append(dict(mutation=m,index=i,case=c,actual=a));break
  else:raise AssertionError(('undetected',m))
 maximum=0
 for i,c in enumerate(cases):
  a=execute(0,c);maximum=max(maximum,a['steps'])
  if bad(c,a):raise AssertionError((i,c,a))
  if c['q']>=2:
   cap=c['slack']+5*c['q'].bit_length()+2*(c['q']-1).bit_length()+9
   assert a['steps']<=cap,(c,a,cap)
 report.update(status='passed',maximum_steps=maximum)
 print(json.dumps(report))
finally:
 proc.stdin.close();proc.wait()
 (OUT/'nonce-operands-native-report.json').write_text(json.dumps(report,indent=2))
