from pathlib import Path
import hashlib,json,random,subprocess,time
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios';OUT.mkdir(parents=True,exist_ok=True)
def bits(n):return [(n>>i)&1 for i in range(n.bit_length())]
def nat(n):return [1]*n.bit_length()+[0]+bits(n)
def word(xs):return '['+','.join('true' if x else 'false' for x in xs)+']'
def vec(xs):return '!['+','.join(word(x) for x in xs)+']'
def fw(n):return n*(2*n.bit_length()+5)+3*n.bit_length()+5
def clock(n):return 5*n.bit_length()+8+fw(2*n.bit_length()+1)
seeds=[118,606,20260914];cases=[(n,s) for n in [0,1,2,3,7,8,15,16,31,32,255,256] for s in [[],[1,0,1,1]]]
for seed in seeds:
 r=random.Random(seed)
 cases.extend((r.randrange(1024),[r.randrange(2) for _ in range(r.randrange(1,10))]) for _ in range(3))
header=(ROOT/'ExplainableCrypto/Helios/Computational/NatFieldWriterMachine.lean').read_text()
s='import ExplainableCrypto.Helios.Computational.NatFieldWriterMachine\n'+'''\nnamespace ExplainableCrypto.Helios.Computational.NatFieldWriterGate
open NatFieldWriterMachine Turing.TM2 BitOracleMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 800000
private def view (cfg : NatFieldWriterMachine.Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)
private def changed (m : Nat) (l : Fin 21) :=
  if m == 1 && l == 0 then Stmt.load (fun _ => 0) (.goto (fun _ => prefixLabel 5))
  else if m == 2 && l == 2 then .load (fun _ => 2) .halt
  else if m == 3 && l == 2 then .push 1 (fun _ => false) (program l)
  else if m == 4 && l == 2 then .push 0 (fun _ => false) (program l)
  else if m == 5 && l == 0 then .load (fun _ => 0) (.goto (fun _ => copyLabel 0))
  else program l
'''
for i,(n,suffix) in enumerate(cases):
 out=nat(len(nat(n)))+nat(n)+suffix
 expected=vec([bits(n),out,[],[],[],[],[]])
 s+=f'example : view (tick^[{clock(n)}] (start {word(bits(n))} {word(suffix)})) = (none,2,List.ofFn ({expected} : Fin 7 → List Bool)) := by decide +kernel\n'
s+='example (l : Fin 21) : localCost (program l) ≤ 32 := by fin_cases l <;> decide +kernel\n'
for m in range(1,5):
 n=2;suffix=[1,0,1,1];expected=vec([bits(n),nat(len(nat(n)))+nat(n)+suffix,[],[],[],[],[]])
 s+=f'example : view ((TM2ReturnLink.tick (changed {m}))^[{clock(n)}] (start {word(bits(n))} {word(suffix)})) ≠ (none,2,List.ofFn ({expected} : Fin 7 → List Bool)) := by decide +kernel\n'
s+='''example : view (tick^[1] (⟨some 0,1,![[false,true],[true,false],[],[],[],[],[]]⟩ : NatFieldWriterMachine.Config)) =
  (none,1,List.ofFn (![[false,true],[true,false],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
'''
n=2;suffix=[1,0];expected=vec([bits(n),nat(len(nat(n)))+nat(n)+suffix,[],[],[],[],[]])
s+=f'example : view ((TM2ReturnLink.tick (changed 5))^[{clock(n)}] (⟨some 0,1,![[false,true],[true,false],[],[],[],[],[]]⟩ : NatFieldWriterMachine.Config)) = (none,2,List.ofFn ({expected} : Fin 7 → List Bool)) := by decide +kernel\n'
s+='end ExplainableCrypto.Helios.Computational.NatFieldWriterGate\n'
p=OUT/'NatFieldWriterGate.lean';p.write_text(s)
report=dict(status='running',canonical_cases=len(cases),mutation_cases=5,seeds=seeds,discarded=0,gaveUp=0,header_sha256=hashlib.sha256(header.encode()).hexdigest(),gate_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='literal full7state exact original tick at cap, zero/small/binary boundaries and seeded values through1023; independent Python encoding; five actual program mutations; entry failure control; all-label localCost32')
(OUT/'nat-field-writer-gate.json').write_text(json.dumps(report,indent=2)+'\n')
with (OUT/'nat-field-writer-kernel.log').open('w') as log:
 result=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
report.update(status='pass' if result.returncode==0 else 'failed',returncode=result.returncode)
(OUT/'nat-field-writer-gate.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));raise SystemExit(result.returncode)
