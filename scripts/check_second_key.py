#!/usr/bin/env python3
"""Gate the executed eight-field ballot-key serializer on complete 71-port states.

Requires the production PrimeSecondKeyMachine header. The seven source-shaped
fixtures retain both earlier proof state and all four fresh p1 coordinates. Reuses the existing original
step handler and kernel-proved native identity adapters. Independent integer
fixtures and the explicit flat record grammar determine every expected bit.
No full raw-caller execution or general execution theorem is claimed by this
bounded gate. --generate-only writes the driver without executing Lean.
"""
from pathlib import Path
import copy,hashlib,json,random,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_second_one_second as prior
import check_prime_sim_key as original
k=original.k
n=prior.n
BASE=original.BASE.replace('PrimeSimKeyControls','PrimeSecondKeyControls').replace('open PrimeSimKeyMachine','open PrimeSecondKeyMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 71 size 3 :=
  if m == 1 || m == 2 || m == 3 || m == 8 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (50 : Fin 71) 17 else
       if m == 2 then Equiv.swap 60 3 else
       if m == 3 then Equiv.swap 68 69 else Equiv.swap 70 59)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 4 && l == 168 then .compute
    (([true,true,true,false,true,true,true] : List Bool).foldl
      (fun s b => Turing.TM2.Stmt.push 70 (fun _ => b) s) (.load (fun _ => 2) .halt))
  else if m == 5 && l == 0 then .compute (.load (fun _ => 2) (.goto (fun _ => 21)))
  else if m == 6 && l.val < 168 && l.val % 21 == 2 then
    .compute (.pop 25 (fun v _ => v) (program l))
  else if m == 7 && l == 168 then .compute (.push 49 (fun _ => false) (program l))
  else if m == 9 && l == 0 then .compute (.load (fun _ => 2) (program l))
  else code l
'''
PORTS=[16,15,50,51,60,65,68,69]

def source():
 return 'import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSecondKeyControls')
def bounds(c):
 s=(c['p']-1).bit_length();length=2*s+1
 field=length*(2*length.bit_length()+5)+3*length.bit_length()+5
 clock=8*(5*s+8+field)+1
 return clock,32*clock

def fixtures():
 fs=[]
 for old in prior.fixtures():
  c=copy.deepcopy(old);c['reached']=prior.expected(old)[0]+[''];fs.append(c)
 return fs

def value(w):return sum(int(bit)<<i for i,bit in enumerate(w))
def expected(c,m=0):
 ws=c['reached'].copy();ports=PORTS.copy()
 if m==1:ports[2]=17
 if m==2:ports[4]=3
 if m==3:ports[6],ports[7]=ports[7],ports[6]
 if m==5:ports=ports[:-1]
 fields=[k.nat(value(ws[port])) for port in ports]
 if m==6:fields=[word[1:] for word in fields]
 key=k.nat(7 if m==4 else 8)+''.join(k.nat(len(word))+word for word in fields)
 ws[70]=key
 if m==7:ws[49]='0'+ws[49]
 if m==8:ws[70]='';ws[59]=key
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSecondKeyNativeGenerated.lean';path.write_text(src)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 path=OUT/'second-key-native.json';r=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,guard_rejections=0,discarded=0,gaveUp=0,seeds=[118,606,20260914],scope='seven source-shaped p1 full states, four directed and three seeded; exact flat key and retained old70',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSecondKeyMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeSecondKeyNativeReproduction',bounds=bounds,host_timeout=300);fs=fixtures();fs=[fs[1],fs[0]]+fs[2:];c=fs[0]
  a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));T,C=bounds(c);assert a['steps']<=T and a['charge']<=C
  report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('stale_alpha','stale_A','swapped_C_D','wrong_record_arity','omitted_last_field','truncated_scalar_encoding','corrupted_saved','wrong_output','bypassed_entry_guard'),1):
   c=copy.deepcopy(fs[0])
   if m==9:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original caps',name,a)
   baseline=(c['reached'],'101',0,1) if m==9 else expected(c)
   assert not n.agrees(a,*baseline),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  bad=copy.deepcopy(fs[0]);bad['initial_mem']=1;a=r.execute(0,bad)
  assert n.agrees(a,bad['reached'],'101',0,1),(bad,a)
  T,C=bounds(bad);assert a['steps']<=T and a['charge']<=C,('original guard caps',a)
  report['guard_rejection']=dict(input=bad,actual=a);report['guard_rejections']=1;save()
  for c in fs[1:]:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));T,C=bounds(c);assert a['steps']<=T and a['charge']<=C
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
