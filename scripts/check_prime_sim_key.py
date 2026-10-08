#!/usr/bin/env python3
"""Gate the executed eight-field ballot-key serializer on complete 44-port states.

Requires the production PrimeSimKeyMachine header. Reuses the existing original
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
import check_sim_one_second as prior
n=prior.n;k=prior.k
BASE=prior.BASE.replace('PrimeSimOneSecondControls','PrimeSimKeyControls').replace('open PrimeSimOneSecondMachine','open PrimeSimKeyMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 44 size 3 :=
  if m == 1 || m == 2 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (15 : Fin 44) 16 else Equiv.swap 40 42)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 3 && l == 0 then .compute (.load (fun _ => 2) (.goto (fun _ => next 0)))
  else if m == 4 && l == 168 then .compute
    (([true,true,true,false,true,true,true] : List Bool).foldl
      (fun s b => Turing.TM2.Stmt.push 43 (fun _ => b) s) (.load (fun _ => 2) .halt))
  else if m == 5 && l == 168 then .compute (.push 14 (fun _ => false) (program l))
  else if m == 6 && l.val < 168 && l.val % 21 == 2 then
    .compute (.pop 25 (fun v _ => v) (program l))
  else if m == 7 && l == 0 then .compute (.load (fun _ => 2) (program l))
  else code l
'''
PORTS=[16,15,17,0,3,38,40,42]
def source():
 return 'import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeSimKeyControls')
def bounds(c):
 s=(c['p']-1).bit_length();length=2*s+1
 field=length*(2*length.bit_length()+5)+3*length.bit_length()+5
 clock=8*(5*s+8+field)+1
 return clock,32*clock

def fixtures():
 fs=[]
 for old in prior.fixtures():
  c=copy.deepcopy(old);c['reached']=prior.expected(old)[0]+[''];fs.append(c)
 # Actual p23/q11 source fixture: nonce pair(3,1), c/e/z0/z1=(2,0,4,0).
 c=k.fixture(p=23,q=11,g=2,pk=4,slack=0,vote=True,saved='101')
 c['tape']='0100'+'0000'+'101'
 ws,_,_=k.prefix_expected(c)
 ws[2]=k.bits(11)
 for port,num in [(10,2),(11,0),(12,4),(7,0)]:ws[port]=k.nat(num)
 ws+=['']*21
 alpha=pow(2,3,23);beta=pow(4,3,23)*2%23;d=2;gamma=beta*pow(2,10,23)%23
 for port,num in [(1,None),(3,16),(38,3),(39,gamma),(40,9),(42,12)]:
  ws[port]=k.nat(d) if num is None else k.bits(num)
 c.update(name='q11_all_distinct_source',p=23,q=11,reached=ws,fresh_tape='101',initial_mem=2)
 assert [value(ws[port]) for port in PORTS]==[2,4,8,13,16,3,9,12]
 fs.insert(0,c)
 for seed in (118,606,20260914):
  rng=random.Random(seed);c=copy.deepcopy(fs[0]);c['name']=f'canonical_digits_seed_{seed}'
  for port in PORTS:c['reached'][port]=k.bits(rng.randrange(23))
  fs.append(c)
 return fs

def value(w):return sum(int(bit)<<i for i,bit in enumerate(w))
def expected(c,m=0):
 ws=c['reached'].copy();ports=PORTS.copy()
 if m==1:ports[0],ports[1]=ports[1],ports[0]
 if m==2:ports[6],ports[7]=ports[7],ports[6]
 if m==3:ports=ports[:-1]
 fields=[k.nat(value(ws[port])) for port in ports]
 if m==6:fields=[word[1:] for word in fields]
 ws[43]=k.nat(7 if m==4 else 8)+''.join(k.nat(len(word))+word for word in fields)
 if m==5:ws[14]='0'+ws[14]
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeSimKeyNativeGenerated.lean';path.write_text(src)
  print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 path=OUT/'prime-sim-key-native.json';r=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,guard_rejections=0,discarded=0,gaveUp=0,seeds=[118,606,20260914],scope='five source-consistent full states including q11 all-distinct; three seeded serializer-only canonical-digit fixtures',header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/PrimeSimKeyMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeSimKeyNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures();c=fs[0]
  a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c))
  report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(('swapped_generator_key','swapped_one_commitments','omitted_last_field','wrong_record_arity','corrupted_context','truncated_scalar_encoding','bypassed_entry_guard'),1):
   c=copy.deepcopy(fs[0])
   if m==7:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original caps',name,a)
   baseline=(c['reached'],'101',0,1) if m==7 else expected(c)
   assert not n.agrees(a,*baseline),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  bad=copy.deepcopy(fs[0]);bad['initial_mem']=1;a=r.execute(0,bad)
  assert n.agrees(a,bad['reached'],'101',0,1),(bad,a)
  report['guard_rejection']=dict(input=bad,actual=a);report['guard_rejections']=1;save()
  for c in fs[1:]:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c))
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
