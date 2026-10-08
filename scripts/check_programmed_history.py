#!/usr/bin/env python3
"""Bounded original-code gate: nested statement encoding and history prepend.

Independent Python bit grammar supplies complete48-state expectations. Uses the
existing step runner and identity adapters; no new machine interpreter. Default
requires production header; --staged-header checks the exact temporary header.
"""
from pathlib import Path
import copy,hashlib,json,random,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_sim_key as prior
n=prior.n;k=prior.k
BASE=prior.BASE.replace('PrimeSimKeyControls','PrimeProgrammedHistoryControls').replace('open PrimeSimKeyMachine','open PrimeProgrammedHistoryMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 48 size 3 :=
  if m == 1 || m == 2 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (15 : Fin 48) 16 else Equiv.swap 0 17)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 3 && l == 4 then .compute (guard
    (([true,false,true] : List Bool).foldl
      (fun s b => Turing.TM2.Stmt.push 29 (fun _ => b) s) (enter (parseLabel 0))))
  else if m == 4 && l == 5 then .compute (guard (enter (writerLabel 2 3)))
  else if m == 5 && l == 6 then .compute (guard (enter (writerLabel 3 5)))
  else if m == 6 && l == 8 then .compute (.push 46 (fun _ => false) (program l))
  else if m == 7 && l == 0 then .compute (.load (fun _ => 2) (program l))
  else code l
'''

def field(w):return k.nat(len(w))+w
def fields(ws):return k.nat(len(ws))+''.join(map(field,ws))
def stmt(v):return fields([fields([k.nat(v[0]),k.nat(v[1])]),fields([k.nat(v[2]),k.nat(v[3])])])
def fixtures():
 fs=[]
 def add(name,p,values,history):
  ws=['101' if j%2 else '01' for j in range(48)]
  for j in range(23,30):ws[j]=''
  for j,v in zip([16,15,17,0],values):ws[j]=k.bits(v)
  ws[47]=fields(history)
  fs.append(dict(name=name,p=p,values=values,history=history,reached=ws,fresh_tape='101',initial_mem=2))
 add('distinct_coordinates_unequal_history',23,[2,4,8,13],[stmt([3,9,12,16]),stmt([1,2,3,4])])
 add('empty_history',3,[1,2,2,1],[])
 add('duplicate_statement_retained',7,[2,4,1,2],[stmt([2,4,1,2])])
 add('count_three_to_four',7,[2,4,4,1],[stmt([2,4,1,2])]*3)
 add('zero_numeric_coordinates',1,[0,0,0,0],[])
 for seed in (118,606,20260914):
  rng=random.Random(seed)
  add(f'seed_{seed}',11,[rng.randrange(11) for _ in range(4)],
    [stmt([rng.randrange(11) for _ in range(4)]) for _ in range(rng.randrange(4))])
 return fs

def expected(c,m=0):
 ws=c['reached'].copy();v=c['values'].copy();hist=c['history'];h=len(hist)
 if m==1:v[0],v[1]=v[1],v[0]
 if m==2:v[2],v[3]=v[3],v[2]
 s=stmt(v)
 if m==3:s=k.nat(1)+s[len(k.nat(2)):]
 if m==5:
  ws[29]=s;ws[47]=k.nat(h+1)+''.join(map(field,hist))
 else:ws[47]=k.nat(h if m==4 else h+1)+field(s)+''.join(map(field,hist))
 if m==6:ws[46]='0'+ws[46]
 return ws,'101',0

def bounds(c):
 p=c['p'];H=len(c['reached'][47]);g=2*(p-1).bit_length()+1
 pair=lambda a,b:5+2*a.bit_length()+1+a+2*b.bit_length()+1+b
 F=lambda x:x*(2*x.bit_length()+5)+3*x.bit_length()+5
 P=pair(g,g);S=pair(P,P);W=5*(p-1).bit_length()+8+F(g)
 T=4*W+2*F(P)+F(S)+5*H.bit_length()+3*(H+1).bit_length()+17
 return T,32*T

def main():
 staged='--staged-header' in sys.argv
 header=ROOT/('tmp/concrete-helios/PrimeProgrammedHistoryMachine.lean' if staged else 'ExplainableCrypto/Helios/Computational/PrimeProgrammedHistoryMachine.lean')
 src=(header.read_text() if staged else 'import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine\n')+'\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeProgrammedHistoryControls')
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeProgrammedHistoryNativeGenerated.lean';path.write_text(src);print(path);return
 path=OUT/'programmed-history-native.json';r=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,guard_rejections=0,discarded=0,gaveUp=0,seeds=[118,606,20260914],scope='canonical numeric coordinate digits and nested statement histories; source origin separate',header_sha256=hashlib.sha256(header.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeProgrammedHistoryNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures();c=fs[0]
  for m,name in [(0,'original')]+list(enumerate(('swapped_generator_key','swapped_ciphertext_coordinates','wrong_outer_pair_count','omitted_count_increment','omitted_statement_write','corrupted_sticky_flag','bypassed_entry_guard'),1)):
   c=copy.deepcopy(fs[0])
   if m==7:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m)
   assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original caps',name,a)
   if m:
    baseline=(c['reached'],'101',0,1) if m==7 else expected(c)
    assert not n.agrees(a,*baseline),('insensitive',name)
    report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1
   else:
    assert a['words'][47] != fields(c['history']+[stmt(c['values'])]),'append shortcut'
    report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1
   save();print(name+' PASS',flush=True)
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
