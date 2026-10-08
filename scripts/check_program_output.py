#!/usr/bin/env python3
"""Gate proof and updated-state encoding on complete50-word boundary states.

Independent bit grammar supplies expected nested records. Canonical numeric
coordinates/scalars and typed-shaped state records are exercised; actual raw
source origin is a separate Lean obligation. Entry is label11, not label0.
"""
from pathlib import Path
import copy,hashlib,json,random,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_sim_key as prior
n=prior.n;k=prior.k
BASE=prior.BASE.replace('PrimeSimKeyControls','PrimeProgramOutputControls').replace('open PrimeSimKeyMachine','open PrimeProgramOutputMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 50 size 3 :=
  if m == 1 || m == 2 || m == 3 || m == 7 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (3 : Fin 50) 38
       else if m == 2 then Equiv.swap 11 1
       else if m == 3 then Equiv.swap 44 45 else Equiv.swap 48 49)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 4 && l == 0 then .compute
    (.branch (fun v => v == 2)
      (([true,false,true] : List Bool).foldl
        (fun s b => Turing.TM2.Stmt.push 28 (fun _ => b) s)
        (.goto (fun _ => natLabel 2 0))) fail)
  else if m == 5 && l == 2 then .compute (.push 14 (fun _ => false) (program l))
  else if m == 6 && l == 3 then .compute (.goto (fun _ => 4))
  else if m == 8 && l == natLabel 0 0 then .compute (.load (fun _ => 2) (program l))
  else if m == 9 && l == 2 then .compute (.push 46 (fun _ => false) (program l))
  else if m == 10 && l == pairLabel 0 0 then .compute (.goto (fun _ => pairLabel 1 0))
  else code l
'''

def field(w):return k.nat(len(w))+w
def fields(ws):return k.nat(len(ws))+''.join(map(field,ws))
def pair(a,b):return fields([a,b])
def statement(v):return pair(pair(k.nat(v[0]),k.nat(v[1])),pair(k.nat(v[2]),k.nat(v[3])))
def bits_value(w):return sum(int(b)<<i for i,b in enumerate(w))
def fixtures():
 fs=[]
 def add(name,p,q,coords,scalars,shadow,history,live,bad):
  ws=['101' if j%2 else '01' for j in range(50)]
  for j in range(23,38):ws[j]=''
  for j in (48,49):ws[j]=''
  for j,v in zip([3,38,40,42],coords):ws[j]=k.bits(v)
  for j,v in zip([11,12,1,7],scalars):ws[j]=k.nat(v)
  ws[44]=shadow;ws[45]=live;ws[46]=str(int(bad));ws[47]=history
  N=max(len(shadow),len(live),len(history))
  fs.append(dict(name=name,p=p,q=q,N=N,reached=ws,initial_mem=2,fresh_tape='101'))
 key=fields([k.nat(v) for v in [2,4,8,13,16,3,9,12]])
 shadow=fields([pair(key,k.nat(2))]);stmt=statement([2,4,8,13])
 add('distinct_proof_and_updated_state',23,11,[16,3,9,12],[0,4,2,0],shadow,fields([stmt,statement([3,9,12,16]),stmt]),fields([]),True)
 add('wrapped_challenge',7,3,[2,4,1,2],[1,2,2,0],fields([]),fields([statement([2,4,1,2])]),fields([pair(key,k.nat(1))]),False)
 add('zero_digits_empty_payloads',1,1,[0,0,0,0],[0,0,0,0],'','','',False)
 for seed in (118,606,20260914):
  rng=random.Random(seed)
  add(f'seed_{seed}',23,11,[rng.randrange(23) for _ in range(4)],[rng.randrange(11) for _ in range(4)],
      fields([pair(key,k.nat(rng.randrange(11)))]),fields([stmt]*rng.randrange(1,4)),fields([]),bool(rng.randrange(2)))
 return fs

def expected(c,m=0):
 ws=c['reached'].copy();a,b,cc,d=[k.nat(bits_value(ws[i])) for i in [3,38,40,42]]
 e,z0,dc,z1=[ws[i] for i in [11,12,1,7]]
 if m==1:a,b=b,a
 if m==2:e,dc=dc,e
 gp0=pair(a,b);gp1=pair(cc,d)
 if m==4:gp0=k.nat(1)+field(a)+field(b)
 sp0='' if m==10 else pair(e,z0)
 proof=pair(pair(gp0,sp0),pair(gp1,pair(dc,z1)))
 shadow,live=ws[44],ws[45]
 if m==3:shadow,live=live,shadow
 saved=pair(pair(shadow,pair(ws[46],ws[47])),live)
 ws[48],ws[49]=(saved,proof) if m==7 else (proof,saved)
 if m==5:ws[14]='0'+ws[14]
 if m==6:ws[28]=gp0
 if m==9:ws[46]='0'+ws[46]
 return ws,'101',0

def bounds(c):
 p,q,N=c['p'],c['q'],c['N'];g=2*(p-1).bit_length()+1;z=2*(q-1).bit_length()+1
 pairsize=lambda a,b:5+(2*a.bit_length()+1+a)+(2*b.bit_length()+1+b)
 listsize=lambda a,n:2*n.bit_length()+1+n*(2*a.bit_length()+1+a)
 gp=pairsize(g,g);sp=pairsize(z,z);branch=pairsize(gp,sp)
 key=9+8*(2*g.bit_length()+1+g);entry=pairsize(key,z)
 cache=listsize(entry,N+1);hist=listsize(pairsize(gp,gp),N+1)
 meta=pairsize(1,hist);prog=pairsize(cache,meta)
 F=lambda x:x*(2*x.bit_length()+5)+3*x.bit_length()+5
 P=lambda a,b:2*(a+b)+F(a)+F(b)+7
 nat=5*(p-1).bit_length()+8+F(g)
 left=[z,z,gp,gp,branch,1,cache,prog];right=[z,z,sp,sp,branch,hist,meta,N]
 temps=[gp,gp,sp,sp,branch,branch,meta,prog]
 T=4*nat+sum(P(a,b) for a,b in zip(left,right))+sum(temps)+11
 return T,32*T

def main():
 header=ROOT/'ExplainableCrypto/Helios/Computational/PrimeProgramOutputMachine.lean'
 driver=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeProgramOutputControls').replace('⟨some 0,','⟨some (natLabel 0 0),')
 src='import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine\n'+n.NATIVE_SNAPSHOT+BASE+MUT+driver
 if '--generate-only' in sys.argv:
  dest=OUT/'PrimeProgramOutputNativeGenerated.lean';dest.write_text(src);print(dest);return
 path=OUT/'program-output-native.json';r=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,guard_rejections=0,discarded=0,gaveUp=0,seeds=[118,606,20260914],scope='numeric/canonical-shaped constructor boundary with arbitrary preserved frame; raw source origin separate',header_sha256=hashlib.sha256(header.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeProgramOutputNativeReproduction',bounds=bounds,host_timeout=120)
  fs=fixtures()
  for m,name in [(0,'original')]+list(enumerate(('swapped_zero_coordinates','swapped_branch_challenges','swapped_shadow_live','wrong_group_pair_count','corrupted_original_raw','omitted_temporary_cleanup','swapped_proof_saved_outputs','bypassed_entry_guard','corrupted_sticky_flag','omitted_scalar_pair'),1)):
   c=copy.deepcopy(fs[0])
   if m==8:c['initial_mem']=1
   a=r.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',name,a)
   if m:
    baseline=(c['reached'],'101',0,1) if m==8 else expected(c)
    assert not n.agrees(a,*baseline),('insensitive',name)
    report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1
   else:report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1
   save();print(name+' PASS',flush=True)
  bad=copy.deepcopy(fs[0]);bad['initial_mem']=1;a=r.execute(0,bad)
  assert n.agrees(a,bad['reached'],'101',0,1),(bad,a)
  T,C=bounds(bad);assert a['steps']<=T and a['charge']<=C
  report['guard_rejection']=dict(input=bad,actual=a);report['guard_rejections']=1;save()
  for c in fs[1:]:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c))
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('originalcaps',c['name'],a)
   report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','guard_rejection')},indent=2),flush=True)
if __name__=='__main__':main()
