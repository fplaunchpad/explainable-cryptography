#!/usr/bin/env python3
"""Fixed proof-request reentry: six numeric boundaries, seven instruction defects.

Build PrimeProofRequestReentry first. This reuses the existing original-step
native driver, checks full58 state and original bounds, and includes zero sum,
nonzero sum, prior-proof/state retention and a guard rejection. No raw source
reachability or random campaign is claimed. --generate-only emits the imported
driver without running Lean. A wrong writer-port development was independently
refuted and is retained as checked Controls.wrong_input_one in the module.
"""
from pathlib import Path
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import check_program_output as o
n=o.n;k=o.k
HEADER=ROOT/'ExplainableCrypto/Helios/Computational/PrimeProofRequestReentry.lean'
OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
BASE=o.BASE.replace('PrimeProgramOutputControls','PrimeProofRequestReentryControls').replace('open PrimeProgramOutputMachine','open PrimeProofRequestReentry')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 58 size 3 :=
  if m == 1 && l == 34 then .compute (.push 48 (fun _ => false) (program l))
  else if m == 2 && l == 34 then .compute (.pop 44 (fun _ b => BinaryModuloCode.memory b) (program l))
  else if m == 3 && l == 24 then .compute (enter 25)
  else if m == 4 && 35 <= l.val && l.val < 39 then .compute
    (TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 58) 21) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 5 && l == addLabel (BinaryModAddMachine.subLabel 0 0) then .compute
    (.load (fun _ => 2) (.goto (fun _ => 8)))
  else if m == 6 && l == 10 then .compute (.pop 51 (fun _ b => BinaryModuloCode.memory b)
    (.push 51 (fun _ => false) (program l)))
  else if m == 7 && (l == 0 || l == 1) then .compute (.load (fun _ => 2) (program l))
  else code l
'''
def source():
 d=n.DRIVER.replace('PrimeHonestTranscriptControls','PrimeProofRequestReentryControls')
 d=d.replace('let m := p[0]!.toNat!','let tag := p[0]!.toNat!\n    let m := tag % 100')
 d=d.replace('⟨some 0,⟨p[2]!', '⟨some (if tag / 100 == 1 then 1 else 0),⟨p[2]!')
 return 'import ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry\n'+n.NATIVE_SNAPSHOT+BASE+MUT+d
CLEAR=[1,2,3,7,10,11,12,13,23,24,25,26,27,28,29,37,38,39,40,42,43,49,50,51]
def make(name,total,q=3,r1=1,r2=2,vote=True):
 p,g,pk={2:(3,2,1),3:(7,2,4),11:(23,2,4)}[q]
 ws=['101' if j%2 else '01' for j in range(58)]
 for j in range(23,38):ws[j]=''
 a,b=pow(g,r1,p),pow(pk,r1,p)*(g if vote else 1)%p
 aa,bb=pow(g,r2,p),pow(pk,r2,p)
 for j,v in [(0,b),(6,p),(15,pk),(16,g),(17,a),(2,q),(22,q-1),(13,r2 if total else r1)]:ws[j]=k.bits(v)
 ws[18]=str(int(vote));ws[19]='0'+k.nat(q);ws[20]=k.nat(r1);ws[21]=k.nat(r2)
 # Independent nested records; requests have canonical scalar words and group coordinates.
 com=[1,1,1,1];e,z0,d,z1=0,0,0,0
 for j,v in zip([3,38,40,42],com):ws[j]=k.bits(v)
 for j,v in zip([11,12,1,7],[e,z0,d,z1]):ws[j]=k.nat(v)
 ws[10]=k.nat(0);ws[39]=k.bits(b*pow(g,q-1,p)%p);ws[41]=''
 kw=o.fields([k.nat(v) for v in [g,pk,a,b]+com]);stmt=o.statement([g,pk,a,b])
 proof=o.pair(o.pair(o.pair(k.nat(1),k.nat(1)),o.pair(k.nat(0),k.nat(0))),o.pair(o.pair(k.nat(1),k.nat(1)),o.pair(k.nat(0),k.nat(0))))
 ws[43]=kw;ws[44]=o.fields([o.pair(kw,k.nat(0))]);ws[45]=o.fields([]);ws[46]='1';ws[47]=o.fields([stmt,stmt]);ws[48]=proof
 ws[49]=o.pair(o.pair(ws[44],o.pair(ws[46],ws[47])),ws[45]);ws[14]='10101'
 ws[50]=k.nat(r2) if total else '';ws[51]='0' if total else ''
 ws[52]=proof if total else '';ws[53]='';ws[54]=k.bits(aa) if total else '';ws[55]=k.bits(bb) if total else '';ws[56]='';ws[57]=''
 return dict(name=name,total=total,q=q,p=p,r1=r1,r2=r2,vote=vote,N=max(map(len,ws)),reached=ws,initial_mem=2,fresh_tape='101',kind='canonical_numeric_boundary')
def bounds(c):
 q,N=c['q'],c['N'];Q=q.bit_length();R=(q-1).bit_length()
 T=40*N+20*R+8*Q+100+(10*R+5*Q+17)+(26*Q+24)
 return T,32*T
def expected(c,m=0):
 ws=c['reached'].copy()
 if c['initial_mem']!=2 and m!=7:return ws,'101',0,1
 nonce=(c['r1']+c['r2'])%c['q'] if c['total'] else c['r2'];vote=c['vote'] if c['total'] else False
 if m==4:nonce=c['r1']
 if m==5:nonce=c['r1']
 if m==6:vote=False
 for j in CLEAR:ws[j]=''
 ws[50]=k.nat(nonce);ws[51]=str(int(vote))
 if m==1:ws[48]='0'+ws[48]
 if m==2:ws[44]=ws[44][1:]
 if m==3:ws[49]=c['reached'][49]
 return ws,'101',0

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeProofRequestReentryNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path))));return
 report=dict(status='running',cases=[],mutants=[],rejections=[],seeds=[],discarded=0,gaveUp=0,host_timeout_seconds=120,header_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 path=OUT/'proof-request-reentry-native.json';r=None
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 def check(a,c,w):
  assert n.agrees(a,*w),(c['name'],a,w)
  T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original_caps',a,T,C)
 def run(c,m=0):
  a=r.execute(m+100*int(c['total']),c);check(a,c,expected(c,m));return a
 save()
 try:
  r=n.GateRunner(src,'PrimeProofRequestReentryNative',bounds=bounds,host_timeout=120)
  fs=[make('q3_zero_sum',True),make('p1_distinct_nonce',False),make('q2_zero_sum',True,q=2,r1=1,r2=1),make('q3_no_wrap_false',True,r1=1,r2=1,vote=False),make('q11_wrap',True,q=11,r1=10,r2=1),make('zero_nonce_boundary',True,r1=0,r2=0)]
  for c in fs[:2]:
   a=run(c);report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for m,name in enumerate(['corrupt_p0_proof','drop_current_shadow_bit','retain_stale_saved','use_r1_for_p1','omit_nonce_addition','lose_original_vote','bypass_entry_guard'],1):
   c=copy.deepcopy(fs[1] if m==4 else fs[0]);c['name']=name
   if m==7:c['initial_mem']=1
   a=run(c,m);assert not n.agrees(a,*expected(c));report['mutants'].append(dict(name=name,input=c,actual=a));save();print(name+' PASS',flush=True)
  c=copy.deepcopy(fs[0]);c['initial_mem']=1;a=run(c);report['rejections'].append(dict(input=c,actual=a));save()
  for c in fs[2:]:
   a=run(c);report['cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  report.update(status='pass',canonical_cases=len(report['cases']),mutation_cases=len(report['mutants']),guard_rejections=len(report['rejections']))
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','rejections')},indent=2),flush=True)
if __name__=='__main__':main()
