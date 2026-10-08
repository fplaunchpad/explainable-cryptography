#!/usr/bin/env python3
"""Independent nested-state extractor gate using the existing original-step loop.

The typed state encoding is three nested pairs inside the fifth raw field.
Fixtures exercise that exact framing shape; arbitrary cache/history payload
bytes test extraction, not semantic validity of their contents. Every complete
48-word result, query count, residual stream and original cap is checked.
--staged-header uses the frozen tmp header before promotion; --generate-only
writes the selected driver without executing Lean.
"""
from pathlib import Path
import copy,hashlib,json,random,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
import check_prime_sim_key as prior
from check_prime_honest_input_kernel import fields,nat
n=prior.n;k=prior.k
NS='PrimeProgrammedStateInputControls'
BASE=prior.BASE.replace('PrimeSimKeyControls',NS).replace('open PrimeSimKeyMachine','open PrimeProgrammedStateInputMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 48 size 3 :=
  if m == 1 || m == 2 then .compute
    (TM2FiniteCoordinates.translate
      (if m == 1 then Equiv.swap (44 : Fin 48) 45 else Equiv.swap 46 47)
      (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 3 && l == 16 then .compute (.push 43 (fun _ => false) (program l))
  else if m == 4 && l == 16 then .compute (.push 10 (fun _ => false) (program l))
  else if m == 5 && l == 16 then .compute (.load (fun _ => 2) .halt)
  else if m == 6 && l == 21 then .compute
    (.pop 23 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 1) (.load (fun _ => 0) (.goto (fun _ => 22)))
        (.load (fun _ => 1) .halt)))
  else if m == 7 && l == 11 then .compute
    (.branch (fun v => v == 2) (.load (fun _ => 0) (.goto (fun _ => 16)))
      (.load (fun _ => 1) .halt))
  else if m == 8 && l == 15 then .compute (.load (fun _ => 2) .halt)
  else if m == 9 && l == 0 then .compute (.load (fun _ => 2) (program l))
  else code l
'''
def header():
 return ROOT/('tmp/concrete-helios/PrimeProgrammedStateInputMachine.lean' if '--staged-header' in sys.argv else 'ExplainableCrypto/Helios/Computational/PrimeProgrammedStateInputMachine.lean')
def source():
 imp=header().read_text() if '--staged-header' in sys.argv else 'import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine\n'
 return imp+'\n'+n.NATIVE_SNAPSHOT+BASE+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls',NS)
def bounds(c):
 N=len(c['reached'][14]);S=N.bit_length();clock=11*(3*S+7+N*(2*S+3))+6*N+41
 return clock,32*clock

def make(name='empty_cache_history',a=None,b=None,c=None,d=None,shadow='0',live='0',flag='0',history='0',outer_count=5,top_count=2,meta_tail=''):
 priorcase=prior.fixtures()[2];old=prior.expected(priorcase)[0]
 parts=[nat(7),fields([nat(2),nat(4)]),'0'+nat(3),'1']
 for i,x in enumerate([a,b,c,d]):
  if x is not None:parts[i]=x
 meta=fields([flag,history])+meta_tail
 programmed=fields([shadow,meta]);saved=fields([programmed,live],count=top_count)
 raw=fields(parts+[saved],count=outer_count)
 old[14]=raw
 return dict(name=name,reached=old+['']*4,fresh_tape='101',initial_mem=2,parts=parts,shadow=shadow,live=live,flag=flag,history=history,saved=saved,meta_tail=meta_tail,outer_count=outer_count,top_count=top_count)
def expected(c,m=0):
 ws=c['reached'].copy();ws[44:48]=[c['shadow'],c['live'],c['flag'],c['history']];mem=2
 if m==1:ws[44],ws[45]=ws[45],ws[44]
 if m==2:ws[46],ws[47]=ws[47],ws[46]
 if m==3:ws[43]='0'+ws[43]
 if m==4:ws[10]='0'+ws[10]
 if m==7:ws[26]=c['meta_tail']
 if m==8:
  ws=c['reached'].copy();ws[23]=nat(len(c['saved']))+c['saved'];ws[26]=c['parts'][3]
 return ws,'101',0,mem

def rejected(c):
 ws=c['reached'].copy()
 if c['initial_mem']!=2:return ws,'101',0,1
 if c['outer_count']!=5:ws[23]=ws[14][5:];return ws,'101',0,1
 if c['top_count']!=2:ws[26]=c['saved'][2:];return ws,'101',0,1
 ws[44:48]=[c['shadow'],c['live'],c['flag'],c['history']]
 if c['meta_tail']:ws[26]=c['meta_tail']
 else:ws[46]=c['flag'][1:]
 return ws,'101',0,1

def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'PrimeProgrammedStateInputNativeGenerated.lean';path.write_text(src);print(json.dumps(dict(status='generated',lean_executed=False,path=str(path)),indent=2));return
 path=OUT/'programmed-state-input-native.json';r=None
 report=dict(status='running',canonical_cases=0,mutation_cases=0,rejection_cases=0,discarded=0,gaveUp=0,seeds=[118,606,20260914],scope='fixed nested framing and arbitrary retained frame/payload bytes; no cache semantic validation claim',header_sha256=hashlib.sha256(header().read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest(),cases=[],mutants=[],rejections=[])
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'PrimeProgrammedStateInputNative',bounds=bounds,host_timeout=120)
  witness=make(name='distinct_retained',shadow=fields(['10','011']),live=fields(['1']),flag='1',history=fields(['10','10','011']))
  for c in [make(),witness]:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  mutants=[(1,'swapped_shadow_live',witness),(2,'swapped_flag_history',witness),(3,'corrupted_completed_key',witness),(4,'corrupted_challenge',witness),(5,'unchecked_flag',make(flag='10')),(6,'wrong_outer_count',make(outer_count=4)),(7,'ignored_nested_tail',make(meta_tail='1')),(8,'omitted_final_discard_and_remaining_fields',witness),(9,'bypassed_entry_guard',dict(witness,initial_mem=1))]
  for m,name,c in mutants:
   a=r.execute(m,c);want=expected(c,m);assert n.agrees(a,*want),(name,c,a,want)
   T,C=bounds(c);assert a['steps']<=T and a['charge']<=C,('original caps',name,a)
   baseline=rejected(c) if m in (5,6,7,9) else expected(c)
   assert not n.agrees(a,*baseline),('insensitive',name)
   report['mutants'].append(dict(name=name,input=c,actual=a,independent_expected=want));report['mutation_cases']+=1;save();print('detected '+name,flush=True)
  for c in [make(flag=''),make(flag='10'),make(outer_count=4),make(top_count=1),make(meta_tail='1'),dict(witness,initial_mem=1)]:
   a=r.execute(0,c);want=rejected(c);assert n.agrees(a,*want),(c,a,want)
   report['rejections'].append(dict(input=c,actual=a));report['rejection_cases']+=1;save()
  cases=[make(name='all_empty_payloads',a='',b='',c='',d='',shadow='',live='',history=''),make(name='flag_true_empty',flag='1'),make(name='long_payload',a='101'*20,history=fields(['11']*3),live='10101')]
  for seed in (118,606,20260914):
   rng=random.Random(seed)
   for j in range(2):
    word=lambda:''.join(rng.choice('01') for _ in range(rng.randrange(16)))
    cases.append(make(name=f'seed_{seed}_{j}',a=word(),b=word(),c=word(),d=word(),shadow=word(),live=word(),flag=rng.choice('01'),history=word()))
  for c in cases:
   a=r.execute(0,c);assert n.agrees(a,*expected(c)),(c,a,expected(c));report['cases'].append(dict(input=c,actual=a));report['canonical_cases']+=1;save();print(c['name']+' PASS',flush=True)
  report['status']='pass'
 except BaseException as e:
  report.update(status='failed',failure_type=type(e).__name__,failure=repr(e),child_returncode=None if r is None else r.process.poll());raise
 finally:
  if r:r.close();report['final_child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('cases','mutants','rejections')},indent=2),flush=True)
if __name__=='__main__':main()
