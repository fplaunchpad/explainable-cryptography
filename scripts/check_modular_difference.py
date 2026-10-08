#!/usr/bin/env python3
"""Bounded gate for a new subtraction interface of unchanged42-label code."""
import hashlib,json,random,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_mod_add as old
from check_cache_request_input import Runner
OUT=ROOT/'tmp/concrete-helios'
SEEDS=(118,606,20260914)
def bits(n):return '' if n==0 else bin(n)[2:][::-1]
def execute(runner,mut,c):
 q,left,right=c
 return runner.run(mut,bits(left),(bits(right) or '-')+' '+bits(q))
def expected(c):
 q,left,right=c
 return [bits((left-right)%q),bits(right),'','','','',bits(q),'']
def good(c,a):
 q,_,_=c;clock=26*q.bit_length()+24
 return a['halted'] and a['memory']==2 and a['queries']==0 and a['steps']<=clock and a['charge']<=32*clock and a['words']==expected(c)
def main():
 exhaustive=[(q,c,e) for q in range(1,17) for c in range(q) for e in range(q)]
 directed=[(q,c,e) for q in (2,3,11,17,255,256,257) for c,e in ((0,0),(q-1,0),(0,q-1),(q-1,q-1),(q-2,q-1),(q-1,q-2))]
 seeded=[]
 for seed in SEEDS:
  rng=random.Random(seed)
  for _ in range(64):
   q=rng.randrange(1,1<<rng.randrange(1,25));seeded.append((q,rng.randrange(q),rng.randrange(q)))
 report=dict(status='running',claim='actual unchanged ModAdd(start c,e,q) computes (c-e)%q',exhaustive_domain='1<=q<=16, all0<=c,e<q',seeds=SEEDS,discards=0,gaveUp=0,canonical_cases=0,mutants=[],directed=[],max_steps=0,max_charge=0,source_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/BinaryModAddMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(old.DRIVER.encode()).hexdigest())
 save=lambda:(OUT/'modular-difference-native.json').write_text(json.dumps(report,indent=2)+'\n')
 runner=Runner(old.DRIVER,'ModularDifferenceNative')
 try:
  for m,name in ((1,'skip_underflow'),(2,'omit_complement_copy'),(3,'corrupt_modulus'),(4,'omit_result_restore')):
   c=(3,1,2);a=execute(runner,m,c)
   assert not good(c,a),(name,c,a)
   report['mutants'].append(dict(name=name,mutation=m,input=c,expected=expected(c),actual=a));print('detected '+name,flush=True)
  c=(3,1,0);a=execute(runner,4,c);assert not good(c,a)
  report['mutants'].append(dict(name='omit_result_restore_at_zero_endpoint',mutation=4,input=c,expected=expected(c),actual=a))
  for i,c in enumerate(directed+exhaustive+seeded):
   a=execute(runner,0,c)
   if not good(c,a):
    report['failure']=dict(input=c,expected=expected(c),actual=a);raise AssertionError(report['failure'])
   report['canonical_cases']+=1;report['max_steps']=max(report['max_steps'],a['steps']);report['max_charge']=max(report['max_charge'],a['charge'])
   if i<len(directed):report['directed'].append(dict(input=c,expected=expected(c),actual=a))
   if (i+1)%256==0:save();print('Checked '+str(i+1),flush=True)
  report.update(status='pass',exhaustive_cases=len(exhaustive),directed_cases=len(directed),seeded_cases=len(seeded),distinct_mutants=4,mutation_checks=5)
 finally:
  runner.close();report['child_returncode']=runner.process.returncode;save()
 print(json.dumps({k:v for k,v in report.items() if k not in ('mutants','directed')},indent=2),flush=True)
if __name__=='__main__':main()
