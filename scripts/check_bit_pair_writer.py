#!/usr/bin/env python3
"""Preserving pair writer: bounded actual-code gate against independent encodings.

Build BitPairWriterMachine and run this script. Eighteen canonical cases cover
empty, asymmetric, unequal nonpalindromic and long words plus seeds118,606,
20260914. Ten actual code mutations cover order/count/framing/copies/preservation,
flags and truncation. Every original/mutant/rejection checks original step/charge
caps, zero queries and unchanged residual101. No discards or gaveUp.
The native test-only snapshot/table adapters are proved identical in the driver.
The host120second timeout is a test limit, not a runtime theorem.
--generate-only writes the production-import driver. Reproduction output has its
own directory; retained historical evidence is not overwritten.
"""
from pathlib import Path
import sys,json,hashlib,copy,random
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'tmp/concrete-helios/reproduction';OUT.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(ROOT/'scripts'));sys.dont_write_bytecode=True
import check_prime_honest_transcript_native as n
def bits(x):return ''.join(str(x>>i&1) for i in range(x.bit_length()))
def nat(x):return '1'*x.bit_length()+'0'+bits(x)
def pair(a,b):return nat(2)+nat(len(a))+a+nat(len(b))+b
def make(name,a,b,mem=2):return dict(name=name,reached=[a,b,'','','','',''],initial_mem=mem,fresh_tape='101',expected=[a,b,pair(a,b),'','','',''])
def fixtures():
 fs=[make('empty_both','',''),make('empty_left','','10110'),make('empty_right','011',''),make('nonpalindromic','10110','011'),make('singletons','0','1'),make('long_asymmetric','10110010'*8,'001011'*15)]
 for seed in [118,606,20260914]:
  r=random.Random(seed)
  for j in range(4):
   a=''.join(str(r.getrandbits(1)) for _ in range(r.randrange(1,130)));b=''.join(str(r.getrandbits(1)) for _ in range(r.randrange(1,130)));fs.append(make(f'seed_{seed}_{j}',a,b))
 return fs
def bounds(c):
 L,R=map(len,c['reached'][:2]);F=lambda x:x*(2*x.bit_length()+5)+3*x.bit_length()+5;T=2*(L+R)+F(L)+F(R)+7;return T,32*T
BASE=n.k.BASE.split('private def replaceRecord')[0].replace('PrimeHonestTranscriptControls','BitPairWriterGate').replace('open PrimeHonestTranscriptMachine','open BitPairWriterMachine')
MUT=r'''
private def mutated (m : Nat) (l : Fin size) : Command 7 size 3 :=
  if m == 1 && 3 ≤ l.val && l.val < 7 then
    .compute (TM2FiniteCoordinates.translate (Equiv.swap (0 : Fin 7) 1) (Equiv.refl _) (Equiv.refl _) (program l))
  else if m == 2 && l == 2 then .compute (.load (fun _ => 2) .halt)
  else if m == 3 && l == 0 then .compute (.load (fun _ => 0) (.goto (fun _ => fieldLabel 0 3)))
  else if m == 4 && l == 1 then .compute (.load (fun _ => 0) (.goto (fun _ => fieldLabel 1 3)))
  else if m == 5 && l == 2 then .compute (.pop 2 (fun v _ => v) (program l))
  else if (m == 6 || m == 7) && l == 2 then
    .compute (.push (if m == 6 then 0 else 1) (fun _ => false) (program l))
  else if m == 8 && l == 0 then .compute (.load (fun _ => 0) (.goto (fun _ => copyLabel 0 0)))
  else if m == 9 && l == 1 then .compute (.load (fun _ => 1) (program l))
  else if m == 10 && l == 2 then .compute (.push 2 (fun _ => false) (program l))
  else code l
'''
def source():
 return 'import ExplainableCrypto.Helios.Computational.BitPairWriterMachine\n'+n.NATIVE_SNAPSHOT+BASE+'''example : ∀ l, localCost (program l) ≤ 32 := by decide +kernel
example : bitFieldsEncode [[],[]] = [true,true,false,false,true,false,false] := by decide +kernel
'''+MUT+n.DRIVER.replace('PrimeHonestTranscriptControls','BitPairWriterGate')
def good(a,c):return n.agrees(a,c['expected'],'101',0)
def main():
 src=source()
 if '--generate-only' in sys.argv:
  path=OUT/'BitPairWriterNativeGenerated.lean';path.write_text(src);print(path);return
 r=None;path=OUT/'bit-pair-writer-native.json';report=dict(status='running',canonical_cases=[],mutants=[],rejections=[],seeds=[118,606,20260914],discards=0,gaveUp=0,header_sha256=hashlib.sha256((ROOT/'ExplainableCrypto/Helios/Computational/BitPairWriterMachine.lean').read_bytes()).hexdigest(),driver_sha256=hashlib.sha256(src.encode()).hexdigest())
 def save():path.write_text(json.dumps(report,indent=2)+'\n')
 save()
 try:
  r=n.GateRunner(src,'BitPairWriterNativeReproduction',bounds=bounds,host_timeout=120);fs=fixtures()
  for c in fs[:6]:
   a=r.execute(0,c);assert good(a,c),(c,a);report['canonical_cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  c=fs[3]
  for m in [1,2,3,4,5,6,7,9,10]:
   a=r.execute(m,c);assert a['halted'] and not good(a,c),(m,c,a);report['mutants'].append(dict(mutation=m,input=c,actual=a));save();print('mutant '+str(m)+' detected',flush=True)
  c=copy.deepcopy(fs[3]);c['initial_mem']=1;a=r.execute(0,c);assert n.agrees(a,c['reached'],'101',0,1),(c,a);report['rejections'].append(dict(input=c,actual=a));a=r.execute(8,c);assert good(a,c),(c,a);report['mutants'].append(dict(mutation=8,input=c,actual=a));save()
  for c in fs[6:]:
   a=r.execute(0,c);assert good(a,c),(c,a);report['canonical_cases'].append(dict(input=c,actual=a));save();print(c['name']+' PASS',flush=True)
  for block in ['canonical_cases','mutants','rejections']:
   for item in report[block]:
    a=item['actual'];T,C=bounds(item['input']);assert a['halted'] and a['steps']<=T and a['charge']<=C and a['coins']==a['hashes']==0 and a['remaining']=='101'
  report.update(status='pass',original_caps_and_query_policy='pass for all originals/mutants/rejections')
 except BaseException as e:report.update(status='failed',failure=repr(e));raise
 finally:
  if r:r.close();report['child_returncode']=r.process.returncode
  save()
 print(json.dumps({k:(len(v) if isinstance(v,list) and k in ['canonical_cases','mutants','rejections'] else v) for k,v in report.items()},indent=2))
if __name__=='__main__':main()
