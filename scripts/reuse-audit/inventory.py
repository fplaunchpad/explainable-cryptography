#!/usr/bin/env python3
"""Measure the frozen proof inventory; counts are not effort or savings estimates."""
from pathlib import Path
import csv,json,re,collections,hashlib,subprocess
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'output/reuse-audit'
snapshot=json.loads((OUT/'completed-secrecy-snapshot.json').read_text())
kernel=json.loads((OUT/'kernel-dependencies.json').read_text())
kmods={r['module'] for r in kernel}
def strip_comments(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s):out.append(s[i+1]);i+=2;continue
   if s[i]=='"':string=False
   i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   while i<len(s) and s[i]!='\n':out.append(' ');i+=1
  else:
   if s[i]=='"':string=True
   out.append(s[i]);i+=1
 return ''.join(out)
def measures(s):
 raw=s.splitlines();code=strip_comments(s).splitlines()
 return {'physical_lines':len(raw),'code_lines':sum(bool(x.strip()) for x in code),
         'comment_only_lines':sum(bool(a.strip()) and not b.strip() for a,b in zip(raw,code)),
         'blank_lines':sum(not x.strip() for x in raw)}
rows=[]
for p in sorted((ROOT/'ExplainableCrypto/Helios/Symbolic').glob('*.lean')):
 module='.'.join(p.relative_to(ROOT).with_suffix('').parts)
 role='audit' if p.stem=='Audit' else 'controls' if p.stem.endswith(('SPOT','Experiments')) else 'model_and_proof'
 rows.append({'module':module,'role':role,'kernel_dependency':module in kmods,'import_dependency':module in snapshot['modules'],**measures(p.read_text())})
with (OUT/'module-inventory.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def total(xs):
 return {'modules':len(xs),**{k:sum(x[k] for x in xs) for k in ['physical_lines','code_lines','comment_only_lines','blank_lines']}}
result={'all_symbolic':total(rows),'by_role':{r:total([x for x in rows if x['role']==r]) for r in ['model_and_proof','controls','audit']},
 'kernel_files':total([x for x in rows if x['kernel_dependency']]),
 'import_files':total([x for x in rows if x['import_dependency']]),
 'import_only_files':total([x for x in rows if x['import_dependency'] and not x['kernel_dependency']]),
 'kernel_source_process_files':total([x for x in rows if x['kernel_dependency'] and x['module'].split('.')[-1].startswith('Source')]),
 'kernel_other_files':total([x for x in rows if x['kernel_dependency'] and not x['module'].split('.')[-1].startswith('Source')]),
 'kernel_constants':len(kernel),'constant_origins':dict(collections.Counter(r['module'].split('.')[0] for r in kernel)),
 'external_module_origins':dict(collections.Counter(m.split('.')[0] for m in kmods if not m.startswith('ExplainableCrypto.'))),
 'adapter_files':{p.name:measures(p.read_text()) for p in sorted((ROOT/'docs/research/reuse-adapters').glob('*.lean'))}}
# Concrete candidate scopes, deliberately not an estimate of replaceable work.
s=(ROOT/'ExplainableCrypto/Helios/Symbolic/SourceUnusedRestrictions.lean').read_text();a=s.index('theorem freeNames_restrictNames');b=s.index('\n/--',a)
result['frame_replacement_original']=measures(s[a:b])
s=(ROOT/'docs/research/reuse-adapters/FramePort.lean').read_text();a=s.index('theorem frameResChainFresh');b=s.index('\n/-- Original structural',a)
result['frame_replacement_adapter']=measures(s[a:b])
s=(ROOT/'ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean').read_text();a=s.index('def WeakReduction');b=s.index('\nend ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named',a)
result['generic_b10_candidate_scope']=measures(s[a:b])
s=(ROOT/'docs/research/reuse-adapters/CSLibComposition.lean').read_text();a=s.index('structure FramedWeak');b=s.index('\ninductive Event',a)
result['cslib_composition_adapter_core']=measures(s[a:b])
# Separate control fixtures and axiom-print scaffolding from adapter logic.
result['adapter_code_roles']={}
for name,start in [('CSLibComposition','inductive Event'),('FramePort','abbrev fullFrame'),('SourceCSLibBridge','theorem bound_changes_domain')]:
 text=(ROOT/f'docs/research/reuse-adapters/{name}.lean').read_text()
 a=text.index(start);b=text.index('#print axioms',a)
 controls=measures(text[a:b])['code_lines']
 audits=sum(line.startswith('#print axioms') for line in text.splitlines())
 result['adapter_code_roles'][name]={'proof_and_interface':measures(text)['code_lines']-controls-audits,'controls':controls,'axiom_prints':audits}
assert hashlib.sha256((ROOT/'lake-manifest.json').read_bytes()).hexdigest()==snapshot['lake_manifest_sha256']
for name,pin in snapshot['reference_pins'].items():
 assert subprocess.check_output(['git','-C',str(ROOT/'external'/name),'rev-parse','HEAD'],text=True).strip()==pin['revision'],name
for m,r in snapshot['modules'].items():
 assert hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest()==r['sha256'],m
(OUT/'inventory-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
