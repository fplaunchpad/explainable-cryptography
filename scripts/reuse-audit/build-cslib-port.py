from pathlib import Path
import re,subprocess,os,shutil,time,json
root=Path(__file__).resolve().parents[2]; src=root/'external/CSLib'; dst=root/'output/reuse-audit/cslib-main-toolchain';lib=dst/'lib';dst.mkdir(exist_ok=True);lib.mkdir(exist_ok=True)
seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);p=src/(m.replace('.','/')+'.lean')
 if not p.exists():return
 for d in re.findall(r'^(?:public\s+)?import\s+([\w.]+)',p.read_text(),re.M):
  if d.startswith('Cslib.'):visit(d)
 order.append(m)
visit('Cslib.Foundations.Semantics.LTS.Bisimulation')
env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
lean=subprocess.check_output(['lake','env','which','lean'],text=True).strip()
results=[]
for m in order:
 rel=Path(m.replace('.','/')+'.lean');p=dst/rel;p.parent.mkdir(parents=True,exist_ok=True)
 text=(src/rel).read_text()
 if m.endswith('.Bisimulation'):
  old='(Deterministic.bisim_tfae s₁ s₂).out 1 2'
  assert text.count(old)==1
  text=text.replace(old,'(Deterministic.bisim_tfae (lts₁ := lts₁) (lts₂ := lts₂) s₁ s₂).out 0 1')
 if not p.exists() or p.read_text()!=text:p.write_text(text)
 out=lib/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists() and out.stat().st_mtime>=p.stat().st_mtime:
  results.append({'module':m,'seconds':0,'exit_code':0,'output':'reused already checked object'});continue
 start=time.monotonic();r=subprocess.run([lean,str(rel),'-o',str(out)],cwd=dst,env=env,capture_output=True,text=True)
 results.append({'module':m,'seconds':round(time.monotonic()-start,3),'exit_code':r.returncode,'output':r.stdout+r.stderr})
 print(m,r.returncode,results[-1]['seconds'],flush=True)
 if r.returncode:
  print(r.stdout+r.stderr,flush=True);break
(root/'output/reuse-audit/cslib-main-toolchain-build.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(results[-1]['exit_code'])
