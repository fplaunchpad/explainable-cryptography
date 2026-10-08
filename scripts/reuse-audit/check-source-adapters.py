#!/usr/bin/env python3
"""Check isolated source adapters against the frozen main toolchain and CSLib port."""
from pathlib import Path
import subprocess,os,json,time
root=Path(__file__).resolve().parents[2]
dst=root/'output/reuse-audit/cslib-main-toolchain';lib=dst/'lib'
env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
lean=subprocess.check_output(['lake','env','which','lean'],cwd=root,text=True).strip()
results=[]
for name in ['CSLibComposition','SourceCSLibBridge']:
 source=(root/f'docs/research/reuse-adapters/{name}.lean').read_text()
 (dst/f'{name}.lean').write_text(source)
 start=time.monotonic()
 r=subprocess.run([lean,f'{name}.lean','-o',str(lib/f'{name}.olean')],cwd=dst,env=env,capture_output=True,text=True)
 results.append(dict(module=name,seconds=round(time.monotonic()-start,3),exit_code=r.returncode,output=r.stdout+r.stderr))
 print(name,r.returncode,results[-1]['seconds'],r.stdout+r.stderr,flush=True)
 if r.returncode:break
(root/'output/reuse-audit/source-adapter-checks.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(results[-1]['exit_code'])
