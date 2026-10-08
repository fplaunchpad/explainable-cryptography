#!/usr/bin/env python3
"""Kernel routing campaign against the original instructions.

Run `lake build ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextControls`
then `python3 scripts/check_nonce_ciphertext_kernel.py`. Checks all 810 independent
fixtures plus the imported nine kernel controls (six actual-code mutations).
Uses fixtures from check_nonce_ciphertext.py without launching its native runner.
Reports/logs/generated source go under tmp/concrete-helios/reproduction.
Production-import promotion preserves the prior campaign; it is not a new run."""
import hashlib
import json
import subprocess
from check_nonce_ciphertext import OUT, ROOT, HEADER, fixtures, expected, SEEDS

def word(raw): return '['+','.join('true' if b=='1' else 'false' for b in raw)+']'

def generated_source(cases):
    source='import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextControls\n'+'''
namespace ExplainableCrypto.Helios.Computational.NonceRoutingKernelGate
open PrimeNonceCiphertextMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
example : ∀ l, BitOracleMachine.localCost (program l) ≤ 6 := by decide +kernel
private def observed (fuel : Nat) (cfg : Config) :=
  let out := tick^[fuel] cfg
  (out.l,out.var.val,List.ofFn out.stk)
'''
    for i,c in enumerate(cases):
        args=' '.join(word(c[k]) for k in ('record','first','second','samplerMod','context','modulus','g','pk'))
        want='['+','.join(word(w) for w in expected(c))+']'
        source+=f'example : observed {7*c["n"].bit_length()+9} (start {args} {str(c["vote"]).lower()}) = (none,2,{want}) := by decide +kernel\n'
        if (i+1)%64==0: source+=f'#eval IO.println "kernel checked {i+1}/{len(cases)}"\n'
    source+='end ExplainableCrypto.Helios.Computational.NonceRoutingKernelGate\n'
    return source

def main():
    cases=fixtures()
    source=generated_source(cases)
    path=OUT/'NonceRoutingKernelGate.lean';path.write_text(source)
    log=OUT/'nonce-ciphertext-kernel-gate.log'
    with log.open('w') as stream:
        run=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    text=log.read_text()
    report=dict(status='pass' if run.returncode==0 and 'sorry' not in text and 'error:' not in text else 'failed',
                cases=len(cases),seeds=SEEDS,discarded=0,gaveUp=0,
                source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                controller_sha256=hashlib.sha256(HEADER.read_bytes()).hexdigest(),
                controls='same nine literal kernel controls including six actual-code mutations',
                scope='complete state at independently computed clock; every local instruction cost at most six')
    (OUT/'nonce-ciphertext-kernel-gate.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)
    if report['status']!='pass':raise SystemExit(1)
if __name__=='__main__':main()
