import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineSpec

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Proof-side complete states at the actual operation boundaries. These are
not instructions or caller certificates; the run proves they are reached. -/
def phaseWords (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) : Fin 16 → Fin 38 → List Bool :=
  let u := (g^z0%p).bits
  let v := (alpha^(q-e)%p).bits
  let r := (answer p q g alpha e z0).bits
  let w0 := initialWords (inputWords p q g alpha e z0 frame)
  let w1 := Function.update (Function.update w0 1 e.bits) 9 (q-e).bits
  let w2 := Function.update w1 30 (uniformNatEncode z0)
  let w3 := Function.update (Function.update w2 30 []) 36 z0.bits
  let w4 := Function.update w3 34 g.bits
  let w5 := Function.update w4 29 p.bits
  let w6 := Function.update w5 23 u
  let w7 := Function.update (Function.update w6 23 []) 3 u
  let w8 := Function.update w7 34 alpha.bits
  let w9 := Function.update w8 36 (q-e).bits
  let w10 := Function.update w9 23 v
  let w11 := Function.update (Function.update w10 23 []) 31 v
  let w12 := Function.update (Function.update w11 3 []) 33 u
  let w13 := Function.update (Function.update w12 31 []) 23 r
  let w14 := Function.update (Function.update w13 23 []) 3 r
  let w15 := Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update w14 29 []) 33 []) 34 []) 36 []) 1 []) 9 []
  ![w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15]

def phaseCfg (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool)
    (phase : Fin 16) (label : Option (Fin size)) (memory : Fin 3) : Config :=
  ⟨label,memory,phaseWords p q g alpha e z0 frame phase⟩

theorem phase_start (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) :
    phaseCfg p q g alpha e z0 frame 0 (some 0) 2 = start (inputWords p q g alpha e z0 frame) := rfl

theorem phase_result (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) :
    phaseCfg p q g alpha e z0 frame 15 none 2 =
      result (answer p q g alpha e z0).bits (inputWords p q g alpha e z0 frame) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms phase_start
#print axioms phase_result
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
