import ExplainableCrypto.Helios.Symbolic.SourceTermProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Symbolic references used by the voter generator. Cipher/proof registers
start uninitialized and are filled by the two lets for each candidate. -/
structure VoterRegisters (n : Nat) (V : Type) where
  key : Term V
  nonces : Fin (n+1) → Term V
  votes : Fin (n+1) → Term V
  ciphertexts : Fin (n+1) → Term V
  proofs : Fin (n+1) → Term V

namespace VoterRegisters

def map (s : VoterRegisters n V) (σ : V → Term W) : VoterRegisters n W :=
  ⟨s.key.subst σ,fun j => (s.nonces j).subst σ,fun j => (s.votes j).subst σ,
    fun j => (s.ciphertexts j).subst σ,fun j => (s.proofs j).subst σ⟩

def shift (s : VoterRegisters n V) : VoterRegisters n (Option V) := s.map (fun v => .var (some v))

def ciphertext (s : VoterRegisters n V) (j : Fin (n+1)) : Term V :=
  .ternary .penc s.key (s.nonces j) (s.votes j)

def proof (s : VoterRegisters n V) (j : Fin (n+1)) : Term V :=
  .spk s.key (s.nonces j) (s.votes j) (s.ciphertext j)

def compute (s : VoterRegisters n V) (j : Fin (n+1)) : VoterRegisters n V :=
  { s with
    ciphertexts := Function.update s.ciphertexts j (s.ciphertext j)
    proofs := Function.update s.proofs j (s.proof j) }

/-- After the two lets, the ciphertext is Some None and its proof is None. -/
def afterBind (s : VoterRegisters n V) (j : Fin (n+1)) : VoterRegisters n (Option (Option V)) :=
  { s.shift.shift with
    ciphertexts := Function.update s.shift.shift.ciphertexts j (.var (some none))
    proofs := Function.update s.shift.shift.proofs j (.var none) }

def proofRhs (s : VoterRegisters n V) (j : Fin (n+1)) : Term (Option V) :=
  .spk s.shift.key (s.shift.nonces j) (s.shift.votes j) (.var none)

/-- An explicit expected register table for a processed index list. Values
outside that list remain unchanged, exposing skipped-candidate mutants. -/
noncomputable def completed (s : VoterRegisters n V) (indices : List (Fin (n+1))) : VoterRegisters n V :=
  { s with
    ciphertexts := fun j => if j ∈ indices then s.ciphertext j else s.ciphertexts j
    proofs := fun j => if j ∈ indices then s.proof j else s.proofs j }

theorem afterBind_map (s : VoterRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.afterBind j).map
      (extendEnv (extendEnv σ ((s.ciphertext j).subst σ))
        ((s.proofRhs j).subst (extendEnv σ ((s.ciphertext j).subst σ)))) =
      (s.map σ).compute j := by
  classical
  cases s
  dsimp only [afterBind,map,shift,compute]
  congr 1 <;> try (funext k; by_cases hk : k=j)
  all_goals simp_all [map,shift,ciphertext,proofRhs,proof,
    Term.subst,Term.subst_subst,extendEnv]

theorem completed_compute (s : VoterRegisters n V) (j : Fin (n+1)) (indices : List (Fin (n+1))) :
    (s.compute j).completed indices = s.completed (j::indices) := by
  classical
  cases s
  dsimp only [compute,completed]
  congr 1 <;> funext k <;> by_cases hk : k=j <;> by_cases hm : k ∈ indices
  all_goals simp [ciphertext,proof,hk,hm]

/-- Every ciphertext and every complete proof contributes to the final tuple;
the last field binds aggregate nonce, vote and saved ciphertext product. -/
def aggregateValue (s : VoterRegisters n V) : Term V :=
  Term.tuple ((List.finRange (n+1)).map s.ciphertexts ++ (List.finRange (n+1)).map s.proofs ++
    [.spk s.key (foldCandidates .compose s.nonces) (foldCandidates .add s.votes)
      (foldCandidates .mul s.ciphertexts)])

end VoterRegisters
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
