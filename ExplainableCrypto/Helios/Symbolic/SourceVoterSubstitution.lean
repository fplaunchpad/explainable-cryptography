import ExplainableCrypto.Helios.Symbolic.SourceNamedInstantiation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type} {n : Nat}

namespace VoterRegisters

theorem map_comp (s : VoterRegisters n V) (σ : V → Term W) (τ : W → Term U) :
    (s.map σ).map τ = s.map (fun v => (σ v).subst τ) := by
  cases s
  simp only [map,Term.subst_subst]

theorem shift_map (s : VoterRegisters n V) (σ : V → Term W) :
    s.shift.map (liftSubst σ) = (s.map σ).shift := by
  simp only [shift,map_comp,Term.subst,liftSubst]

theorem ciphertext_subst (s : VoterRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.ciphertext j).subst σ = (s.map σ).ciphertext j := rfl

theorem proofRhs_subst (s : VoterRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.proofRhs j).subst (liftSubst σ) = (s.map σ).proofRhs j := by
  simp only [proofRhs,shift,map,Term.subst,Term.subst_subst,liftSubst]

theorem afterBind_subst (s : VoterRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.afterBind j).map (liftSubst (liftSubst σ)) = (s.map σ).afterBind j := by
  classical
  cases s
  dsimp only [afterBind,map,shift]
  congr 1 <;> try (funext k; by_cases hk : k=j)
  all_goals simp_all [Term.subst,Term.subst_subst,liftSubst]

end VoterRegisters

theorem voterAggregate_subst (s : VoterRegisters n V) (σ : V → Term W) :
    (voterAggregate s).subst σ = voterAggregate (s.map σ) := by
  simp only [voterAggregate,TermProgram.subst,VoterRegisters.shift,VoterRegisters.map,
    Term.subst_tuple,List.map_append,List.map_map,List.map_singleton,foldCandidates_subst,
    Term.subst_subst,Term.subst,liftSubst,Function.comp_def]

theorem voterComponents_subst (indices : List (Fin (n+1))) (s : VoterRegisters n V) (σ : V → Term W) :
    (voterComponents indices s).subst σ = voterComponents indices (s.map σ) := by
  induction indices generalizing V W with
  | nil => exact voterAggregate_subst s σ
  | cons j js ih => simp only [voterComponents,TermProgram.subst,VoterRegisters.ciphertext_subst,
      VoterRegisters.proofRhs_subst,ih,VoterRegisters.afterBind_subst]

theorem scopedVoterComponents_subst (nonces : Fin (n+1) → Nat) (indices : List (Fin (n+1)))
    (s : VoterRegisters n V) (σ : V → Term W) :
    (scopedVoterComponents nonces indices s).subst σ = scopedVoterComponents nonces indices (s.map σ) := by
  induction indices generalizing V W with
  | nil => simp only [scopedVoterComponents,ScopedTermProgram.ofProgram_subst,voterAggregate_subst]
  | cons j js ih => simp only [scopedVoterComponents,ScopedTermProgram.subst,VoterRegisters.ciphertext_subst,
      VoterRegisters.proofRhs_subst,ih,VoterRegisters.afterBind_subst]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
