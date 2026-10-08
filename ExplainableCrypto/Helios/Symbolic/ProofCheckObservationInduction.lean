import ExplainableCrypto.Helios.Symbolic.AtomicObservationInduction
import ExplainableCrypto.Helios.Symbolic.MinimalProofChecking

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Stuck proof checks retain all three ordered arguments under full E. Both
no-match premises are essential because successful checks all return ok. -/
theorem EqE.proof_check_iff_of_no_match (a b c d e f : Term V)
    (hl : ¬ ProofCheckMatch a b c) (hr : ¬ ProofCheckMatch d e f) :
    EqE (.ternary .checkspk a b c) (.ternary .checkspk d e f) ↔
      EqE a d ∧ EqE b e ∧ EqE c f := by
  constructor
  · intro he
    obtain ⟨w, hleft, hright⟩ := (eqE_iff_join _ _).mp he
    rcases hleft.proof_check_cases with ⟨a', b', c', ha, hb, hc, hw⟩ | ⟨hm, _⟩
    · rcases hright.proof_check_cases with ⟨d', e', f', hd, he', hf, hw'⟩ | ⟨hm, _⟩
      · have hargs := ((BaseEq.ternary_iff .checkspk .checkspk _ _ _ _ _ _).mp (hw.symm.trans hw')).2
        exact ⟨ha.sound.trans (hargs.1.sound.trans hd.sound.symm),
          hb.sound.trans (hargs.2.1.sound.trans he'.sound.symm),
          hc.sound.trans (hargs.2.2.sound.trans hf.sound.symm)⟩
      · exact False.elim (hr hm)
    · exact False.elim (hl hm)
  · rintro ⟨ha, hb, hc⟩
    exact .ternary .checkspk ha hb hc

/-- The whole-check comparison with public ok detects any new E8/E9 match in
the destination frame, provided that this specific test is below the bound. -/
theorem Frame.ObservationsBelow.check_failure {φ ψ : Frame restricted handles} {bound : Nat}
    (hobs : φ.ObservationsBelow ψ bound) (a b c : Recipe handles)
    (hp : (Term.ternary .checkspk a b c).Public restricted)
    (hn : ¬ ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c))
    (hsize : (Term.ternary .checkspk a b c).nodeCount + 1 < bound) :
    ¬ ProofCheckMatch (ψ.eval a) (ψ.eval b) (ψ.eval c) := by
  intro hm
  have ht := hobs (.ternary .checkspk a b c) (.const .ok) hp trivial hsize
  exact hn ((EqE.check_ok_iff _ _ _).mp (ht.mpr hm.reduces.sound))

/-- Two first-frame minimum checking recipes cannot succeed. The smaller ok
probes preserve that fact; the three smaller argument tests then transfer their
full-E equality. No destination minimum or no-match premise is assumed. -/
theorem minimum_proof_check_equality_transfer (φ ψ : Frame restricted handles)
    (a b c d e f : Recipe handles)
    (hl : MinimalRecipe restricted φ.value (.ternary .checkspk a b c))
    (hr : MinimalRecipe restricted φ.value (.ternary .checkspk d e f))
    (hobs : φ.ObservationsBelow ψ
      ((Term.ternary .checkspk a b c).nodeCount + (Term.ternary .checkspk d e f).nodeCount)) :
    EqE (φ.eval (.ternary .checkspk a b c)) (φ.eval (.ternary .checkspk d e f)) ↔
      EqE (ψ.eval (.ternary .checkspk a b c)) (ψ.eval (.ternary .checkspk d e f)) := by
  have hnl := hl.no_proof_check_match a b c
  have hnr := hr.no_proof_check_match d e f
  have hnl' := hobs.check_failure a b c hl.isPublic hnl
    (by have := d.nodeCount_pos; simp only [Term.nodeCount]; omega)
  have hnr' := hobs.check_failure d e f hr.isPublic hnr
    (by have := a.nodeCount_pos; simp only [Term.nodeCount]; omega)
  have ha := hobs a d hl.isPublic.1 hr.isPublic.1 (by simp only [Term.nodeCount]; omega)
  have hb := hobs b e hl.isPublic.2.1 hr.isPublic.2.1 (by simp only [Term.nodeCount]; omega)
  have hc := hobs c f hl.isPublic.2.2 hr.isPublic.2.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hnl hnr).trans
    ((and_congr ha (and_congr hb hc)).trans
      (EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hnl' hnr').symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Initial-frame specialization for syntactic checking recipes. StuckCheckOrigins
subsequently derives these forms for arbitrary minimum recipes with stuck-check values. -/
theorem minimum_proof_check_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b c d e f : Recipe 3)
    (hl : MinimalRecipe ns.restricted (frame ns false left right).value (.ternary .checkspk a b c))
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value (.ternary .checkspk d e f))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      ((Term.ternary .checkspk a b c).nodeCount + (Term.ternary .checkspk d e f).nodeCount)) :
    EqE ((frame ns false left right).eval (.ternary .checkspk a b c))
      ((frame ns false left right).eval (.ternary .checkspk d e f)) ↔
    EqE ((frame ns true left right).eval (.ternary .checkspk a b c))
      ((frame ns true left right).eval (.ternary .checkspk d e f)) :=
  minimum_proof_check_equality_transfer _ _ a b c d e f hl hr hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
