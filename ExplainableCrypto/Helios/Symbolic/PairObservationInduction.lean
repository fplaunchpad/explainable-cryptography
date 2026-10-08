import ExplainableCrypto.Helios.Symbolic.PairObservationOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Pair reconstruction is used only when the other term has an actual pair
value. No global eta equation is added to E. -/
theorem pair_equality_iff_projections (a b t : Term V)
    (ht : ∃ x y, EqE t (.binary .pair x y)) :
    EqE (.binary .pair a b) t ↔ EqE a (.unary .fst t) ∧ EqE b (.unary .snd t) := by
  obtain ⟨x, y, ht⟩ := ht
  have he := pair_reconstruction_of_value ht
  exact ⟨fun h => (EqE.pair_iff _ _ _ _).mp (h.trans he),
    fun h => ((EqE.pair_iff _ _ _ _).mpr h).trans he.symm⟩

/-- Even when the other recipe is a long projected ballot tail, comparison of
its projections with the constructed fields is below the original pair size. -/
theorem constructed_pair_equality_transfer (φ ψ : Frame restricted handles) (a b s : Recipe handles)
    (hp : (Term.binary .pair a b).Public restricted) (hs : s.Public restricted)
    (hφ : ∃ x y, EqE (φ.eval s) (.binary .pair x y))
    (hψ : ∃ x y, EqE (ψ.eval s) (.binary .pair x y))
    (hobs : φ.ObservationsBelow ψ ((Term.binary .pair a b).nodeCount + s.nodeCount)) :
    EqE (φ.eval (.binary .pair a b)) (φ.eval s) ↔
      EqE (ψ.eval (.binary .pair a b)) (ψ.eval s) := by
  have ha := hobs a (.unary .fst s) hp.1 hs
    (by have := b.nodeCount_pos; simp only [Term.nodeCount]; omega)
  have hb := hobs b (.unary .snd s) hp.2 hs
    (by have := a.nodeCount_pos; simp only [Term.nodeCount]; omega)
  exact (pair_equality_iff_projections _ _ _ hφ).trans
    ((and_congr ha hb).trans (pair_equality_iff_projections _ _ _ hψ).symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The exact pair-form comparison matrix uses smaller public tests whenever
one side is constructed, and fresh tail identity when both sides are tails. -/
theorem pair_form_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : PairObservationForm n r) (hfs : PairObservationForm n s)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  rcases hfr with ⟨a, b, rfl⟩ | ⟨i, k, hk, rfl⟩
  · exact constructed_pair_equality_transfer _ _ a b s hr hs
      (hfs.pair_value ns false left right) (hfs.pair_value ns true left right) hobs
  · rcases hfs with ⟨a, b, rfl⟩ | ⟨j, l, hl, rfl⟩
    · have ht := constructed_pair_equality_transfer (frame ns false left right) (frame ns true left right)
        a b ((Term.var i.succ).drop k) hs hr
        (ballot_tail_pair_value ns false left right i k hk)
        (ballot_tail_pair_value ns true left right i k hk)
        (by simpa only [Nat.add_comm] using hobs)
      exact ⟨fun he => (ht.mp he.symm).symm, fun he => (ht.mpr he.symm).symm⟩
    · exact (ballot_tail_equality_iff ns hf false left right i j k l hk hl).trans
        (ballot_tail_equality_iff ns hf true left right i j k l hk hl).symm

/-- The pair-valued induction branch derives exact origins and second-world
pair-valuedness from first-world minima. The global smaller-test premise remains
explicit; arbitrary minimum replacement across worlds is not assumed. -/
theorem minimum_pair_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {a b c d : Ground}
    (her : EqE ((frame ns false left right).eval r) (.binary .pair a b))
    (hes : EqE ((frame ns false left right).eval s) (.binary .pair c d))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) :=
  pair_form_equality_swap ns hf left right r s hr.isPublic hs.isPublic
    (minimum_pair_observation_form ns false left right ns.restricted r hr her)
    (minimum_pair_observation_form ns false left right ns.restricted s hs hes) hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
