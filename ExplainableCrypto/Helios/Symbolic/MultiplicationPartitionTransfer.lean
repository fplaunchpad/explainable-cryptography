import ExplainableCrypto.Helios.Symbolic.MinimumMultiplicationPartitions

namespace ExplainableCrypto.Helios.Symbolic
variable {V W U : Type} {restricted : Finset Nat}

section Reconstruction
local instance partitionMulSemigroup : CommSemigroup (FullClass U) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary .mul a b).fullClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := fullSetoid U) (.binary .mul ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := fullSetoid U) (.equation (.assoc .mul trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := fullSetoid U) (.equation (.comm .mul trivial a b))

private def evalBase (τ : V → Term U) : BaseClass V → FullClass U :=
  Quotient.lift (fun r => (r.subst τ).fullClass)
    (fun _ _ h => Quotient.sound (s := fullSetoid U) (h.sound.subst τ))
private theorem evalBase_baseClass (τ : V → Term U) (r : Term V) :
    evalBase τ r.baseClass = (r.subst τ).fullClass := rfl

private def foldFactors (τ : V → Term U) (s : Multiset (BaseClass V)) : WithOne (FullClass U) :=
  (s.map (fun q => (evalBase τ q : WithOne (FullClass U)))).prod
private theorem fold_add (τ : V → Term U) (a b : Multiset (BaseClass V)) :
    foldFactors τ (a+b) = foldFactors τ a * foldFactors τ b := by
  simp [foldFactors, Multiset.prod_add]
private theorem fold_term (τ : V → Term U) (r : Term V) :
    foldFactors τ r.mulFactors = ((r.subst τ).fullClass : WithOne (FullClass U)) := by
  induction r with
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.mulFactors, fold_add, ha, hb]; rfl)
      | simp [Term.mulFactors, foldFactors, evalBase_baseClass]
  | _ => simp [Term.mulFactors, foldFactors, evalBase_baseClass]
private theorem fold_pieces (τ : V → Term U) (xs : Multiset (Term V × Term W)) :
    foldFactors τ (xs.map (fun p => p.1.mulFactors)).sum =
      (xs.map (fun p => ((p.1.subst τ).fullClass : WithOne (FullClass U)))).prod := by
  induction xs using Multiset.induction_on with
  | empty => simp [foldFactors]
  | cons x xs ih => simp only [Multiset.map_cons, Multiset.sum_cons, fold_add, fold_term, ih, Multiset.prod_cons]

/-- Exact source factor accounting reassembles the original recipes in any
substitution once their partition-piece class bags agree. No unit is introduced. -/
theorem MultiplicationPartition.eqE_of_piece_bags {σ : V → Term W} {r s : Term V} {a b : Term W}
    (p : MultiplicationPartition restricted σ r a) (q : MultiplicationPartition restricted σ s b)
    (τ : V → Term U)
    (he : p.pieces.map (fun x => (x.1.subst τ).fullClass) = q.pieces.map (fun x => (x.1.subst τ).fullClass)) :
    EqE (r.subst τ) (s.subst τ) := by
  have hp := congrArg (foldFactors τ) p.sourceFactors
  have hq := congrArg (foldFactors τ) q.sourceFactors
  rw [fold_pieces, fold_term] at hp hq
  have hh := congrArg (fun xs : Multiset (FullClass U) =>
    (xs.map (fun x : FullClass U => (x : WithOne (FullClass U)))).prod) he
  simp only [Multiset.map_map, Function.comp_def] at hh
  rw [hp, hq] at hh
  exact (fullClass_eq_iff _ _).mp (WithOne.coe_injective hh)
end Reconstruction

/-- Equal normal endpoints match partition factors. A supplied transfer of the
public piece equalities then reassembles equality of the whole source recipes. -/
theorem MultiplicationPartition.transfer_normal_equality {σ : V → Term W} {r s : Term V} {a b : Term W}
    (p : MultiplicationPartition restricted σ r a) (q : MultiplicationPartition restricted σ s b)
    (ha : Irreducible a) (hb : Irreducible b) (τ : V → Term U)
    (ht : ∀ x ∈ p.pieces, ∀ y ∈ q.pieces,
      EqE (x.1.subst σ) (y.1.subst σ) → EqE (x.1.subst τ) (y.1.subst τ))
    (he : EqE (r.subst σ) (s.subst σ)) : EqE (r.subst τ) (s.subst τ) := by
  have he' := (irreducible_eqE_iff_base ha hb).mp (p.value.symm.trans (he.trans q.value))
  have hbag := p.targetFactors.trans (he'.mul_factors.trans q.targetFactors.symm)
  have hr : Multiset.Rel (fun x y : Term V × Term W => x.2.baseClass = y.2.baseClass) p.pieces q.pieces := by
    rw [← Multiset.rel_map, Multiset.rel_eq]
    exact hbag
  apply p.eqE_of_piece_bags q τ
  rw [← Multiset.rel_eq, Multiset.rel_map]
  exact hr.mono (fun x hx y hy hxy => (fullClass_eq_iff _ _).mpr
    (ht x hx y hy ((p.values x hx).trans (((baseClass_eq_iff _ _).mp hxy).sound.trans (q.values y hy).symm))))

end ExplainableCrypto.Helios.Symbolic
