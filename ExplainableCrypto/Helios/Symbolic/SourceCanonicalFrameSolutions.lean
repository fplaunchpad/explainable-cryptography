import ExplainableCrypto.Helios.Symbolic.SourceFrameSolutionStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

/-- An outer restriction prefix allows exactly the atom assignments that keep
all unbound base names fixed. Channel restrictions do not affect frame terms. -/
theorem models_restrictNames (ns : List SourceName) (a : Named V)
    (ρ : Nat → Nat) (env : V → Ground) :
    (restrictNames ns a).Models ρ env ↔
      ∃ τ : Nat → Nat, (∀ n, SourceName.base n ∉ ns → τ n = ρ n) ∧ a.Models τ env := by
  induction ns generalizing ρ with
  | nil =>
    simp only [restrictNames,List.foldr,List.not_mem_nil,not_false_eq_true,forall_true_left]
    constructor
    · intro h; exact ⟨ρ,fun _ => rfl,h⟩
    · rintro ⟨τ,hτ,h⟩; rw [funext hτ] at h; exact h
  | cons n ns ih =>
    cases n with
    | channel c =>
      simpa [restrictNames,Models] using ih ρ
    | base c =>
      change (∃ k, (restrictNames ns a).Models (Function.update ρ c k) env) ↔ _
      simp only [ih]
      constructor
      · rintro ⟨k,τ,hτ,ha⟩
        refine ⟨τ,?_,ha⟩
        intro n hn
        have hnc : n ≠ c := fun he => hn (by simp [he])
        have hns : SourceName.base n ∉ ns := fun hm => hn (List.mem_cons_of_mem _ hm)
        simpa only [Function.update_of_ne hnc] using hτ n hns
      · rintro ⟨τ,hτ,ha⟩
        refine ⟨τ c,τ,?_,ha⟩
        intro n hn
        by_cases hnc : n=c
        · simp [hnc]
        · rw [Function.update_of_ne hnc]
          exact hτ n (by simp only [List.mem_cons,SourceName.base.injEq,hnc,false_or]; exact hn)

theorem canonicalFrame_models_iff (φ : Frame restricted handles) (env : Fin handles → Ground) :
    (canonicalFrame hidden φ).Models id env ↔
      ∃ ρ : Nat → Nat, (∀ n, n ∉ restricted → ρ n = n) ∧
        ∀ i, EqE (env i) ((φ.value i).mapNames ρ) := by
  simp only [canonicalFrame,models_restrictNames,base_mem_restrictionNames,
    Models,Extended.activeFrame_mapNames,Extended.activeFrame_satisfies_iff,Frame.mapNames,id_eq]

/-- Canonical frames always have their literal full ground values as a solution. -/
theorem canonicalFrame_models (φ : Frame restricted handles) :
    (canonicalFrame hidden φ).Models id φ.value := by
  apply (canonicalFrame_models_iff φ φ.value).mpr
  exact ⟨id,fun _ _ => rfl,fun i => by rw [Term.mapNames_id]; exact .refl _⟩

/-- Equality must hold for every solution, rather than just one convenient
assignment of the restricted atoms. This is not a deduction relation. -/
def ValidEquation (a : Named V) (r s : Term V) : Prop :=
  ∀ env : V → Ground, a.Models id env → EqE (r.subst env) (s.subst env)

theorem ValidEquation.structural {a b : Named V} {r s : Term V}
    (h : a.ValidEquation r s) (hab : Structural a b) : b.ValidEquation r s :=
  fun env hm => h env ((hab.models id env).mpr hm)

theorem validEquation_structural_iff {a b : Named V} (hab : Structural a b) (r s : Term V) :
    a.ValidEquation r s ↔ b.ValidEquation r s :=
  ⟨fun h => h.structural hab,fun h => h.structural hab.symm⟩

theorem validEquation_frameOf_iff (a : Named V) (r s : Term V) :
    a.frameOf.ValidEquation r s ↔ a.ValidEquation r s := by
  simp only [ValidEquation,models_frameOf]

/-- Exact public observation agreement. Noninjective private-name assignments
are harmless under universal quantification: full E maps forward, and the
identity solution proves the reverse direction. -/
theorem canonicalFrame_validEquation_iff (φ : Frame restricted handles) (r s : Recipe handles)
    (hr : r.Public restricted) (hs : s.Public restricted) :
    (canonicalFrame hidden φ).ValidEquation r s ↔ EqE (φ.eval r) (φ.eval s) := by
  constructor
  · intro h; exact h φ.value (canonicalFrame_models φ)
  · intro he env hm
    obtain ⟨ρ,hfix,hval⟩ := (canonicalFrame_models_iff φ env).mp hm
    have fixed (t : Recipe handles) (ht : t.Public restricted) : t.mapNames ρ = t :=
      t.mapNames_eq_of_fixed ρ (fun n hn => hfix n ((Term.public_iff_nameSupport t restricted).mp ht n hn))
    have hmap := he.mapNames ρ
    simp only [Frame.eval,Term.mapNames_subst,fixed r hr,fixed s hs] at hmap
    exact (r.subst_congr env (fun i => (φ.value i).mapNames ρ) hval).trans
      (hmap.trans (s.subst_congr env (fun i => (φ.value i).mapNames ρ) hval).symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
