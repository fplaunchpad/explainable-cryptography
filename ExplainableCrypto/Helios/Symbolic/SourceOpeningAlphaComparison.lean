import ExplainableCrypto.Helios.Symbolic.SourceOpeningParallelComparison

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem opening_alpha_assignments (a : Named V) (n m : SourceName) (e k : Nat ≃ Nat)
    (he : SourceName.map e k = Equiv.swap n m) (hf : m ∉ a.allNames)
    (ρ : NameAssignment) (v : Nat) :
    ∀ x ∈ a.freeNames, Function.update ρ n v x =
      (Function.update ρ m v ∘ SourceName.map e k) x := by
  intro x hx
  rw [he]
  have hm : x ≠ m := fun hxm => hf (hxm ▸ freeNames_subset_allNames a hx)
  by_cases hn : x=n
  · subst x; simp
  · simp [Equiv.swap_apply_of_ne_of_ne hn hm,hn,hm]

/-- Alpha conversion preserves a chosen allocation and its complete opened
body. The source freshness condition prevents capture of free names. -/
theorem opens_alpha_iff (a : Named V) (n m : SourceName) (e k : Nat ≃ Nat)
    (he : SourceName.map e k = Equiv.swap n m) (hf : m ∉ a.allNames)
    (hs : ∀ v, n.withValue v = m.withValue v) (ρ : NameAssignment)
    (ns : List SourceName) (b : Extended V) :
    Opens (.newName n a) ρ ns b ↔ Opens (.newName m (a.mapNames e k)) ρ ns b := by
  constructor
  · intro h; cases h with
    | newName _ v ha hg =>
      have hc := ha.names_congr _ (opening_alpha_assignments a n m e k he hf ρ v)
      rw [hs v] at hg ⊢
      exact .newName m v ((opens_mapNames_iff _ _ _ _ _ _).mpr hc) hg
  · intro h; cases h with
    | newName _ v ha hg =>
      have hc := ((opens_mapNames_iff _ _ _ _ _ _).mp ha).names_congr _
        (fun x hx => (opening_alpha_assignments a n m e k he hf ρ v x hx).symm)
      rw [← hs v] at hg ⊢
      exact .newName n v hc hg

theorem openingEquivalent_alphaBase (a : Named V) (n m : Nat)
    (hf : SourceName.base m ∉ a.allNames) :
    OpeningEquivalent (.newName (.base n) a)
      (.newName (.base m) (a.mapNames (Equiv.swap n m) id)) := by
  exact .of_opens_iff (opens_alpha_iff a (.base n) (.base m) (Equiv.swap n m)
    (Equiv.refl Nat) (SourceName.map_base_swap_eq n m) hf (fun _ => rfl))

theorem openingEquivalent_alphaChannel (a : Named V) (n m : Nat)
    (hf : SourceName.channel m ∉ a.allNames) :
    OpeningEquivalent (.newName (.channel n) a)
      (.newName (.channel m) (a.mapNames id (Equiv.swap n m))) := by
  exact .of_opens_iff (opens_alpha_iff a (.channel n) (.channel m) (Equiv.refl Nat)
    (Equiv.swap n m) (SourceName.map_channel_swap_eq n m) hf (fun _ => rfl))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
