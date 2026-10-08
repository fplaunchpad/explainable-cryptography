import ExplainableCrypto.Helios.Symbolic.SourceSameRealizations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem SourceName.withValue_map (n : SourceName) (f g : Nat → Nat) (v : Nat) :
    (n.map f g).withValue v = n.withValue v := by cases n <;> rfl

namespace Named
variable {V W : Type}

/-- Source variable renaming cannot conceal an opening with a different body
shape. No injectivity premise is needed: allocation never binds a variable. -/
theorem opens_rename_iff (a : Named V) (σ : V → W) (ρ : NameAssignment)
    (ns : List SourceName) (b : Extended W) :
    Opens (a.rename σ) ρ ns b ↔ ∃ c, Opens a ρ ns c ∧ b = c.rename σ := by
  constructor
  · intro h
    induction a generalizing W ρ ns b with
    | embed a =>
      cases h
      exact ⟨a.mapNames ρ.base ρ.channel,.embed a ρ,Extended.mapNames_rename a ρ.base ρ.channel σ⟩
    | par a c ih ij =>
      cases h with
      | par ha hc hd =>
        obtain ⟨a',ha',rfl⟩ := ih σ _ _ _ ha
        obtain ⟨c',hc',rfl⟩ := ij σ _ _ _ hc
        exact ⟨.par a' c',.par ha' hc' hd,rfl⟩
    | newName n a ih =>
      cases h with
      | newName _ v ha hf =>
        obtain ⟨a',ha',rfl⟩ := ih σ _ _ _ ha
        exact ⟨a',.newName n v ha' hf,rfl⟩
    | newVar a ih =>
      cases h with
      | newVar ha =>
        obtain ⟨a',ha',rfl⟩ := ih (Option.map σ) _ _ _ ha
        exact ⟨.newVar a',.newVar ha',rfl⟩
  · rintro ⟨c,hc,rfl⟩
    exact hc.rename σ

/-- Rename source binders/free names while retaining the exact allocated list
and Extended body. The outer assignment composes with the source permutations. -/
theorem opens_mapNames_iff (a : Named V) (e k : Nat ≃ Nat) (ρ : NameAssignment)
    (ns : List SourceName) (b : Extended V) :
    Opens (a.mapNames e k) ρ ns b ↔ Opens a (ρ ∘ SourceName.map e k) ns b := by
  induction a generalizing ρ ns with
  | embed a =>
    have he : (a.mapNames e k).mapNames ρ.base ρ.channel =
        a.mapNames (NameAssignment.base (ρ ∘ SourceName.map e k))
          (NameAssignment.channel (ρ ∘ SourceName.map e k)) := by
      rw [Extended.mapNames_comp]
      rfl
    constructor <;> intro h <;> cases h
    · rw [he]; exact .embed _ _
    · rw [← he]; exact .embed _ _
  | par a c ih ij =>
    constructor
    · intro h; cases h with
      | par ha hc hd => exact .par ((ih _ _ _).mp ha) ((ij _ _ _).mp hc) hd
    · intro h; cases h with
      | par ha hc hd => exact .par ((ih _ _ _).mpr ha) ((ij _ _ _).mpr hc) hd
  | newVar a ih =>
    constructor
    · intro h; cases h with
      | newVar ha => exact .newVar ((ih _ _ _).mp ha)
    · intro h; cases h with
      | newVar ha => exact .newVar ((ih _ _ _).mpr ha)
  | newName n a ih =>
    constructor
    · intro h; cases h with
      | newName _ v ha hf =>
        have hc := (ih _ _ _).mp ha
        rw [NameAssignment.update_comp] at hc
        simpa only [SourceName.withValue_map] using Opens.newName n v hc
          (by simpa only [SourceName.withValue_map] using hf)
    · intro h; cases h with
      | newName _ v ha hf =>
        have hc := ha
        rw [← NameAssignment.update_comp ρ e k n v] at hc
        simpa only [SourceName.withValue_map, mapNames] using Opens.newName (n.map e k) v
          ((ih _ _ _).mpr hc) (by simpa only [SourceName.withValue_map] using hf)

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
