import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticEquivalence

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat} {a b : Named (Fin handles)}

/-- Coherent alpha conversion moves both actual frame presentations with one
base/channel permutation. Complete values and their old handle indices remain. -/
theorem RepresentsFrame.common_fresh {φ ψ : Frame restricted handles}
    (ha : a.RepresentsFrame hidden φ) (hb : b.RepresentsFrame hidden ψ) (avoid : Finset SourceName) :
    ∃ e k : Nat ≃ Nat,
      a.RepresentsFrame (hidden.image k) (φ.mapNames e) ∧
      b.RepresentsFrame (hidden.image k) (ψ.mapNames e) ∧
      (∀ n ∈ restrictionNames (hidden.image k) (restricted.image e), n ∉ avoid) ∧
      (∀ n ∈ avoid, n ∉ restrictionNames hidden restricted → n.map e k = n) := by
  obtain ⟨e,k,hφ,hψ,hf,hfix⟩ := exists_common_fresh_policy hidden restricted
    (.embed (Extended.activeFrame φ)) (.embed (Extended.activeFrame ψ)) avoid
  have hφ' : Structural (canonicalFrame hidden φ) (canonicalFrame (hidden.image k) (φ.mapNames e)) := by
    simpa only [canonicalFrame,Named.mapNames,Extended.activeFrame_mapNames] using hφ
  have hψ' : Structural (canonicalFrame hidden ψ) (canonicalFrame (hidden.image k) (ψ.mapNames e)) := by
    simpa only [canonicalFrame,Named.mapNames,Extended.activeFrame_mapNames] using hψ
  exact ⟨e,k,ha.trans hφ',hb.trans hψ',hf,hfix⟩

/-- All-public-recipe equivalence remains attached to a common presentation
whose bound names avoid any finite external test support. -/
theorem StaticEq.fresh_witness (h : StaticEq a b) (avoid : Finset SourceName) :
    ∃ (hidden restricted : Finset Nat) (φ ψ : Frame restricted handles),
      a.RepresentsFrame hidden φ ∧ b.RepresentsFrame hidden ψ ∧ φ.StaticEq ψ ∧
      ∀ n ∈ restrictionNames hidden restricted, n ∉ avoid := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,he⟩ := h
  obtain ⟨e,k,ha',hb',hf,_⟩ := ha.common_fresh hb avoid
  exact ⟨hidden.image k,restricted.image e,φ.mapNames e,ψ.mapNames e,ha',hb',he.mapNames e,hf⟩

/-- Arbitrary fixed literal recipes are tested after coherently freshening
both frame presentations. The same original r and s occur in the conclusion. -/
theorem StaticEq.test_witness (h : StaticEq a b) (r s : Recipe handles) :
    ∃ (hidden restricted : Finset Nat) (φ ψ : Frame restricted handles),
      a.RepresentsFrame hidden φ ∧ b.RepresentsFrame hidden ψ ∧
      r.Public restricted ∧ s.Public restricted ∧ φ.StaticEq ψ ∧
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,he,hf⟩ := h.fresh_witness
    ((r.nameSupport ∪ s.nameSupport).image SourceName.base)
  have hr : r.Public restricted := by
    apply (Term.public_iff_nameSupport r restricted).mpr
    intro n hn hn'
    exact hf (.base n) ((base_mem_restrictionNames n hidden restricted).mpr hn')
      (Finset.mem_image.mpr ⟨n,Finset.mem_union_left _ hn,rfl⟩)
  have hs : s.Public restricted := by
    apply (Term.public_iff_nameSupport s restricted).mpr
    intro n hn hn'
    exact hf (.base n) ((base_mem_restrictionNames n hidden restricted).mpr hn')
      (Finset.mem_image.mpr ⟨n,Finset.mem_union_right _ hn,rfl⟩)
  exact ⟨hidden,restricted,φ,ψ,ha,hb,hr,hs,he,he r s hr hs⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
