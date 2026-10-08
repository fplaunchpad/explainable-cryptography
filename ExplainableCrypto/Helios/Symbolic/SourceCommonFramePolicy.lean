import ExplainableCrypto.Helios.Symbolic.SourceCanonicalPolicyPadding

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- A permutation fixing a literal cannot introduce it into a full frame
where it did not occur before. -/
theorem Frame.nameSupport_mapNames_absent (φ : Frame restricted handles) (e : Nat ≃ Nat) (n : Nat)
    (hn : n ∉ φ.nameSupport) (he : e n=n) : n ∉ (φ.mapNames e).nameSupport := by
  intro h
  obtain ⟨i,hi⟩ := (Frame.mem_nameSupport _ _).mp h
  change n ∈ ((φ.value i).mapNames e).nameSupport at hi
  rw [Term.nameSupport_mapNames] at hi
  obtain ⟨m,hm,hmn⟩ := Finset.mem_image.mp hi
  have hmn' : m=n := e.injective (hmn.trans he.symm)
  exact hn ((Frame.mem_nameSupport φ n).mpr ⟨i,hmn' ▸ hm⟩)

namespace Historical.General.Source.Named
variable {a b c d : Named (Fin handles)}

/-- Two actual presentations can share a policy once its added names are
unused in each opposite frame. This retains full source structural witnesses. -/
theorem RepresentsFrame.common_policy {left right hidden₁ hidden₂ : Finset Nat}
    {φ : Frame left handles} {ψ : Frame right handles}
    (ha : a.RepresentsFrame hidden₁ φ) (hb : b.RepresentsFrame hidden₂ ψ)
    (hφ : ∀ n ∈ right, n ∉ left → n ∉ φ.nameSupport)
    (hψ : ∀ n ∈ left, n ∉ right → n ∉ ψ.nameSupport) (hidden : Finset Nat) :
    a.RepresentsFrame hidden (φ.withPolicy (left ∪ right)) ∧
      b.RepresentsFrame hidden (ψ.withPolicy (left ∪ right)) := by
  refine ⟨ha.pad_policy hidden right hφ,?_⟩
  simpa only [RepresentsFrame,canonicalFrame,Frame.withPolicy,Extended.activeFrame,
    Finset.union_comm right left] using hb.pad_policy hidden left hψ

/-- Any two independently chosen static-equivalence witnesses admit one
common base policy and actual source presentations. This aligns policies; it
does not identify the two middle frames or assume their equality tests agree. -/
theorem StaticEq.common_policy (hab : StaticEq a b) (hcd : StaticEq c d) :
    ∃ (policy : Finset Nat) (φ ψ χ δ : Frame policy handles),
      a.RepresentsFrame ∅ φ ∧ b.RepresentsFrame ∅ ψ ∧
      c.RepresentsFrame ∅ χ ∧ d.RepresentsFrame ∅ δ ∧
      φ.StaticEq ψ ∧ χ.StaticEq δ := by
  obtain ⟨hidden₁,left,φ,ψ,ha,hb,he₁⟩ := hab
  obtain ⟨hidden₂,right,χ,δ,hc,hd,he₂⟩ := hcd
  let avoid₁ := (χ.nameSupport ∪ (δ.nameSupport ∪ right)).image SourceName.base
  obtain ⟨e,k,ha',hb',hf₁,_⟩ := ha.common_fresh hb avoid₁
  let left' := left.image e
  let φ' := φ.mapNames e
  let ψ' := ψ.mapNames e
  have first_fresh (n : Nat) (hn : n ∈ left') :
      n ∉ χ.nameSupport ∧ n ∉ δ.nameSupport ∧ n ∉ right := by
    have hh := hf₁ (.base n) ((base_mem_restrictionNames n _ _).mpr hn)
    have hf : n ∉ χ.nameSupport ∪ (δ.nameSupport ∪ right) := fun hm =>
      hh (Finset.mem_image.mpr ⟨n,hm,rfl⟩)
    simpa only [Finset.mem_union,not_or] using hf
  let avoid₂ := (φ'.nameSupport ∪ (ψ'.nameSupport ∪ left')).image SourceName.base
  obtain ⟨e',k',hc',hd',hf₂,hfix⟩ := hc.common_fresh hd avoid₂
  let right' := right.image e'
  let χ' := χ.mapNames e'
  let δ' := δ.mapNames e'
  have second_fresh (n : Nat) (hn : n ∈ right') :
      n ∉ φ'.nameSupport ∧ n ∉ ψ'.nameSupport := by
    have hh := hf₂ (.base n) ((base_mem_restrictionNames n _ _).mpr hn)
    have hf : n ∉ φ'.nameSupport ∪ (ψ'.nameSupport ∪ left') := fun hm =>
      hh (Finset.mem_image.mpr ⟨n,hm,rfl⟩)
    have hx : n ∉ φ'.nameSupport ∧ n ∉ ψ'.nameSupport ∧ n ∉ left' := by
      simpa only [Finset.mem_union,not_or] using hf
    exact ⟨hx.1,hx.2.1⟩
  have first_stays_fresh (n : Nat) (hn : n ∈ left') :
      n ∉ χ'.nameSupport ∧ n ∉ δ'.nameSupport := by
    have hfirst := first_fresh n hn
    have he : e' n=n := SourceName.base.inj (hfix (.base n)
      (Finset.mem_image.mpr ⟨n,Finset.mem_union_right _ (Finset.mem_union_right _ hn),rfl⟩)
      (fun hm => hfirst.2.2 ((base_mem_restrictionNames n _ _).mp hm)))
    exact ⟨χ.nameSupport_mapNames_absent e' n hfirst.1 he,
      δ.nameSupport_mapNames_absent e' n hfirst.2.1 he⟩
  refine ⟨left' ∪ right',φ'.withPolicy _,ψ'.withPolicy _,χ'.withPolicy _,δ'.withPolicy _,
    ha'.pad_policy ∅ right' (fun n hn _ => (second_fresh n hn).1),
    hb'.pad_policy ∅ right' (fun n hn _ => (second_fresh n hn).2),?_,?_,
    (he₁.mapNames e).withPolicy _ Finset.subset_union_left,?_⟩
  · simpa only [RepresentsFrame,canonicalFrame,Frame.withPolicy,Extended.activeFrame,
      right',Finset.union_comm] using hc'.pad_policy ∅ left' (fun n hn _ => (first_stays_fresh n hn).1)
  · simpa only [RepresentsFrame,canonicalFrame,Frame.withPolicy,Extended.activeFrame,
      right',Finset.union_comm] using hd'.pad_policy ∅ left' (fun n hn _ => (first_stays_fresh n hn).2)
  · exact (he₂.mapNames e').withPolicy _ Finset.subset_union_right

end Historical.General.Source.Named
end ExplainableCrypto.Helios.Symbolic
