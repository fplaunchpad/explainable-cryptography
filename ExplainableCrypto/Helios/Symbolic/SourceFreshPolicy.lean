import ExplainableCrypto.Helios.Symbolic.SourceCommonFreshPrefix
import Mathlib.Data.Finset.Card

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem SourceName.map_injective (e k : Nat ≃ Nat) : Function.Injective (SourceName.map e k) := by
  intro u v h
  cases u <;> cases v <;> simp_all [SourceName.map,e.injective.eq_iff,k.injective.eq_iff]

namespace Named

theorem Structural.restrictNames_perm (ns ns' : List SourceName) (hp : ns.Perm ns') (a : Named V) :
    Structural (Named.restrictNames ns a) (Named.restrictNames ns' a) := by
  induction hp with
  | nil => exact .refl _
  | cons n h ih => exact .newName n ih
  | swap n m ns => exact .nameComm _ _ _
  | trans h h' ih ih' => exact ih.trans ih'

theorem fresh_prefix_image_eq (ns ns' : List SourceName) (e k : Nat ≃ Nat)
    (hn : ns.Nodup) (hn' : ns'.Nodup) (hl : ns'.length = ns.length)
    (hi : ∀ u ∈ ns, u.map e k ∈ ns') :
    ns.toFinset.image (SourceName.map e k) = ns'.toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact List.mem_toFinset.mpr (hi v (List.mem_toFinset.mp hv))
  · rw [Finset.card_image_of_injective _ (SourceName.map_injective e k)]
    simpa only [List.toFinset_card_of_nodup hn,List.toFinset_card_of_nodup hn'] using hl.le

theorem restrictionNames_image (hidden restricted : Finset Nat) (e k : Nat ≃ Nat) :
    (restrictionNames hidden restricted).toFinset.image (SourceName.map e k) =
      (restrictionNames (hidden.image k) (restricted.image e)).toFinset := by
  ext u
  cases u <;> simp [restrictionNames,SourceName.map,Finset.image_union]

/-- Exact canonical policies follow from the common fresh prefix; the binders
are reordered only with source New-C. Both processes use the same permutations. -/
theorem exists_common_fresh_policy (hidden restricted : Finset Nat) (a : Named V) (b : Named W)
    (avoid : Finset SourceName) :
    ∃ e k : Nat ≃ Nat,
      Structural (restrictNames (restrictionNames hidden restricted) a)
        (restrictNames (restrictionNames (hidden.image k) (restricted.image e)) (a.mapNames e k)) ∧
      Structural (restrictNames (restrictionNames hidden restricted) b)
        (restrictNames (restrictionNames (hidden.image k) (restricted.image e)) (b.mapNames e k)) ∧
      (∀ u ∈ restrictionNames (hidden.image k) (restricted.image e), u ∉ avoid) ∧
      (∀ u ∈ avoid, u ∉ restrictionNames hidden restricted → u.map e k = u) := by
  obtain ⟨ns',e,k,ha,hb,hf,hn,hl,hi,hfix⟩ :=
    exists_common_fresh_prefix (restrictionNames hidden restricted) a b avoid
  have he := fresh_prefix_image_eq _ ns' e k (restrictionNames_nodup hidden restricted) hn hl hi
  rw [restrictionNames_image] at he
  have hp : ns'.Perm (restrictionNames (hidden.image k) (restricted.image e)) :=
    List.perm_of_nodup_nodup_toFinset_eq hn (restrictionNames_nodup _ _) he.symm
  refine ⟨e,k,ha.trans (Structural.restrictNames_perm _ _ hp _),hb.trans (Structural.restrictNames_perm _ _ hp _),?_,hfix⟩
  intro u hu
  exact hf u (hp.mem_iff.mpr hu)
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
