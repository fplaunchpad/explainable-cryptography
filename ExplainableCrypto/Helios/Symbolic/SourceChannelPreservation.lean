import ExplainableCrypto.Helios.Symbolic.SourceChannelScope

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Extended

theorem Reduction.channels_subset {a b : Extended V} (h : Reduction a b) : b.channels ⊆ a.channels := by
  induction h with
  | atomComm c x p q =>
    simp only [Extended.channels,Agent.channels,Agent.channels_bind]
    intro d hd
    rcases Finset.mem_union.mp hd with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hp)
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hq)
  | thenBranch => exact Finset.subset_union_left
  | elseBranch => exact Finset.subset_union_right
  | parLeft c h ih => exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | parRight a h ih => exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | newVar h ih => exact ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih

theorem FreeStep.channels_subset {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) : b.channels ⊆ a.channels := by
  induction h with
  | input c m p =>
    simp only [Extended.channels,Agent.channels,Agent.channels_bind]
    exact Finset.subset_insert _ _
  | output => exact Finset.subset_insert _ _
  | scopeInput h ih => exact ih
  | scopeOutput h ih => exact ih
  | parLeft c h ih => exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | parRight a h ih => exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih

theorem BoundOutput.channels_subset {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) : b.channels ⊆ a.channels := by
  induction h with
  | openAtom h => exact h.channels_subset
  | scope h ih => simpa only [Extended.channels,channels_rename] using ih
  | parLeft d h ih =>
    simpa only [Extended.channels,channels_rename] using Finset.union_subset_union ih (Finset.Subset.refl d.channels)
  | parRight a h ih =>
    simpa only [Extended.channels,channels_rename] using Finset.union_subset_union (Finset.Subset.refl a.channels) ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih
end Extended

namespace Named
variable {hidden restricted : Finset Nat} {handles : Nat}

theorem Reduction.channels_subset {a b : Named V} (h : Reduction a b) : b.channels ⊆ a.channels := by
  induction h with
  | embed h => exact h.channels_subset
  | parLeft c h ih => exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | parRight a h ih => exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | newName n h ih =>
    cases n with
    | base n => exact ih
    | channel c => exact Finset.erase_subset_erase c ih
  | newVar h ih => exact ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih

theorem FreeStep.channels_subset {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) : b.channels ⊆ a.channels := by
  induction h with
  | embed h => exact h.channels_subset
  | scopeName n hf h ih =>
    cases n with
    | base n => exact ih
    | channel c => exact Finset.erase_subset_erase c ih
  | scopeInput h ih => exact ih
  | scopeOutput h ih => exact ih
  | parLeft c h ih => exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | parRight a h ih => exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih

theorem BoundOutput.channels_subset {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) : b.channels ⊆ a.channels := by
  induction h with
  | embed h => exact h.channels_subset
  | openAtom h => exact h.channels_subset
  | scopeName n hf h ih =>
    cases n with
    | base n => exact ih
    | channel c => exact Finset.erase_subset_erase c ih
  | scopeVar h ih => simpa only [Named.channels,channels_rename] using ih
  | parLeft d h ih =>
    simpa only [Named.channels,channels_rename] using Finset.union_subset_union ih (Finset.Subset.refl d.channels)
  | parRight a h ih =>
    simpa only [Named.channels,channels_rename] using Finset.union_subset_union (Finset.Subset.refl a.channels) ih
  | congr hp h hq ih => rw [← hq.channels,hp.channels]; exact ih

theorem reduction_star_channels_subset {a b : Named V} (h : Relation.ReflTransGen Reduction a b) :
    b.channels ⊆ a.channels := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail h h' ih => exact Finset.Subset.trans h'.channels_subset ih

theorem after_internal_private_free_blocked (p : ScopedState restricted handles) {a : Named (Fin handles)}
    (ht : Relation.ReflTransGen Reduction (restrictedState hidden p) a)
    (q : Named (Fin handles)) (l : Extended.FreeLabel (Fin handles)) (hc : l.channel ∈ hidden) :
    ¬ FreeStep a l q := by
  intro h
  have hm := reduction_star_channels_subset ht h.channel_mem
  exact ((channel_mem_restrictedState hidden p l.channel).mp hm).2 hc

theorem after_internal_private_bound_blocked (p : ScopedState restricted handles) {a : Named (Fin handles)}
    (ht : Relation.ReflTransGen Reduction (restrictedState hidden p) a)
    (q : Named (Option (Fin handles))) (c : Nat) (hc : c ∈ hidden) : ¬ BoundOutput a c q := by
  intro h
  have hm := reduction_star_channels_subset ht h.channel_mem
  exact ((channel_mem_restrictedState hidden p c).mp hm).2 hc
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
