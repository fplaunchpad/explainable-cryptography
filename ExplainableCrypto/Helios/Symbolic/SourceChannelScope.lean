import ExplainableCrypto.Helios.Symbolic.SourceNamedChannels

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Extended

theorem frameEntries_channels (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) :
    (frameEntries h vars values).channels = ∅ := by
  induction h <;> simp_all [frameEntries,channels,Agent.channels]

theorem activeFrame_channels (φ : Frame restricted handles) : (activeFrame φ).channels = ∅ :=
  frameEntries_channels handles id φ.value

theorem frameProcess_channels (φ : Frame restricted handles) (p : Agent Empty) :
    (frameProcess φ p).channels = p.channels := by
  simp only [frameProcess,channels,activeFrame_channels,groundAgent,Agent.channels_subst,Finset.empty_union]
end Extended

namespace Named
variable {hidden restricted : Finset Nat} {handles : Nat}

theorem FreeStep.channel_mem {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) : l.channel ∈ a.channels := by
  induction h with
  | embed h => exact h.channel_mem
  | @scopeName V n a b l hf h ih =>
    cases n with
    | base n => exact ih
    | channel c =>
      apply Finset.mem_erase.mpr
      refine ⟨?_,ih⟩
      intro he
      apply hf
      rw [← he]
      exact l.channel_mem_support
  | scopeInput h ih => exact ih
  | scopeOutput h ih => exact ih
  | parLeft c h ih => exact Finset.mem_union_left _ ih
  | parRight a h ih => exact Finset.mem_union_right _ ih
  | congr hp h hq ih => rw [hp.channels]; exact ih

theorem BoundOutput.channel_mem {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) : c ∈ a.channels := by
  induction h with
  | embed h => exact h.channel_mem
  | openAtom h => exact h.channel_mem
  | scopeName n hf h ih =>
    cases n with
    | base n => exact ih
    | channel d => exact Finset.mem_erase.mpr ⟨fun he => hf (congrArg SourceName.channel he.symm),ih⟩
  | scopeVar h ih => exact ih
  | parLeft d h ih => exact Finset.mem_union_left _ ih
  | parRight a h ih => exact Finset.mem_union_right _ ih
  | congr hp h hq ih => rw [hp.channels]; exact ih

theorem channel_mem_restrictNames (ns : List SourceName) (a : Named V) (c : Nat) :
    c ∈ (restrictNames ns a).channels ↔ c ∈ a.channels ∧ SourceName.channel c ∉ ns := by
  induction ns with
  | nil => simp [restrictNames]
  | cons n ns ih =>
    cases n <;> simp_all [restrictNames,List.foldr,channels,and_left_comm]

theorem channel_mem_restrictedState (hidden : Finset Nat) (p : ScopedState restricted handles) (c : Nat) :
    c ∈ (restrictedState hidden p).channels ↔ c ∈ p.body.channels ∧ c ∉ hidden := by
  simp only [restrictedState,channel_mem_restrictNames,channels,Extended.frameProcess_channels,channel_mem_restrictionNames]

/-- These converses include arbitrary Struct/alpha paths and arbitrary targets,
not just the direct Scope constructor used by the forward bridge. -/
theorem restricted_free_channel_public (p : ScopedState restricted handles) {q : Named (Fin handles)}
    {l : Extended.FreeLabel (Fin handles)} (h : FreeStep (restrictedState hidden p) l q) : l.channel ∉ hidden :=
  ((channel_mem_restrictedState hidden p l.channel).mp h.channel_mem).2

theorem restricted_bound_channel_public (p : ScopedState restricted handles) {q : Named (Option (Fin handles))}
    {c : Nat} (h : BoundOutput (restrictedState hidden p) c q) : c ∉ hidden :=
  ((channel_mem_restrictedState hidden p c).mp h.channel_mem).2

theorem restricted_private_free_blocked (p : ScopedState restricted handles) (q : Named (Fin handles))
    (l : Extended.FreeLabel (Fin handles)) (hc : l.channel ∈ hidden) :
    ¬ FreeStep (restrictedState hidden p) l q := fun h => restricted_free_channel_public p h hc

theorem restricted_private_bound_blocked (p : ScopedState restricted handles) (q : Named (Option (Fin handles)))
    (c : Nat) (hc : c ∈ hidden) : ¬ BoundOutput (restrictedState hidden p) c q :=
  fun h => restricted_bound_channel_public p h hc
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
