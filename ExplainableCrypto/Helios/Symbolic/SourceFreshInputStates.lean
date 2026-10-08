import ExplainableCrypto.Helios.Symbolic.SourceFreshPolicy

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {hidden restricted : Finset Nat} {handles : Nat}

/-- Freshen both complete states with the same permutations, keeping the actual
input recipe unchanged. Its public channel is fixed; its previously bound base
literals become free input names under the fresh policy. All public frame
observations remain equivalent in the two worlds. -/
theorem exists_common_fresh_input_states (p q : ScopedState restricted handles) (c : Nat) (r : Recipe handles)
    (hc : c ∉ hidden) (hs : p.frame.StaticEq q.frame) :
    ∃ e k : Nat ≃ Nat,
      Structural (restrictedState hidden p) (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      Structural (restrictedState hidden q) (restrictedState (hidden.image k) (q.mapNames e k)) ∧
      r.Public (restricted.image e) ∧ k c = c ∧
      (p.frame.mapNames e).StaticEq (q.frame.mapNames e) := by
  obtain ⟨e,k,hp,hq,hf,hfix⟩ := exists_common_fresh_policy hidden restricted
    (.embed (Extended.frameProcess p.frame p.body)) (.embed (Extended.frameProcess q.frame q.body))
    (Extended.FreeLabel.input c r).nameSupport
  have hpub := (input_restriction_fresh_iff (hidden := hidden.image k) (restricted := restricted.image e) c r).mp hf
  have hchan : (SourceName.channel c).map e k = .channel c := hfix (.channel c)
    (by simp [Extended.FreeLabel.nameSupport])
    (by simpa only [channel_mem_restrictionNames] using hc)
  refine ⟨e,k,?_,?_,hpub.2,SourceName.channel.inj hchan,hs.mapNames e⟩
  · simpa only [restrictedState,ScopedState.mapNames,Named.mapNames,Extended.frameProcess_mapNames] using hp
  · simpa only [restrictedState,ScopedState.mapNames,Named.mapNames,Extended.frameProcess_mapNames] using hq

/-- A source input from an actual state has a representative with a public
recipe and the same label/target. This does not normalize its derivation or
assert that the target is already a canonical evaluated state. -/
theorem input_action_common_fresh_states (p q : ScopedState restricted handles)
    (c : Nat) (r : Recipe handles) (target : Named (Fin handles))
    (h : FreeStep (restrictedState hidden p) (.input c r) target) (hs : p.frame.StaticEq q.frame) :
    ∃ e k : Nat ≃ Nat,
      Structural (restrictedState hidden p) (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      Structural (restrictedState hidden q) (restrictedState (hidden.image k) (q.mapNames e k)) ∧
      r.Public (restricted.image e) ∧ k c = c ∧
      (p.frame.mapNames e).StaticEq (q.frame.mapNames e) ∧
      FreeStep (restrictedState (hidden.image k) (p.mapNames e k)) (.input c r) target := by
  obtain ⟨e,k,hp,hq,hr,hc,he⟩ := exists_common_fresh_input_states p q c r (restricted_free_channel_public p h) hs
  exact ⟨e,k,hp,hq,hr,hc,he,.congr hp.symm h (.refl _)⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
