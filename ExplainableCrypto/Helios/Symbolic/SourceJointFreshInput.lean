import ExplainableCrypto.Helios.Symbolic.SourceJointBoundOutput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- Every actual raw input admits a common fresh canonical policy in both
worlds. The original literal label and raw processes remain unchanged. Full
frame equivalence, both source relations and the complete input target survive. -/
theorem JointOpening.common_fresh_input (p t : ScopedState restricted handles)
    {a b d : Named (Fin handles)}
    (ha : JointOpening a (restrictedState hidden p))
    (hd : JointOpening d (restrictedState hidden t)) (hs : p.frame.StaticEq t.frame)
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b)
    (hdet : ∀ c m q s, Agent.Visible p.body (.input c m) q → Agent.Visible p.body (.input c m) s → Agent.EvalEq q s) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Structural (restrictedState hidden p) (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      Structural (restrictedState hidden t) (restrictedState (hidden.image k) (t.mapNames e k)) ∧
      r.Public (restricted.image e) ∧ k c = c ∧
      (p.frame.mapNames e).StaticEq (t.frame.mapNames e) ∧
      JointOpening a (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      JointOpening d (restrictedState (hidden.image k) (t.mapNames e k)) ∧
      ScopedStep (hidden.image k) (restricted.image e) (p.mapNames e k) (.input c r)
        ⟨p.frame.mapNames e,q⟩ ∧
      JointOpening b (restrictedState (hidden.image k) ⟨p.frame.mapNames e,q⟩) := by
  have hc := ha.free_channel_public p h
  obtain ⟨e,k,hp,ht,hr,hk,he⟩ := exists_common_fresh_input_states p t c r hc hs
  have ha' := ha.structural_right hp
  have hd' := hd.structural_right ht
  obtain ⟨q,hq,hb⟩ := ha'.public_input h hr (Agent.input_determinism_mapNames p.body hdet e k)
  have hc' : c ∉ hidden.image k := by
    simpa only [hk] using (channel_public_mapNames_iff c hidden k).mpr hc
  exact ⟨e,k,q,hp,ht,hr,hk,he,ha',hd',.input _ _ _ hc' hr hq,hb⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
