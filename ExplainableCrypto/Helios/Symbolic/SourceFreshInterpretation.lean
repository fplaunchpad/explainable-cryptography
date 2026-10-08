import ExplainableCrypto.Helios.Symbolic.SourceInterpretedNameActions
import ExplainableCrypto.Helios.Symbolic.SourceFreshInputStates

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

namespace Extended
variable {restricted : Finset Nat} {handles : Nat}

theorem frameProcess_mapNames_realizes (φ : Frame restricted handles) (p : Agent Empty)
    (f g : Nat → Nat) :
    (frameProcess (φ.mapNames f) (p.mapNames f g)).Realizes (φ.mapNames f).value (p.mapNames f g) := by
  simpa only [frameProcess_mapNames,Frame.mapNames] using (frameProcess_realizes φ p).mapNames f g

/-- Reflection at any consistently renamed actual state recovers the original
full environment and body, without treating its private values as fixed names. -/
theorem frameProcess_mapNames_realizes_iff (φ : Frame restricted handles) (a p : Agent Empty)
    (env : Fin handles → Ground) (e k : Nat ≃ Nat) :
    (frameProcess (φ.mapNames e) (a.mapNames e k)).Realizes
      (fun v => (env v).mapNames e) (p.mapNames e k) ↔ (frameProcess φ a).Realizes env p := by
  rw [← frameProcess_mapNames]
  exact realizes_mapNames_iff _ _ _ _ _
end Extended

namespace Named
variable {hidden restricted : Finset Nat} {handles : Nat}

/-- The coherent fresh-policy construction retains actual interpreted bodies
and complete frame environments in both worlds. This is a source-representative
interface, not an interpretation of arbitrary Named structural derivations. -/
theorem exists_common_fresh_interpreted_input (p q : ScopedState restricted handles)
    (c : Nat) (r : Recipe handles) (hc : c ∉ hidden) (hs : p.frame.StaticEq q.frame) :
    ∃ e k : Nat ≃ Nat,
      Structural (restrictedState hidden p) (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      Structural (restrictedState hidden q) (restrictedState (hidden.image k) (q.mapNames e k)) ∧
      r.Public (restricted.image e) ∧ k c = c ∧
      (p.frame.mapNames e).StaticEq (q.frame.mapNames e) ∧
      (Extended.frameProcess (p.frame.mapNames e) (p.body.mapNames e k)).Realizes
        (p.frame.mapNames e).value (p.body.mapNames e k) ∧
      (Extended.frameProcess (q.frame.mapNames e) (q.body.mapNames e k)).Realizes
        (q.frame.mapNames e).value (q.body.mapNames e k) := by
  obtain ⟨e,k,hp,hq,hr,hc,he⟩ := exists_common_fresh_input_states p q c r hc hs
  exact ⟨e,k,hp,hq,hr,hc,he,Extended.frameProcess_mapNames_realizes _ _ _ _,
    Extended.frameProcess_mapNames_realizes _ _ _ _⟩
end Named

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
