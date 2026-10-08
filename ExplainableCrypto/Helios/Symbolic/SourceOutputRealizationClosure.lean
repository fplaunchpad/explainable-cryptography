import ExplainableCrypto.Helios.Symbolic.SourceInputRealizationClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- An actual bound output from a full canonical realization class constrains
every old environment value and the entire fresh captured message. A canonical
output's complete value and continuation must be deterministic modulo E. -/
theorem BoundOutput.capture_realizes_iff {a : Extended (Fin handles)}
    {b : Extended (Option (Fin handles))} {c : Nat} (h : BoundOutput a c b)
    (φ : Frame restricted handles) (p q : Agent Empty) (m : Ground)
    (ha : a.SameRealizations (frameProcess φ p))
    (hd : ∀ n s, Agent.Visible p (.output c n) s → EqE n m ∧ Agent.EvalEq s q)
    (env : Fin handles → Ground) (v : Ground) (t : Agent Empty) :
    b.Realizes (extendEnv env v) t ↔
      (∀ i, EqE (env i) (φ.value i)) ∧ EqE v m ∧ Agent.EvalEq q t := by
  constructor
  · intro hb
    obtain ⟨u,n,r,hu,hn,hr,he⟩ := h.realizes_backward env v hb
    obtain ⟨hv,hp⟩ := (frameProcess_realizes_iff φ p env u).mp ((ha env u).mp hu)
    obtain ⟨l,s,hs,hl,hj⟩ := hp.symm.visible_transport hr
    cases hl with
    | output _ hn' =>
      obtain ⟨hm,hq⟩ := hd _ s hs
      exact ⟨hv,hn.trans (hn'.trans hm),hq.symm.trans (hj.symm.trans he)⟩
  · rintro ⟨hv,hm,ht⟩
    have hp : a.Realizes env p := (ha env p).mpr
      ((frameProcess_realizes_iff φ p env p).mpr ⟨hv,.refl _⟩)
    obtain ⟨n,s,hs,hb⟩ := h.realizes env hp
    obtain ⟨hn,hq⟩ := hd n s hs
    exact (hb.extend_congr (hn.trans hm.symm)).congr (hq.trans ht)

/-- The output-handle bijection reconstructs any target environment from its
old coordinates and fresh last coordinate, not just the canonical frame value. -/
theorem outputHandle_environment_split (env : Fin (handles+1) → Ground) :
    (fun v => env (outputHandle v)) =
      extendEnv (fun i => env i.castSucc) (env (Fin.last handles)) := by
  funext v
  cases v with
  | none => rw [outputHandle_none]; rfl
  | some i => rw [outputHandle_some]; rfl

/-- After the actual fresh-variable renaming, all realizations of the raw
output target are exactly those of the full extended canonical public frame. -/
theorem BoundOutput.sameRealizations_target {a : Extended (Fin handles)}
    {b : Extended (Option (Fin handles))} {c : Nat} (h : BoundOutput a c b)
    (φ : Frame restricted handles) (p q : Agent Empty) (m : Ground)
    (ha : a.SameRealizations (frameProcess φ p))
    (hd : ∀ n s, Agent.Visible p (.output c n) s → EqE n m ∧ Agent.EvalEq s q) :
    (b.rename outputHandle).SameRealizations (frameProcess (φ.extend m) q) := by
  intro env t
  rw [realizes_rename,outputHandle_environment_split,h.capture_realizes_iff φ p q m ha hd,
    frameProcess_realizes_iff]
  constructor
  · rintro ⟨hv,hm,ht⟩
    refine ⟨?_,ht⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Frame.extend_last] using hm
    · simpa only [Frame.extend_old] using hv j
  · rintro ⟨hv,ht⟩
    exact ⟨fun i => by simpa only [Frame.extend_old] using hv i.castSucc,
      by simpa only [Frame.extend_last] using hv (Fin.last handles),ht⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
