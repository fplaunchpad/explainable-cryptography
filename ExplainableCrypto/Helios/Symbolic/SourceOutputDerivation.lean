import ExplainableCrypto.Helios.Symbolic.SourceActiveFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

theorem capture_parLeft (m : Term V) (p r : Agent V) :
    Structural (.par (capture m p) (.plain r.shift)) (capture m (.par p r)) :=
  (Structural.assoc _ _ _).trans (Structural.parRight _ (Structural.plainPar _ _).symm)

theorem capture_parRight (m : Term V) (p r : Agent V) :
    Structural (.par (.plain r.shift) (capture m p)) (capture m (.par r p)) :=
  (Structural.assoc _ _ _).symm.trans ((Structural.parLeft _ (Structural.comm _ _)).trans
    ((Structural.assoc _ _ _).trans (Structural.parRight _ (Structural.plainPar _ _).symm)))

theorem capture_parEq (m : Term V) {p q : Agent V} (h : Agent.ParEq p q) :
    Structural (capture m p) (capture m q) :=
  .parRight _ (parEq_derivable (h.subst (fun v => .var (some v))))

/-- A core visible output at any active parallel position has an atomic
bound-output derivation, after embedding its ground process into a frame domain. -/
theorem core_output_derivable (V : Type) {p q : Agent Empty} {a : Agent.PayloadEvent}
    (h : Agent.CoreVisible p a q) {c : Nat} {m : Ground} (he : a = .output c m) :
    BoundOutput (.plain (groundAgent p : Agent V)) c (capture (groundTerm m) (groundAgent q)) := by
  induction h with
  | input => cases he
  | output c' m' p =>
    cases he
    exact message_output c (groundTerm m) (groundAgent p)
  | parLeft r h ih =>
    exact .congr (.plainPar _ _) (.parLeft (.plain (groundAgent r)) (ih he)) (capture_parLeft _ _ _)
  | parRight r h ih =>
    exact .congr (.plainPar _ _) (.parRight (.plain (groundAgent r)) (ih he)) (capture_parRight _ _ _)

/-- All ground visible outputs modulo parallel structure derive fresh active
bindings by Out-Atom/Open-Atom, rather than a primitive frame-extension rule. -/
theorem visible_output_derivable (V : Type) {p q : Agent Empty} {c : Nat} {m : Ground}
    (h : Agent.Visible p (.output c m) q) :
    BoundOutput (.plain (groundAgent p : Agent V)) c (capture (groundTerm m) (groundAgent q)) := by
  obtain ⟨p',q',hp,hc,hq⟩ := h
  exact .congr (parEq_derivable (hp.subst Empty.elim)) (core_output_derivable V hc rfl)
    (capture_parEq _ (hq.subst Empty.elim))

/-- The old public active frame remains in the source parallel context while
the output introduces its fresh active variable. -/
theorem frame_visible_output_derivable (φ : Frame restricted handles) {p q : Agent Empty} {c : Nat} {m : Ground}
    (h : Agent.Visible p (.output c m) q) :
    BoundOutput (frameProcess φ p) c
      (.par ((activeFrame φ).rename some) (capture (groundTerm m) (groundAgent q))) :=
  .parRight (activeFrame φ) (visible_output_derivable (Fin handles) h)

/-- Every evaluated scoped output has a source bound-output derivation whose
captured active frame is exactly its wrapper target after explicit handle
renaming. Name restriction and the full source converse remain separate. -/
theorem scoped_output_derivable (hidden : Finset Nat) (p : ScopedState restricted handles)
    (q : ScopedState restricted (handles+1)) (c : Nat) (h : ScopedStep hidden restricted p (.output c) q) :
    ∃ m : Ground,
      BoundOutput (frameProcess p.frame p.body) c
        (.par ((activeFrame p.frame).rename some) (capture (groundTerm m) (groundAgent q.body))) ∧
      Structural
        ((Extended.par ((activeFrame p.frame).rename some) (capture (groundTerm m) (groundAgent q.body))).rename outputHandle)
        (frameProcess q.frame q.body) := by
  obtain ⟨_,m,he,hv⟩ := (scoped_output_iff p q c).mp h
  refine ⟨m,frame_visible_output_derivable p.frame hv,?_⟩
  rw [he]
  exact frame_output_capture p.frame m q.body
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
