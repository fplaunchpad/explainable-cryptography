import ExplainableCrypto.Helios.Symbolic.SourceInterpretationReduction
import ExplainableCrypto.Helios.Symbolic.SourceFrameSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

theorem groundTerm_eval (m : Ground) (env : V → Ground) : (groundTerm m).subst env = m := by
  rw [groundTerm_subst]
  have he : (Empty.elim : Empty → Ground) = Term.var := by funext v; exact v.elim
  simp only [groundTerm,he,Term.subst_var]

theorem groundAgent_eval (p : Agent Empty) (env : V → Ground) : (groundAgent p).subst env = p := by
  rw [groundAgent_subst]
  have he : (Empty.elim : Empty → Ground) = Term.var := by funext v; exact v.elim
  simp only [groundAgent,he,Agent.subst_var]

/-- Interpretation retains every full frame value, modulo E. The frame itself
has no executable process, even when a structurally different result is used. -/
theorem frameEntries_realizes_iff (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    (env : V → Ground) (p : Agent Empty) :
    (frameEntries h vars values).Realizes env p ↔
      (∀ i, EqE (env (vars i)) (values i)) ∧ Agent.EvalEq .nil p := by
  induction h generalizing p with
  | zero =>
    constructor
    · intro hp; exact ⟨fun i => Fin.elim0 i,hp⟩
    · exact fun hp => hp.2
  | succ h ih =>
    simp only [frameEntries,Realizes,groundTerm_eval]
    constructor
    · rintro ⟨q,r,⟨hx,hq⟩,hr,hp⟩
      obtain ⟨ht,hr⟩ := (ih _ _ r).mp hr
      refine ⟨?_,(Agent.EvalEq.of_parEq (Agent.ParEq.zero .nil).symm).trans
        ((Agent.EvalEq.par hq hr).trans hp)⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hx
      · exact ht j
    · rintro ⟨hv,hp⟩
      exact ⟨.nil,.nil,⟨hv (Fin.last h),.refl _⟩,
        (ih _ _ .nil).mpr ⟨fun i => hv i.castSucc,.refl _⟩,
        (Agent.EvalEq.of_parEq (.zero _)).trans hp⟩

theorem activeFrame_realizes_iff (φ : Frame restricted handles) (env : Fin handles → Ground)
    (p : Agent Empty) : (activeFrame φ).Realizes env p ↔
      (∀ i, EqE (env i) (φ.value i)) ∧ Agent.EvalEq .nil p :=
  frameEntries_realizes_iff handles id φ.value env p

theorem frameProcess_realizes_iff (φ : Frame restricted handles) (a : Agent Empty)
    (env : Fin handles → Ground) (p : Agent Empty) :
    (frameProcess φ a).Realizes env p ↔
      (∀ i, EqE (env i) (φ.value i)) ∧ Agent.EvalEq a p := by
  change (∃ q r, (activeFrame φ).Realizes env q ∧
    (plain (groundAgent a)).Realizes env r ∧ Agent.EvalEq (.par q r) p) ↔ _
  simp only [activeFrame_realizes_iff,Realizes,groundAgent_eval]
  have hn : Agent.ParEq (.par .nil a) a := (Agent.ParEq.comm _ _).trans (.zero _)
  constructor
  · rintro ⟨q,r,⟨hv,hq⟩,hr,hp⟩
    exact ⟨hv,(Agent.EvalEq.of_parEq hn.symm).trans ((Agent.EvalEq.par hq hr).trans hp)⟩
  · rintro ⟨hv,hp⟩
    exact ⟨.nil,a,⟨hv,.refl _⟩,.refl _,(Agent.EvalEq.of_parEq hn).trans hp⟩

theorem frameProcess_realizes (φ : Frame restricted handles) (p : Agent Empty) :
    (frameProcess φ p).Realizes φ.value p :=
  (frameProcess_realizes_iff φ p φ.value p).mpr ⟨fun _ => .refl _,.refl _⟩

theorem frameProcess_structural_values {restricted' : Finset Nat}
    (φ : Frame restricted handles) (ψ : Frame restricted' handles) (p q : Agent Empty)
    (h : Structural (frameProcess φ p) (frameProcess ψ q)) :
    (∀ i, EqE (φ.value i) (ψ.value i)) ∧ Agent.EvalEq q p :=
  (frameProcess_realizes_iff ψ q φ.value p).mp
    ((h.realizes φ.value p).mp (frameProcess_realizes φ p))

/-- An arbitrary raw target has an interpreted actual process step. No target
normal-form or admissibility premise is assumed. -/
theorem frameProcess_reduction_interpreted (φ : Frame restricted handles) (p : Agent Empty)
    {b : Extended (Fin handles)} (h : Reduction (frameProcess φ p) b) :
    ∃ q, Agent.Tau p q ∧ b.Realizes φ.value q :=
  h.realizes φ.value (frameProcess_realizes φ p)

/-- If both endpoints are canonical frames, every handle retains its full
E-value and the target body matches an actual Tau result modulo EvalEq. -/
theorem frameProcess_reduction_values {restricted' : Finset Nat}
    (φ : Frame restricted handles) (ψ : Frame restricted' handles) (p q : Agent Empty)
    (h : Reduction (frameProcess φ p) (frameProcess ψ q)) :
    (∀ i, EqE (φ.value i) (ψ.value i)) ∧ ∃ r, Agent.Tau p r ∧ Agent.EvalEq q r := by
  obtain ⟨r,hr,he⟩ := frameProcess_reduction_interpreted φ p h
  obtain ⟨hv,hq⟩ := (frameProcess_realizes_iff ψ q φ.value r).mp he
  exact ⟨hv,r,hr,hq⟩

theorem frameProcess_structural_staticEq (φ ψ : Frame restricted handles) (p q : Agent Empty)
    (h : Structural (frameProcess φ p) (frameProcess ψ q)) : φ.StaticEq ψ :=
  Frame.staticEq_of_pointwise (frameProcess_structural_values φ ψ p q h).1

theorem frameProcess_reduction_staticEq (φ ψ : Frame restricted handles) (p q : Agent Empty)
    (h : Reduction (frameProcess φ p) (frameProcess ψ q)) : φ.StaticEq ψ :=
  Frame.staticEq_of_pointwise (frameProcess_reduction_values φ ψ p q h).1

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
