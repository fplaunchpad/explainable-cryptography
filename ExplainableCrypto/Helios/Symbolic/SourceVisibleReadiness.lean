import ExplainableCrypto.Helios.Symbolic.SourceReachableFramePresentation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V W : Type}

/-- An input at evaluation depth, without crossing a prefix or a guard. -/
def HasInput (c : Nat) : Agent V → Prop
  | .input d _ => c = d
  | .par p q => HasInput c p ∨ HasInput c q
  | _ => False

/-- An output at evaluation depth; its complete payload is not erased by actions. -/
def HasOutput (c : Nat) : Agent V → Prop
  | .output d _ _ => c = d
  | .par p q => HasOutput c p ∨ HasOutput c q
  | _ => False

theorem hasInput_subst (p : Agent V) (σ : V → Term W) (c : Nat) :
    (p.subst σ).HasInput c ↔ p.HasInput c := by
  induction p <;> simp_all [Agent.subst,HasInput]

theorem HasInput.mapNames {p : Agent V} {c : Nat} (h : p.HasInput c) (f g : Nat → Nat) :
    (p.mapNames f g).HasInput (g c) := by
  induction p <;> simp_all [HasInput,Agent.mapNames]
  case par p q ih ij => exact h.elim (fun h => Or.inl (ih h)) (fun h => Or.inr (ij h))

theorem ParEq.hasInput {p q : Agent V} (h : ParEq p q) (c : Nat) :
    p.HasInput c ↔ q.HasInput c := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | zero => simp [HasInput]
  | assoc => exact or_assoc
  | comm => exact or_comm
  | par h j ih ij => exact or_congr ih ij

theorem EquivE.hasInput {p q : Agent V} (h : EquivE p q) (c : Nat) :
    p.HasInput c ↔ q.HasInput c := by
  induction h <;> simp_all [HasInput]

theorem EvalEq.hasInput {p q : Agent V} (h : EvalEq p q) (c : Nat) :
    p.HasInput c ↔ q.HasInput c := by
  obtain ⟨r,hp,hq⟩ := h
  exact (hp.hasInput c).trans (hq.hasInput c)

theorem hasOutput_subst (p : Agent V) (σ : V → Term W) (c : Nat) :
    (p.subst σ).HasOutput c ↔ p.HasOutput c := by
  induction p <;> simp_all [Agent.subst,HasOutput]

theorem HasOutput.mapNames {p : Agent V} {c : Nat} (h : p.HasOutput c) (f g : Nat → Nat) :
    (p.mapNames f g).HasOutput (g c) := by
  induction p <;> simp_all [HasOutput,Agent.mapNames]
  case par p q ih ij => exact h.elim (fun h => Or.inl (ih h)) (fun h => Or.inr (ij h))

theorem ParEq.hasOutput {p q : Agent V} (h : ParEq p q) (c : Nat) :
    p.HasOutput c ↔ q.HasOutput c := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | zero => simp [HasOutput]
  | assoc => exact or_assoc
  | comm => exact or_comm
  | par h j ih ij => exact or_congr ih ij

theorem EquivE.hasOutput {p q : Agent V} (h : EquivE p q) (c : Nat) :
    p.HasOutput c ↔ q.HasOutput c := by
  induction h <;> simp_all [HasOutput]

theorem EvalEq.hasOutput {p q : Agent V} (h : EvalEq p q) (c : Nat) :
    p.HasOutput c ↔ q.HasOutput c := by
  obtain ⟨r,hp,hq⟩ := h
  exact (hp.hasOutput c).trans (hq.hasOutput c)

theorem Visible.hasInput {p q : Agent Empty} {c : Nat} {m : Ground}
    (h : Visible p (.input c m) q) : p.HasInput c := by
  obtain ⟨a,b,hp,hv,hq⟩ := h
  apply (hp.hasInput c).mpr
  clear hp hq
  generalize he : PayloadEvent.input c m = l at hv
  induction hv with
  | input => cases he; rfl
  | output => cases he
  | parLeft _ _ ih => exact Or.inl (ih he)
  | parRight _ _ ih => exact Or.inr (ih he)

theorem Visible.hasOutput {p q : Agent Empty} {c : Nat} {m : Ground}
    (h : Visible p (.output c m) q) : p.HasOutput c := by
  obtain ⟨a,b,hp,hv,hq⟩ := h
  apply (hp.hasOutput c).mpr
  clear hp hq
  generalize he : PayloadEvent.output c m = l at hv
  induction hv with
  | output => cases he; rfl
  | input => cases he
  | parLeft _ _ ih => exact Or.inl (ih he)
  | parRight _ _ ih => exact Or.inr (ih he)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

theorem plain_input_available (p : Agent V) (c : Nat) (r : Term V) (h : p.HasInput c) :
    ∃ b, FreeStep (.plain p) (.input c r) b := by
  induction p with
  | input d p => change c=d at h; subst d; exact ⟨_,.input c r p⟩
  | par p q ih ij =>
    rcases h with h | h
    · obtain ⟨b,hb⟩ := ih r h
      exact ⟨_,.congr (.plainPar p q) (.parLeft _ hb) (.refl _)⟩
    · obtain ⟨b,hb⟩ := ij r h
      exact ⟨_,.congr (.plainPar p q) (.parRight _ hb) (.refl _)⟩
  | nil | output | branch => exact h.elim

theorem plain_bound_available (p : Agent V) (c : Nat) (h : p.HasOutput c) :
    ∃ b, BoundOutput (.plain p) c b := by
  induction p with
  | output d m p => change c=d at h; subst d; exact ⟨_,message_output c m p⟩
  | par p q ih ij =>
    rcases h with h | h
    · obtain ⟨b,hb⟩ := ih h
      exact ⟨_,.congr (.plainPar p q) (.parLeft _ hb) (.refl _)⟩
    · obtain ⟨b,hb⟩ := ij h
      exact ⟨_,.congr (.plainPar p q) (.parRight _ hb) (.refl _)⟩
  | nil | input | branch => exact h.elim

/-- The interpreted ready input yields an original action with the exact raw
recipe. All local scopes receive its typed shift; no model-normalization premise
is required for this prefix-existence direction. -/
theorem input_available_of_realizes {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (ha : a.Realizes env p) {c : Nat} (hp : p.HasInput c) (r : Term V) :
    ∃ b, FreeStep a (.input c r) b := by
  induction a generalizing p with
  | plain q => exact plain_input_available q c r ((Agent.hasInput_subst q env c).mp ((ha.hasInput c).mpr hp))
  | active x m => exact ((ha.2.hasInput c).mpr hp).elim
  | par a b ih ij =>
    obtain ⟨q,s,hq,hs,he⟩ := ha
    rcases (he.hasInput c).mpr hp with hp | hp
    · obtain ⟨t,ht⟩ := ih hq hp r
      exact ⟨_,.parLeft _ ht⟩
    · obtain ⟨t,ht⟩ := ij hs hp r
      exact ⟨_,.parRight _ ht⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := ha
    obtain ⟨b,hb⟩ := ih hm hp (shiftTerm r)
    exact ⟨_,.scopeInput hb⟩

/-- Ready output needs no choice of a ground representative: the original
message-output rule retains the raw complete payload and exports a fresh binder. -/
theorem bound_available_of_realizes {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (ha : a.Realizes env p) {c : Nat} (hp : p.HasOutput c) :
    ∃ b, BoundOutput a c b := by
  induction a generalizing p with
  | plain q => exact plain_bound_available q c ((Agent.hasOutput_subst q env c).mp ((ha.hasOutput c).mpr hp))
  | active x m => exact ((ha.2.hasOutput c).mpr hp).elim
  | par a b ih ij =>
    obtain ⟨q,s,hq,hs,he⟩ := ha
    rcases (he.hasOutput c).mpr hp with hp | hp
    · obtain ⟨t,ht⟩ := ih hq hp
      exact ⟨_,.parLeft _ ht⟩
    · obtain ⟨t,ht⟩ := ij hs hp
      exact ⟨_,.parRight _ ht⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := ha
    obtain ⟨b,hb⟩ := ih hm hp
    exact ⟨_,.scope hb⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
