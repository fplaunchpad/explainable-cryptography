import ExplainableCrypto.Helios.Symbolic.SourceRawOutputMatching

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V : Type}

theorem hasInput_iff_threads (p : Agent V) (c : Nat) :
    p.HasInput c ↔ ∃ body, Agent.input c body ∈ p.threads := by
  induction p <;> simp_all [HasInput,threads,threadList,exists_or]

theorem hasOutput_iff_threads (p : Agent V) (c : Nat) :
    p.HasOutput c ↔ ∃ m body, Agent.output c m body ∈ p.threads := by
  induction p <;> simp_all [HasOutput,threads,threadList,exists_or]

theorem HasInput.prefix {p : Agent V} {c : Nat} (h : p.HasInput c) :
    ∃ body rest, ParEq p (.par (.input c body) rest) := by
  induction p with
  | input d body => change c=d at h; subst d; exact ⟨body,.nil,(ParEq.zero _).symm⟩
  | par p q ih ij =>
    rcases h with h | h
    · obtain ⟨body,rest,hs⟩ := ih h
      exact ⟨body,.par rest q,(hs.par (.refl q)).trans (.assoc _ _ _)⟩
    · obtain ⟨body,rest,hs⟩ := ij h
      exact ⟨body,.par rest p,(ParEq.comm _ _).trans ((hs.par (.refl p)).trans (.assoc _ _ _))⟩
  | nil | output | branch => exact h.elim

theorem HasOutput.prefix {p : Agent V} {c : Nat} (h : p.HasOutput c) :
    ∃ m body rest, ParEq p (.par (.output c m body) rest) := by
  induction p with
  | output d m body => change c=d at h; subst d; exact ⟨m,body,.nil,(ParEq.zero _).symm⟩
  | par p q ih ij =>
    rcases h with h | h
    · obtain ⟨m,body,rest,hs⟩ := ih h
      exact ⟨m,body,.par rest q,(hs.par (.refl q)).trans (.assoc _ _ _)⟩
    · obtain ⟨m,body,rest,hs⟩ := ij h
      exact ⟨m,body,.par rest p,(ParEq.comm _ _).trans ((hs.par (.refl p)).trans (.assoc _ _ _))⟩
  | nil | input | branch => exact h.elim

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

theorem Structural.closeVars (n : Nat) {a b : Extended (LocalVars n V)}
    (h : Structural a b) : Structural (Extended.closeVars n a) (Extended.closeVars n b) := by
  induction n generalizing V with
  | zero => exact h
  | succ n ih => exact .newVar (ih h)

theorem Reduction.closeVars (n : Nat) {a b : Extended (LocalVars n V)}
    (h : Reduction a b) : Reduction (Extended.closeVars n a) (Extended.closeVars n b) := by
  induction n generalizing V with
  | zero => exact h
  | succ n ih => exact .newVar (ih h)

/-- Move the existing variable prefix over a parallel context. The context's
old variables use the exact outerVar embedding, with every binder retained. -/
theorem par_closeVars (n : Nat) (a : Extended V) (b : Extended (LocalVars n V)) :
    Structural (.par a (closeVars n b))
      (closeVars n (.par (a.rename (outerVar n)) b)) := by
  induction n generalizing V with
  | zero =>
    change Structural (.par a b) (.par (a.rename id) b)
    rw [rename_id]
    exact .refl _
  | succ n ih =>
    have h := (Structural.newPar a (closeVars n b)).trans (.newVar (ih (a.rename some) b))
    have he : (a.rename some).rename (outerVar n) = a.rename (outerVar (n+1)) := by
      rw [rename_comp]
      rfl
    rw [he] at h
    exact h

private theorem prefix_beside_context (n : Nat) (head rest : Extended (LocalVars n V)) (a : Extended V) :
    Structural (.par (closeVars n (.par head rest)) a)
      (closeVars n (.par head (.par rest (a.rename (outerVar n))))) :=
  (Structural.comm _ _).trans ((par_closeVars n a _).trans
    (Structural.closeVars n ((Structural.comm _ _).trans (Structural.assoc _ _ _))))

/-- Expose the actual ready input while retaining all local binders, providers
and the complete remaining code. -/
theorem input_prefix_of_realizes {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (ha : a.Realizes env p) {c : Nat} (hp : p.HasInput c) :
    ∃ (n : Nat) (body : Agent (Option (LocalVars n V))) (rest : Extended (LocalVars n V)),
      Structural a (closeVars n (.par (.plain (.input c body)) rest)) := by
  induction a generalizing p with
  | plain q =>
    obtain ⟨body,rest,hs⟩ := ((Agent.hasInput_subst q env c).mp ((ha.hasInput c).mpr hp)).prefix
    exact ⟨0,body,.plain rest,(parEq_derivable hs).trans (.plainPar _ _)⟩
  | active x m => exact ((ha.2.hasInput c).mpr hp).elim
  | newVar a ih =>
    obtain ⟨m,hm⟩ := ha
    obtain ⟨n,body,rest,hs⟩ := ih hm hp
    exact ⟨n+1,body,rest,.newVar hs⟩
  | par a b ih ij =>
    obtain ⟨q,s,hq,hs,he⟩ := ha
    rcases (he.hasInput c).mpr hp with hp | hp
    · obtain ⟨n,body,rest,ht⟩ := ih hq hp
      exact ⟨n,body,.par rest (b.rename (outerVar n)),
        (ht.parLeft b).trans (prefix_beside_context n _ _ b)⟩
    · obtain ⟨n,body,rest,ht⟩ := ij hs hp
      exact ⟨n,body,.par rest (a.rename (outerVar n)),(Structural.comm _ _).trans
        ((ht.parLeft a).trans (prefix_beside_context n _ _ a))⟩

/-- Expose the complete raw output payload and its continuation at the same
channel, without grounding or changing either. -/
theorem output_prefix_of_realizes {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (ha : a.Realizes env p) {c : Nat} (hp : p.HasOutput c) :
    ∃ (n : Nat) (m : Term (LocalVars n V)) (body : Agent (LocalVars n V))
      (rest : Extended (LocalVars n V)),
      Structural a (closeVars n (.par (.plain (.output c m body)) rest)) := by
  induction a generalizing p with
  | plain q =>
    obtain ⟨m,body,rest,hs⟩ := ((Agent.hasOutput_subst q env c).mp ((ha.hasOutput c).mpr hp)).prefix
    exact ⟨0,m,body,.plain rest,(parEq_derivable hs).trans (.plainPar _ _)⟩
  | active x m => exact ((ha.2.hasOutput c).mpr hp).elim
  | newVar a ih =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨n,m,body,rest,hs⟩ := ih hv hp
    exact ⟨n+1,m,body,rest,.newVar hs⟩
  | par a b ih ij =>
    obtain ⟨q,s,hq,hs,he⟩ := ha
    rcases (he.hasOutput c).mpr hp with hp | hp
    · obtain ⟨n,m,body,rest,ht⟩ := ih hq hp
      exact ⟨n,m,body,.par rest (b.rename (outerVar n)),
        (ht.parLeft b).trans (prefix_beside_context n _ _ b)⟩
    · obtain ⟨n,m,body,rest,ht⟩ := ij hs hp
      exact ⟨n,m,body,.par rest (a.rename (outerVar n)),(Structural.comm _ _).trans
        ((ht.parLeft a).trans (prefix_beside_context n _ _ a))⟩

/-- Extract the actual witnesses already chosen by a realization beneath the
finite local prefix. This does not invent a solution of the provider equations. -/
theorem realizes_closeVars_witness {n : Nat} {a : Extended (LocalVars n V)}
    {env : V → Ground} {p : Agent Empty} (h : (closeVars n a).Realizes env p) :
    ∃ env' : LocalVars n V → Ground, a.Realizes env' p := by
  induction n generalizing V with
  | zero => exact ⟨env,h⟩
  | succ n ih => obtain ⟨m,hm⟩ := h; exact ih hm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
