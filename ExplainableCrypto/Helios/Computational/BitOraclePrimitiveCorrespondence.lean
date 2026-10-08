import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveSupport

/-! Bounded complete-query-tree refinement from the existing tape loop to
its primitive target. Source fuel may end live, so this result uses stopping
witnesses rather than unsound padding past an unfinished source computation. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
open Turing OracleComp OracleSpec BitOraclePortTransfer

/-- Exact native query tree and full lowered leaf states, within a common
upper bound on every branch's accumulated target execution. -/
def Compiled {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    OracleComp BitOracleMachine.spec (BitOracleTapeLoop.State s l m) → Nat → State s l m → Prop
  | .pure out, bound, cfg => ∃ used ≤ bound, run code used cfg = pure (lower code out)
  | .liftBind query next, bound, cfg => ∃ before ≤ bound,
      ∃ continuation : BitOracleMachine.spec.Range query → State s l m,
      run code before cfg = OracleComp.queryBind query (fun answer => pure (continuation answer)) ∧
      ∀ answer, Compiled code (next answer) (bound - before) (continuation answer)

private theorem compiled_mono {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleTapeLoop.State s l m))
    (a b : Nat) (cfg : State s l m) (hab : a ≤ b) (h : Compiled code oa a cfg) :
    Compiled code oa b cfg := by
  induction oa generalizing a b cfg with
  | pure out => obtain ⟨used, hu, he⟩ := h; exact ⟨used, hu.trans hab, he⟩
  | queryBind q next ih =>
    obtain ⟨before, hb, continuation, he, ht⟩ := h
    exact ⟨before, hb.trans hab, continuation, he,
      fun answer => ih answer _ _ _ (Nat.sub_le_sub_right hab _) (ht answer)⟩

private theorem compiled_prefix {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleTapeLoop.State s l m))
    (used bound : Nat) (cfg mid : State s l m) (he : run code used cfg = pure mid)
    (h : Compiled code oa bound mid) : Compiled code oa (used + bound) cfg := by
  cases oa with
  | pure out =>
    obtain ⟨after, ha, ht⟩ := h
    refine ⟨used + after, Nat.add_le_add_left ha _, ?_⟩
    rw [run_add, he, pure_bind, ht]
  | queryBind q next =>
    obtain ⟨before, hb, continuation, ht, hn⟩ := h
    refine ⟨used + before, Nat.add_le_add_left hb _, continuation, ?_, ?_⟩
    · rw [run_add, he, pure_bind, ht]
    · simpa only [Nat.add_sub_add_left] using hn

private theorem step_shape {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) :
    (∃ next, BitOracleTapeLoop.step code cfg = pure next) ∨
    ∃ query, ∃ next : BitOracleMachine.spec.Range query → BitOracleTapeLoop.State s l m,
      BitOracleTapeLoop.step code cfg = OracleComp.queryBind query (fun answer => pure (next answer)) := by
  cases cfg with
  | ready label memory tapes =>
    left
    cases label with
    | none => exact ⟨_, rfl⟩
    | some source => cases h : code source <;> simp [BitOracleTapeLoop.step, h]
  | compute source cfg query answer =>
    left
    by_cases h : cfg.l.isNone = true <;> simp [BitOracleTapeLoop.step, h]
  | prepare request destination cfg query answer =>
    left
    by_cases h : cfg.l.isNone = true <;> simp [BitOracleTapeLoop.step, h]
  | call kind cfg => cases cfg with
    | output destination saved cfg answer =>
      left
      by_cases h : cfg.phase = .done <;> simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, h]
    | input destination saved query cfg =>
      left
      by_cases h : cfg.phase = .done <;> simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, h]
    | response destination cfg query answer =>
      left
      by_cases h : cfg.l.isNone = true <;> simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, h]
    | done cfg query answer => exact Or.inl ⟨_, rfl⟩
    | issue destination saved tapes =>
      right
      cases kind <;>
        simp only [BitOracleTapeLoop.step, BitOracleTapeCall.step, OracleTapeDispatch.dispatch,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] <;>
        exact ⟨_, _, rfl⟩

/-- Every finite supported tape-loop run has the exact primitive query tree
and complete lowered results within fuel times the fixed global factor.
All native replies are included; no compiler or successor certificate is given. -/
theorem run_tape {s l m : Nat} (code : BitOracleMachine.Code s l m) (fuel : Nat)
    (cfg : BitOracleTapeLoop.State s l m) (h : Supported code cfg) :
    Compiled code (BitOracleTapeLoop.run code fuel cfg) (fuel * globalFactor code) (lower code cfg) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0, Nat.zero_le _, rfl⟩
  | succ fuel ih =>
    obtain ⟨used, hu, he⟩ := supported_step_match code cfg h
    rcases step_shape code cfg with ⟨next, hn⟩ | ⟨query, next, hn⟩
    · have hs := step_supported code cfg h next (by rw [hn]; simp)
      have hp : run code used (lower code cfg) = pure (lower code next) := by simpa [hn] using he
      have ht := compiled_prefix code (BitOracleTapeLoop.run code fuel next) used
        (fuel * globalFactor code) (lower code cfg) (lower code next) hp (ih next hs)
      rw [BitOracleTapeLoop.run, hn, pure_bind]
      exact compiled_mono code _ _ _ _ (by rw [Nat.succ_mul]; omega) ht
    · have hs (answer : BitOracleMachine.spec.Range query) : Supported code (next answer) :=
        step_supported code cfg h (next answer) (by
          rw [hn]
          change next answer ∈ support (liftM (BitOracleMachine.spec.query query) >>= fun a => pure (next a))
          simp only [support_bind, support_pure, OracleComp.support_liftM, Set.mem_iUnion, Set.mem_range,
            Set.mem_singleton_iff]
          exact ⟨answer, ⟨answer, rfl⟩, rfl⟩)
      have hp : run code used (lower code cfg) = OracleComp.queryBind query
          (fun answer => pure (lower code (next answer))) := by
        change run code used (lower code cfg) =
          (liftM (BitOracleMachine.spec.query query) >>= fun a => pure (lower code (next a)))
        rw [hn] at he
        change run code used (lower code cfg) = lower code <$>
          (liftM (BitOracleMachine.spec.query query) >>= fun a => pure (next a)) at he
        simpa only [map_bind, map_pure] using he
      rw [BitOracleTapeLoop.run, hn]
      change Compiled code (OracleComp.queryBind query (fun a => BitOracleTapeLoop.run code fuel (next a)))
        ((fuel + 1) * globalFactor code) (lower code cfg)
      refine ⟨used, by rw [Nat.succ_mul]; omega, fun a => lower code (next a), hp, ?_⟩
      intro answer
      exact compiled_mono code _ _ _ _ (by rw [Nat.succ_mul]; omega) (ih (next answer) (hs answer))

/-- Ready source configurations derive the invariant automatically. -/
theorem run_ready {s l m : Nat} (code : BitOracleMachine.Code s l m) (fuel : Nat)
    (cfg : BitOracleMachine.Config s l m) (query answer : Tape (Option Bool)) :
    Compiled code (BitOracleTapeLoop.run code fuel (BitOracleTapeLoop.ready cfg query answer))
      (fuel * globalFactor code) (lower code (BitOracleTapeLoop.ready cfg query answer)) :=
  run_tape code fuel _ (ready_supported code _ _ _)

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
