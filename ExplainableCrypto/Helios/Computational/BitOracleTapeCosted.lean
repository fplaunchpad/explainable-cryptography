import ExplainableCrypto.Helios.Computational.BitOracleTapeCap
import ExplainableCrypto.Helios.Computational.BitOracleLoopBounded

/-! Accumulate actual tape work against the original source charge.
The existing bounded-answer policy is reused unchanged. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
open Turing OracleComp OracleSpec TM2TapeRuns BitOraclePortTransfer OracleTapeOutput
open BitOracleTapeCap
open BitOracleLoopBounded (Allowed Within)

/-- A bounded-answer cost witness for the actual tape loop. It retains complete
query nodes and canonical caller/native boundaries, with charged stopping times. -/
def Costed {s l m : Nat} (code : BitOracleMachine.Code s l m) (cap limit : Nat) :
    OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat) → Nat → State s l m → Prop
  | .pure out, spent, cfg => ∃ used previous answer,
      spent + used ≤ unitCost cap * out.2 ∧
      run code used cfg = pure (ready out.1 (wordTape previous) answer)
  | .liftBind q next, spent, cfg => ∃ before,
      ∃ continuation : BitOracleMachine.spec.Range q → State s l m,
      run code before cfg = OracleComp.queryBind q (fun answer => pure (continuation answer)) ∧
      ∀ answer, Allowed limit q answer → Costed code cap limit (next answer) (spent + before) (continuation answer)

private theorem allowed_nonempty (limit : Nat) (q : BitOracleMachine.Request) :
    ∃ answer, Allowed limit q answer := by
  cases q with
  | coin => exact ⟨false, trivial⟩
  | hash word => exact ⟨[], Nat.zero_le _⟩

private theorem within_shift {s l m : Nat}
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (limit bound charge : Nat)
    (hw : Within limit bound ((fun out => (out.1, charge + out.2)) <$> oa)) :
    charge ≤ bound ∧ Within limit (bound - charge) oa := by
  induction oa with
  | pure out =>
    have hh : charge + out.2 ≤ bound := hw.2
    exact ⟨by omega, hw.1, by omega⟩
  | queryBind q next ih =>
    obtain ⟨a, ha⟩ := allowed_nonempty limit q
    exact ⟨(ih a (hw a ha)).1, fun b hb => (ih b (hw b hb)).2⟩

private theorem costed_weaken {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cap limit : Nat) (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent small : Nat) (cfg : State s l m) (h : Costed code cap limit oa spent cfg)
    (hle : small ≤ spent) : Costed code cap limit oa small cfg := by
  induction oa generalizing spent small cfg with
  | pure out =>
    obtain ⟨used, previous, answer, hu, he⟩ := h
    exact ⟨used, previous, answer, by omega, he⟩
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    exact ⟨before, continuation, he, fun a ha => ih a _ _ _ (hr a ha) (by omega)⟩

private theorem costed_prefix {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cap limit : Nat) (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent used : Nat) (cfg mid : State s l m) (he : run code used cfg = pure mid)
    (h : Costed code cap limit oa (spent + used) mid) : Costed code cap limit oa spent cfg := by
  cases oa with
  | pure out =>
    obtain ⟨after, previous, answer, ha, hr⟩ := h
    refine ⟨used + after, previous, answer, by omega, ?_⟩
    rw [run_add, he, pure_bind, hr]
  | queryBind q next =>
    obtain ⟨before, continuation, hr, ht⟩ := h
    refine ⟨used + before, continuation, ?_, ?_⟩
    · rw [run_add, he, pure_bind, hr]
    · intro a ha
      simpa only [Nat.add_assoc] using ht a ha

private theorem costed_shift {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cap limit : Nat) (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent charge : Nat) (cfg : State s l m) (h : Costed code cap limit oa spent cfg) :
    Costed code cap limit ((fun out => (out.1, charge + out.2)) <$> oa)
      (unitCost cap * charge + spent) cfg := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, previous, answer, hu, he⟩ := h
    exact ⟨used, previous, answer, by simp only [Nat.mul_add]; omega, he⟩
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    refine ⟨before, continuation, he, ?_⟩
    intro a ha
    change Costed code cap limit ((fun out => (out.1, charge + out.2)) <$> next a)
      ((unitCost cap * charge + spent) + before) (continuation a)
    simpa only [Nat.add_assoc] using ih a (spent + before) (continuation a) (hr a ha)

private theorem source_hash {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (request destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .hash request destination next) :
    BitOracleMachine.run code (fuel + 1) cfg =
      OracleComp.queryBind (spec := BitOracleMachine.spec) (.hash (cfg.stk request)) (fun (answer : List Bool) =>
        (fun out => (out.1, 1 + (cfg.stk request).length + (cfg.stk destination).length + answer.length + out.2)) <$>
          BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next answer)) := by
  simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind]
  rfl

private theorem source_coin {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .coin destination next) :
    BitOracleMachine.run code (fuel + 1) cfg =
      OracleComp.queryBind (spec := BitOracleMachine.spec) .coin (fun (bit : Bool) =>
        (fun out => (out.1, 2 + (cfg.stk destination).length + out.2)) <$>
          BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next [bit])) := by
  simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind]
  rfl

private theorem credit (cap charge : Nat) (h : 1 ≤ charge) : unitCost cap ≤ unitCost cap * charge := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (unitCost cap) h

/-- Source charge pays for actual tape work on every allowed branch. The cap
invariant accounts for future stack growth; every compiler witness is derived. -/
theorem run_costed {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (previous : List Bool)
    (oldAnswer : Tape (Option Bool)) (limit bound cap : Nat)
    (hw : Within limit bound (BitOracleMachine.run code fuel cfg))
    (hcap : height cfg.stk + bound ≤ cap) (hp : previous.length ≤ cap) :
    Costed code cap limit (BitOracleMachine.run code fuel cfg) 0 (ready cfg (wordTape previous) oldAnswer) := by
  induction fuel generalizing cfg previous oldAnswer bound with
  | zero => exact ⟨0, previous, oldAnswer, by simp, rfl⟩
  | succ fuel ih =>
    have hH : height cfg.stk ≤ cap := by omega
    cases hl : cfg.l with
    | none =>
      have hn : BitOracleMachine.run code (fuel + 1) cfg = BitOracleMachine.run code fuel cfg := by
        simp only [BitOracleMachine.run, BitOracleMachine.step, hl, pure_bind,
          Nat.zero_add, Prod.mk.eta, bind_pure]
      rw [hn] at hw ⊢
      exact ih cfg previous oldAnswer bound hw hcap hp
    | some source =>
      cases hc : code source with
      | compute stmt =>
        have hn : BitOracleMachine.run code (fuel + 1) cfg =
            (fun out => (out.1, BitOracleMachine.localCost stmt + out.2)) <$>
              BitOracleMachine.run code fuel (TM2.stepAux stmt cfg.var cfg.stk) := by
          simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, pure_bind,
            map_eq_bind_pure_comp, Function.comp_def]
        rw [hn] at hw ⊢
        obtain ⟨hc_le, rest⟩ := within_shift _ limit bound (BitOracleMachine.localCost stmt) hw
        have next_cap : height (TM2.stepAux stmt cfg.var cfg.stk).stk +
            (bound - BitOracleMachine.localCost stmt) ≤ cap := by
          have := compute_growth stmt cfg
          omega
        have tail := ih _ previous oldAnswer _ rest next_cap hp
        have shifted := costed_shift code cap limit _ 0 (BitOracleMachine.localCost stmt) _ tail
        obtain ⟨used, hu, he⟩ := compute_run code cfg source stmt hl hc (wordTape previous) oldAnswer
        have cost := compute_bound cfg stmt cap used hH (by have := accesses_le_charge stmt; omega) hu
        have paid := cost.trans (credit cap _ (Nat.succ_le_of_lt (charge_pos stmt)))
        have small := costed_weaken code cap limit _ _ used _ shifted (by omega)
        exact costed_prefix code cap limit _ 0 used _ _ he (by simpa only [Nat.zero_add] using small)
      | hash request destination next =>
        rw [source_hash code fuel cfg source request destination next hl hc] at hw ⊢
        obtain ⟨before, hb, he⟩ := hash_issue code cfg source request destination next hl hc previous oldAnswer
        refine ⟨before, (fun answer => .call .hash (BitOracleTapeCall.incoming cfg request destination next answer)),
          (by exact he), ?_⟩
        intro answer allowed
        let charge := 1 + (cfg.stk request).length + (cfg.stk destination).length + answer.length
        obtain ⟨hc_le, rest⟩ := within_shift _ limit bound charge (hw answer allowed)
        have ha : answer.length ≤ charge := by dsimp [charge]; omega
        have next_cap : height (BitOracleMachine.resume cfg destination next answer).stk + (bound - charge) ≤ cap := by
          have := reply_growth cfg destination next answer charge ha
          omega
        have next_prev : (cfg.stk request).length ≤ cap := (length_le_height cfg.stk request).trans hH
        have tail := ih _ (cfg.stk request) (wordTape answer) _ rest next_cap next_prev
        have shifted := costed_shift code cap limit _ 0 charge _ tail
        obtain ⟨used, hu, hr⟩ := reply_run code .hash cfg request destination next
          (cfg.stk request) (wordTape (cfg.stk request)) answer
        have cost := hash_bound cfg request destination next previous answer cap before used hH hp (by omega) hb hu
        have paid := cost.trans (credit cap charge (by dsimp [charge]; omega))
        have small := costed_weaken code cap limit _ _ (before + used) _ shifted (by omega)
        have result := costed_prefix code cap limit _ before used _ _ hr small
        simpa only [Nat.zero_add, charge, BitOracleTapeCall.incoming] using result
      | coin destination next =>
        rw [source_coin code fuel cfg source destination next hl hc] at hw ⊢
        have he := coin_issue code cfg source destination next hl hc (wordTape previous) oldAnswer
        refine ⟨2, (fun bit => .call .coin (BitOracleTapeCall.received cfg destination destination next []
          (wordTape previous) [bit])), (by exact he), ?_⟩
        intro bit allowed
        let charge := 2 + (cfg.stk destination).length
        obtain ⟨hc_le, rest⟩ := within_shift _ limit bound charge (hw bit allowed)
        have ha : [bit].length ≤ charge := by change 1 ≤ 2 + (cfg.stk destination).length; omega
        have next_cap : height (BitOracleMachine.resume cfg destination next [bit]).stk + (bound - charge) ≤ cap := by
          have := reply_growth cfg destination next [bit] charge ha
          omega
        have tail := ih _ previous (wordTape [bit]) _ rest next_cap hp
        have shifted := costed_shift code cap limit _ 0 charge _ tail
        obtain ⟨used, hu, hr⟩ := reply_run code .coin cfg destination destination next [] (wordTape previous) [bit]
        have cost := coin_bound cfg destination next bit cap used hH (by dsimp [charge] at hc_le; omega) hu
        have paid := cost.trans (credit cap charge (by dsimp [charge]; omega))
        have small := costed_weaken code cap limit _ _ (2 + used) _ shifted (by omega)
        exact costed_prefix code cap limit _ 2 used _ _ hr small

/-- Every allowed continuation fits the claimed total clock, including work
already spent before reaching a query boundary. -/
theorem costed_spent_le {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (cap limit bound spent : Nat) (cfg : State s l m)
    (h : Costed code cap limit oa spent cfg) (hw : Within limit bound oa) :
    spent ≤ unitCost cap * bound := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, previous, answer, hu, _⟩ := h
    have hb := Nat.mul_le_mul_left (unitCost cap) hw.2
    omega
  | queryBind q next ih =>
    obtain ⟨before, continuation, _, hr⟩ := h
    obtain ⟨answer, ha⟩ := allowed_nonempty limit q
    have hb := ih answer (spent + before) (continuation answer) (hr answer ha) (hw answer ha)
    omega

end ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
