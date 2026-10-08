import ExplainableCrypto.Helios.Computational.BitOracleTapeCorrespondence

/-! Charge-derived height growth and one polynomial cap for actual tape regions.
These bounds feed the common-clock source proof, not a new execution model. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeCap
open Turing TM2TapeRuns BitOraclePortTransfer

/-- A uniform allowance for one complete active source transition. -/
def unitCost (cap : Nat) : Nat := 650 * (cap + 1) ^ 2

theorem charge_pos {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    0 < BitOracleMachine.localCost q := by
  cases q <;> simp [BitOracleMachine.localCost]

theorem accesses_le_charge {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    TM2TapeCost.accesses q ≤ BitOracleMachine.localCost q := by
  induction q <;> simp_all [TM2TapeCost.accesses, BitOracleMachine.localCost] <;> omega

private theorem height_le {K : Type} [Fintype K] (words : K → List Bool) (H : Nat)
    (h : ∀ k, (words k).length ≤ H) : height words ≤ H :=
  Finset.sup_le (fun k _ => h k)

/-- Empty private columns do not increase the caller's stack height. -/
theorem framed_height {s l m : Nat} (cfg : BitOracleMachine.Config s l m) :
    height (BitOracleTapeCompute.framed cfg).stk ≤ height cfg.stk := by
  apply height_le
  intro port
  cases port with
  | inl i => exact length_le_height cfg.stk i
  | inr bit => exact Nat.zero_le _

/-- The executed local statement pays for every possible increase in height. -/
theorem compute_growth {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (cfg : BitOracleMachine.Config s l m) :
    height (TM2.stepAux q cfg.var cfg.stk).stk ≤ height cfg.stk + BitOracleMachine.localCost q := by
  apply height_le
  intro i
  exact (TM2TapeCost.statement_height q (height cfg.stk) cfg.var cfg.stk
    (length_le_height cfg.stk) i).trans (Nat.add_le_add_left (accesses_le_charge q) _)

/-- Received word length pays for successor growth, including an initially empty caller. -/
theorem reply_growth {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (answer : List Bool) (charge : Nat)
    (ha : answer.length ≤ charge) :
    height (BitOracleMachine.resume cfg destination next answer).stk ≤ height cfg.stk + charge := by
  apply height_le
  intro i
  by_cases h : i = destination
  · subst i
    simpa only [BitOracleMachine.resume, Function.update_self] using
      ha.trans (Nat.le_add_left _ _)
  · simpa only [BitOracleMachine.resume, Function.update_of_ne h] using
      (length_le_height cfg.stk i).trans (Nat.le_add_right _ _)

private theorem request_height {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) :
    height (requestStart cfg request next []).stk ≤ height cfg.stk := by
  apply height_le
  intro port
  cases port with
  | inl i => rw [(request_start cfg request i next []).1]; exact length_le_height cfg.stk i
  | inr bit => cases bit <;> exact Nat.zero_le _

private theorem reply_height {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (answer : List Bool) (cap : Nat)
    (hH : height cfg.stk ≤ cap) (ha : answer.length ≤ cap) :
    height (start cfg destination next answer).stk ≤ cap := by
  apply height_le
  intro port
  cases port with
  | inl i => rw [start_original]; exact (length_le_height cfg.stk i).trans hH
  | inr bit => cases bit with
    | false => exact ha
    | true => exact Nat.zero_le _

private theorem transfer_bound (cap B H : Nat) (hB : B ≤ 4 * (cap + 1)) (hH : H ≤ cap) :
    B * (6 * H + 18 * B + 7) ≤ 316 * (cap + 1) ^ 2 := by
  have h := Nat.mul_le_mul hB (by omega : 6 * H + 18 * B + 7 ≤ 79 * (cap + 1))
  nlinarith

/-- The actual ordinary-statement allowance is bounded by the global cap. -/
theorem compute_bound {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) (cap used : Nat)
    (hH : height cfg.stk ≤ cap) (ha : TM2TapeCost.accesses q ≤ cap)
    (hu : used ≤ 3 + TM2TapeCost.accesses q *
      (2 * (height (BitOracleTapeCompute.framed cfg).stk + TM2TapeCost.accesses q) + 2)) :
    used ≤ unitCost cap := by
  have hh := (framed_height cfg).trans hH
  have h := Nat.mul_le_mul ha (by omega :
    2 * (height (BitOracleTapeCompute.framed cfg).stk + TM2TapeCost.accesses q) + 2 ≤ 4 * cap + 2)
  unfold unitCost
  nlinarith

/-- Actual hash preparation, export, native event, loading, response and return
fit one cap. All request/response layout heights are derived from the caller. -/
theorem hash_bound {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (previous answer : List Bool)
    (cap before after : Nat) (hH : height cfg.stk ≤ cap)
    (hp : previous.length ≤ cap) (ha : answer.length ≤ cap)
    (hb : before ≤ (2 * (cfg.stk request).length + 4) *
      (6 * height (requestStart cfg request next []).stk + 18 * (2 * (cfg.stk request).length + 4) + 7) +
      previous.length + 2 * (cfg.stk request).length + 7)
    (ht : after ≤ 3 * (cfg.stk request).length + 4 * answer.length + 9 +
      ((cfg.stk destination).length + 3 * answer.length + 4) *
        (6 * height (start cfg destination next answer).stk +
          18 * ((cfg.stk destination).length + 3 * answer.length + 4) + 7)) :
    before + after ≤ unitCost cap := by
  have hr := (length_le_height cfg.stk request).trans hH
  have hd := (length_le_height cfg.stk destination).trans hH
  have first := transfer_bound cap (2 * (cfg.stk request).length + 4)
    (height (requestStart cfg request next []).stk) (by omega) ((request_height cfg request next).trans hH)
  have second := transfer_bound cap ((cfg.stk destination).length + 3 * answer.length + 4)
    (height (start cfg destination next answer).stk) (by omega) (reply_height cfg destination next answer cap hH ha)
  unfold unitCost
  nlinarith

/-- The actual coin event and consuming reply also fit the same cap. -/
theorem coin_bound {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (bit : Bool) (cap after : Nat)
    (hH : height cfg.stk ≤ cap) (hc : 1 ≤ cap)
    (ht : after ≤ 3 * ([] : List Bool).length + 4 * [bit].length + 9 +
      ((cfg.stk destination).length + 3 * [bit].length + 4) *
        (6 * height (start cfg destination next [bit]).stk +
          18 * ((cfg.stk destination).length + 3 * [bit].length + 4) + 7)) :
    2 + after ≤ unitCost cap := by
  have hd := (length_le_height cfg.stk destination).trans hH
  have second := transfer_bound cap ((cfg.stk destination).length + 3 * [bit].length + 4)
    (height (start cfg destination next [bit]).stk)
    (by simp only [List.length_cons, List.length_nil]; omega)
    (reply_height cfg destination next [bit] cap hH (by simpa using hc))
  simp only [List.length_cons, List.length_nil] at ht second
  unfold unitCost
  nlinarith

end ExplainableCrypto.Helios.Computational.BitOracleTapeCap
