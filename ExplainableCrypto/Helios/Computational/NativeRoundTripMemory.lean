import ExplainableCrypto.Helios.Computational.TM2MemoryFrame
import ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates

/-! Finite-memory framing needed by the native round trip.
Candidate: composing the existing memory frame and finite coordinate change
retains saved memory, every stack, every step and its local/oracle charge.
Falsifiers: a local load changes saved heads, a branch reads saved instead of
local memory, or oracle replacement loses the saved return address.
Formal oracle: statement/run equalities below. Independent controls use literal
product coordinates and a destructive local load. No new tape semantics,
compiler coverage, or live-padding theorem is asserted. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTripMemory
open Turing.TM2 OracleComp OracleSpec
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

variable {s l m saved : Nat}

def pack (w : Fin saved) (v : Fin m) : Fin (saved*m) := finProdFinEquiv (w,v)
def unpack (v : Fin (saved*m)) : Fin saved × Fin m := finProdFinEquiv.symm v

theorem unpack_pack (w : Fin saved) (v : Fin m) : unpack (pack w v) = (w,v) :=
  Equiv.symm_apply_apply _ _

/-- Executable composition of the two existing transformations. -/
def stmt (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    Stmt (fun _ : Fin s => Bool) (Fin l) (Fin (saved*m)) :=
  TM2FiniteCoordinates.translate (Equiv.refl _) (Equiv.refl _) finProdFinEquiv
    (TM2MemoryFrame.liftStmt (W := Fin saved) q)

def embed (w : Fin saved) (cfg : BitOracleMachine.Config s l m) :
    BitOracleMachine.Config s l (saved*m) := ⟨cfg.l,pack w cfg.var,cfg.stk⟩

theorem statement (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (w : Fin saved) (v : Fin m) (words : Fin s → List Bool) :
    stepAux (stmt q) (pack w v) words = embed w (stepAux q v words) := by
  have h := TM2FiniteCoordinates.statement (Equiv.refl (Fin s)) (Equiv.refl (Fin l))
    (finProdFinEquiv : Fin saved × Fin m ≃ Fin (saved*m))
    (TM2MemoryFrame.liftStmt q) (w,v) words
  rw [TM2MemoryFrame.statement] at h
  have hd (xs : Fin s → List Bool) :
      TM2FiniteCoordinates.data (Equiv.refl (Fin s)) xs = xs := rfl
  simpa [stmt,pack,embed,TM2FiniteCoordinates.present,TM2MemoryFrame.embed,hd] using h

theorem local_cost (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    BitOracleMachine.localCost (stmt (saved := saved) q) = BitOracleMachine.localCost q := by
  induction q <;> simp_all [stmt,TM2FiniteCoordinates.translate,TM2MemoryFrame.liftStmt,
    BitOracleMachine.localCost]

theorem tick (p : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (w : Fin saved) (cfg : BitOracleMachine.Config s l m) :
    TM2ReturnLink.tick (fun q => stmt (p q)) (embed w cfg) =
      embed w (TM2ReturnLink.tick p cfg) := by
  rcases cfg with ⟨label,v,words⟩
  cases label with
  | none => rfl
  | some label => exact statement (p label) w v words

theorem run (p : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (w : Fin saved) (fuel : Nat) (cfg : BitOracleMachine.Config s l m) :
    (TM2ReturnLink.tick (fun q => stmt (p q)))^[fuel] (embed w cfg) =
      embed w ((TM2ReturnLink.tick p)^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply,tick,ih,Function.iterate_succ_apply]

def command (q : BitOracleMachine.Command s l m) : BitOracleMachine.Command s l (saved*m) :=
  match q with
  | .compute p => .compute (stmt p)
  | .coin destination next => .coin destination next
  | .hash request destination next => .hash request destination next

def code (saved : Nat) (p : BitOracleMachine.Code s l m) : BitOracleMachine.Code s l (saved*m) :=
  fun label => command (p label)

theorem step (p : BitOracleMachine.Code s l m) (w : Fin saved)
    (cfg : BitOracleMachine.Config s l m) :
    BitOracleMachine.step (code saved p) (embed w cfg) =
      (fun out => (embed w out.1,out.2)) <$> BitOracleMachine.step p cfg := by
  rcases cfg with ⟨label,v,words⟩
  cases label with
  | none => simp [BitOracleMachine.step,embed]
  | some label =>
    cases h : p label with
    | compute q => simp [BitOracleMachine.step,code,command,h,embed,statement,local_cost]
    | coin destination next => simp [BitOracleMachine.step,code,command,h,
        BitOracleMachine.resume,embed]
    | hash request destination next => simp [BitOracleMachine.step,code,command,h,
        BitOracleMachine.resume,embed]

theorem oracle_run (p : BitOracleMachine.Code s l m) (w : Fin saved)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) :
    BitOracleMachine.run (code saved p) fuel (embed w cfg) =
      (fun out => (embed w out.1,out.2)) <$> BitOracleMachine.run p fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp [BitOracleMachine.run]
  | succ fuel ih =>
    rw [BitOracleMachine.run,step]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    simp only [BitOracleMachine.run,bind_assoc,pure_bind]
    apply bind_congr
    intro first
    rw [ih]
    simp [map_eq_bind_pure_comp,bind_assoc]

/-- Redirecting halt to a live return address does not change statement cost. -/
theorem redirect_cost {r : Nat} (labels : Fin l → Fin r) (ret : Fin r)
    (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    BitOracleMachine.localCost (TM2ReturnLink.redirect labels ret q) =
      BitOracleMachine.localCost q := by
  induction q <;> simp_all [TM2ReturnLink.redirect,BitOracleMachine.localCost]

/-- Execute only the actual deterministic subroutine prefix, ending at its
live return address. Padded source fuel supplies a bound, never live padding.
The target is unrestricted outside the embedded source instructions. -/
theorem live_prefix {r : Nat}
    (p : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (q : BitOracleMachine.Code s r m) (labels : Fin l → Fin r) (ret : Fin r)
    (hq : ∀ label, q (labels label) = .compute (TM2ReturnLink.redirect labels ret (p label)))
    (bound : Nat) (hcost : ∀ label, BitOracleMachine.localCost (p label) ≤ bound)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m)
    (halted : ((TM2ReturnLink.tick p)^[fuel] cfg).l = none) :
    ∃ used ≤ fuel, ∃ charge ≤ bound*used,
      BitOracleMachine.run q used (TM2ReturnLink.embed labels ret cfg) =
        pure (TM2ReturnLink.embed labels ret ((TM2ReturnLink.tick p)^[fuel] cfg),charge) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0,le_rfl,0,le_rfl,rfl⟩
  | succ fuel ih =>
    rcases cfg with ⟨label,v,words⟩
    cases label with
    | none =>
      have hi := Function.iterate_fixed
        (show TM2ReturnLink.tick p (⟨none,v,words⟩ : BitOracleMachine.Config s l m) =
          ⟨none,v,words⟩ from rfl) (fuel+1)
      refine ⟨0,Nat.zero_le _,0,le_rfl,?_⟩
      rw [hi]
      rfl
    | some label =>
      rw [Function.iterate_succ_apply] at halted
      obtain ⟨used,hu,charge,hcharge,hrun⟩ := ih _ halted
      have hs : BitOracleMachine.step q
          (TM2ReturnLink.embed labels ret (⟨some label,v,words⟩ : BitOracleMachine.Config s l m)) =
          pure (TM2ReturnLink.embed labels ret
            (TM2ReturnLink.tick p ⟨some label,v,words⟩),BitOracleMachine.localCost (p label)) := by
        simp only [BitOracleMachine.step,TM2ReturnLink.embed,Option.elim,hq,
          TM2ReturnLink.redirect_step,redirect_cost]
        rfl
      refine ⟨used+1,by omega,BitOracleMachine.localCost (p label)+charge,?_,?_⟩
      · have hc := hcost label
        rw [Nat.mul_add,Nat.mul_one]
        omega
      · rw [BitOracleMachine.run,hs]
        simp only [pure_bind]
        rw [hrun]
        simp only [pure_bind,Function.iterate_succ_apply]

/-- Independent product coordinate: saved 2, local 1 in a 4-by-3 memory. -/
theorem pack_literal : pack (2 : Fin 4) (1 : Fin 3) = 7 := by decide +kernel

private def loadControl : Stmt (fun _ : Fin 1 => Bool) (Fin 1) (Fin 3) :=
  .load (fun _ => 2) .halt

/-- A destructive local load updates only the local component. -/
theorem load_retains_saved :
    stepAux (stmt (saved := 4) loadControl) 7 (fun _ => [true,false]) =
      (⟨none,8,fun _ => [true,false]⟩ : BitOracleMachine.Config 1 1 12) := by rfl

theorem load_not_reset_saved :
    (stepAux (stmt (saved := 4) loadControl) 7 (fun _ => [true,false])).var ≠ 2 := by
  decide +kernel

private def liveControl : BitOracleMachine.Code 1 2 1 :=
  fun q => if q = 0 then .compute (.goto (fun _ => 1)) else .coin 0 1

private def liveInitial : BitOracleMachine.Config 1 2 1 :=
  ⟨some 0,0,fun _ => [true,false]⟩

/-- The selected return is actually live: the exact one-tick prefix has not
consumed its following coin event. -/
theorem live_return_control :
    BitOracleMachine.run liveControl 1 liveInitial =
      pure (⟨some 1,0,fun _ => [true,false]⟩,1) := by rfl

/-- One extra tick consumes the real continuation event, so padding is invalid. -/
theorem live_padding_queries :
    OracleComp.isPure (BitOracleMachine.run liveControl 2 liveInitial) = false := by rfl

theorem live_padding_not_equal :
    BitOracleMachine.run liveControl 2 liveInitial ≠
      BitOracleMachine.run liveControl 1 liveInitial := by
  intro h
  have hi := congrArg OracleComp.isPure h
  change false = true at hi
  cases hi

end ExplainableCrypto.Helios.Computational.NativeRoundTripMemory
