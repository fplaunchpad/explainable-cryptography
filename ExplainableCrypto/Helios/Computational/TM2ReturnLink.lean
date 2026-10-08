import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Size

/-! Link a finite-control subroutine on unchanged tapes and local memory.
Halt becomes a return jump. Padded halted runs transfer with no greater fuel. -/
namespace ExplainableCrypto.Helios.Computational.TM2ReturnLink
open Turing.TM2
variable {K : Type*} {Γ : K → Type*} {L R V : Type*} [DecidableEq K]

def redirect (labels : L → R) (ret : R) : Stmt Γ L V → Stmt Γ R V
  | .push k f s => .push k f (redirect labels ret s)
  | .peek k f s => .peek k f (redirect labels ret s)
  | .pop k f s => .pop k f (redirect labels ret s)
  | .load f s => .load f (redirect labels ret s)
  | .branch f a b => .branch f (redirect labels ret a) (redirect labels ret b)
  | .goto f => .goto (fun v => labels (f v))
  | .halt => .goto (fun _ => ret)

def embed (labels : L → R) (ret : R) (c : Cfg Γ L V) : Cfg Γ R V :=
  ⟨some (c.l.elim ret labels),c.var,c.stk⟩

def tick (p : L → Stmt Γ L V) (c : Cfg Γ L V) : Cfg Γ L V :=
  (step p c).getD c

theorem redirect_step (labels : L → R) (ret : R) (s : Stmt Γ L V)
    (v : V) (tapes : ∀ k, List (Γ k)) :
    stepAux (redirect labels ret s) v tapes = embed labels ret (stepAux s v tapes) := by
  induction s generalizing v tapes with
  | push k f s ih => exact ih _ _
  | peek k f s ih => exact ih _ _
  | pop k f s ih => exact ih _ _
  | load f s ih => exact ih _ _
  | branch f a b ia ib => cases h : f v <;> simp [redirect,stepAux,h,ia,ib]
  | goto f => rfl
  | halt => rfl

/-- A completed subroutine executes in its caller, returning with all data
unchanged from its own result. No assumption about first-halt fuel is needed. -/
theorem run (p : L → Stmt Γ L V) (q : R → Stmt Γ R V)
    (labels : L → R) (ret : R)
    (hq : ∀ l, q (labels l) = redirect labels ret (p l))
    (fuel : Nat) (c : Cfg Γ L V) (h : ((tick p)^[fuel] c).l = none) :
    ∃ used ≤ fuel, (tick q)^[used] (embed labels ret c) = embed labels ret ((tick p)^[fuel] c) := by
  induction fuel generalizing c with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ fuel ih =>
    cases c with
    | mk l v tapes =>
      cases l with
      | none =>
        have hf : tick p ⟨none,v,tapes⟩ = ⟨none,v,tapes⟩ := rfl
        have hi := Function.iterate_fixed hf (fuel+1)
        exact ⟨0,Nat.zero_le _,by rw [hi]; rfl⟩
      | some l =>
        have hs : tick q (embed labels ret ⟨some l,v,tapes⟩) =
            embed labels ret (tick p ⟨some l,v,tapes⟩) := by
          simpa only [tick,embed,Option.elim,step,Option.getD_some,hq] using
            redirect_step labels ret (p l) v tapes
        rw [Function.iterate_succ_apply] at h
        obtain ⟨used,hu,he⟩ := ih _ h
        refine ⟨used+1,by omega,?_⟩
        rw [Function.iterate_succ_apply,hs,he,Function.iterate_succ_apply]

#print axioms redirect_step
#print axioms run
end ExplainableCrypto.Helios.Computational.TM2ReturnLink
