import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! A two-token bulletin-board interface probe, not a cryptographic model.
The adversary receives the sampled public token before choosing its submission.
Rejection is an observable Boolean and preserves the board. -/

open OracleComp OracleSpec

namespace HeliosLibraryProbe.VCVio

abbrev Board := List Bool

def submit (weed : Bool) (token : Bool) : StateT Board ProbComp Bool := do
  let board ← get
  if weed && board.contains token then
    return false
  else
    set (board ++ [token])
    return true

def game (weed : Bool) (adversary : Bool → ProbComp Bool) :
    ProbComp (Bool × Board) := do
  let published ← $ᵗ Bool
  let token ← adversary published
  (submit weed token).run [published]

def accepted (weed : Bool) (adversary : Bool → ProbComp Bool) : ProbComp Bool :=
  Prod.fst <$> game weed adversary

def replay (token : Bool) : ProbComp Bool := pure token
def fresh (token : Bool) : ProbComp Bool := pure (!token)
def blind (_token : Bool) : ProbComp Bool := pure false

theorem rejection_preserves_board (token : Bool) :
    (submit true token).run [token] = pure (false, [token]) := by
  simp [submit, StateT.run_bind, StateT.run_pure]

theorem fresh_appends (token : Bool) (weed : Bool) :
    (submit weed (!token)).run [token] = pure (true, [token, !token]) := by
  cases token <;> cases weed <;> rfl

theorem replay_accepted_without_weeding :
    Pr[= true | accepted false replay] = 1 := by
  simp [accepted, game, replay, submit, StateT.run_bind]

theorem replay_rejected_with_weeding :
    Pr[= true | accepted true replay] = 0 := by
  simp [accepted, game, replay, rejection_preserves_board]

theorem fresh_accepted (weed : Bool) :
    Pr[= true | accepted weed fresh] = 1 := by
  simp [accepted, game, fresh, fresh_appends]

theorem blind_accepted_half :
    Pr[= true | accepted true blind] = 1 / 2 := by
  simp [accepted, game, blind, probOutput_bind_eq_tsum,
    submit, StateT.run_bind, StateT.run_pure]

#print axioms rejection_preserves_board
#print axioms fresh_appends
#print axioms replay_accepted_without_weeding
#print axioms replay_rejected_with_weeding
#print axioms fresh_accepted
#print axioms blind_accepted_half

end HeliosLibraryProbe.VCVio
