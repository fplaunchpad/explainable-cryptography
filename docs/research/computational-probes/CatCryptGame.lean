import CatCryptCore.Crypto.Advantage

/-! Two-token board probe corresponding to VCVioGame. The adversary is a
probabilistic callback, isolated from the board's private heap location. -/

noncomputable section
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace HeliosLibraryProbe.CatCrypt

def boardLoc : Location := ⟨0, Bool → Bool⟩

def submit (weed token : Bool) : SPComp Bool := do
  let board ← SPComp.get boardLoc
  if weed && board token then
    return false
  else
    SPComp.set boardLoc (fun x => board x || x == token)
    return true

def call (adversary : Bool → SDistr Bool) (published : Bool) : SPComp Bool :=
  fun heap => (adversary published).bind fun token => SDistr.pure (token, heap)

def game (weed : Bool) (adversary : Bool → SDistr Bool) : SPComp Bool := do
  let published ← SPComp.sample Bool
  SPComp.set boardLoc (fun x => x == published)
  let token ← call adversary published
  submit weed token

def replay (token : Bool) : SDistr Bool := SDistr.pure token
def fresh (token : Bool) : SDistr Bool := SDistr.pure (!token)
def blind (_token : Bool) : SDistr Bool := SDistr.pure false

theorem rejection_preserves_board (token : Bool) (heap : Heap) :
    submit true token (heap.set boardLoc (fun x => x == token)) =
      SDistr.pure (false, heap.set boardLoc (fun x => x == token)) := by
  simp [submit, SPComp.bind, SPComp.get, SPComp.pure, SDistr.pure_bind]

/-- Exact output probability, marginalizing over every possible final heap. -/
theorem acceptance_probability (weed : Bool) (f : Bool → Bool) :
    prTrue (game weed (fun b => SDistr.pure (f b))) Heap.empty =
      ∑ b : Bool, (2 : ℝ≥0∞)⁻¹ * (if weed && (f b == b) then 0 else 1) := by
  simp only [game, SPComp.monad_bind_eq]
  rw [prTrue_bind_sample]
  congr 1
  funext b
  by_cases h : f b = b <;> cases weed <;>
    simp [prTrue, call, submit, SPComp.bind, SPComp.set, SPComp.get,
      SPComp.pure, SDistr.pure_bind, h] <;> simp [eq_comm]

theorem replay_rejected_with_weeding :
    prTrue (game true replay) Heap.empty = 0 := by
  change prTrue (game true (fun b => SDistr.pure b)) Heap.empty = 0
  rw [acceptance_probability]
  simp

theorem replay_accepted_without_weeding :
    prTrue (game false replay) Heap.empty = 1 := by
  change prTrue (game false (fun b => SDistr.pure b)) Heap.empty = 1
  rw [acceptance_probability]
  norm_num [ENNReal.mul_inv_cancel]

theorem fresh_accepted (weed : Bool) :
    prTrue (game weed fresh) Heap.empty = 1 := by
  change prTrue (game weed (fun b => SDistr.pure (!b))) Heap.empty = 1
  rw [acceptance_probability]
  cases weed <;> norm_num [ENNReal.mul_inv_cancel]

theorem blind_accepted_half :
    prTrue (game true blind) Heap.empty = 1 / 2 := by
  change prTrue (game true (fun _ => SDistr.pure false)) Heap.empty = 1 / 2
  rw [acceptance_probability]
  norm_num [ENNReal.mul_inv_cancel]

theorem fresh_updates_board (token : Bool) (weed : Bool) (heap : Heap) :
    submit weed (!token) (heap.set boardLoc (fun x => x == token)) =
      SDistr.pure (true, heap.set boardLoc (fun _ => true)) := by
  have hb : (fun x => x == token || x == !token) = (fun _ => true) := by
    funext x
    cases x <;> cases token <;> rfl
  cases weed <;>
    simp [submit, SPComp.bind, SPComp.get, SPComp.set, SPComp.pure,
      SDistr.pure_bind, hb]

#print axioms rejection_preserves_board
#print axioms acceptance_probability
#print axioms replay_rejected_with_weeding
#print axioms replay_accepted_without_weeding
#print axioms fresh_accepted
#print axioms blind_accepted_half
#print axioms fresh_updates_board

end HeliosLibraryProbe.CatCrypt
