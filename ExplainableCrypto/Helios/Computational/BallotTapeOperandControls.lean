import ExplainableCrypto.Helios.Computational.BallotReplayTape
import Mathlib.Data.Nat.Size

/-! A supported one-event tape can retain an arbitrarily wide uniform range tag.
This refutes inferring binary operand bounds from total query counts alone. -/
namespace ExplainableCrypto.Helios.Computational.BallotTapeOperandControls
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

def wideQuery (k : Nat) : ProbComp Unit :=
  liftM (unifSpec.query (2^k)) >>= fun _ => pure ()

def zeroTape (k : Nat) : PFunctor.TraceList unifSpec.toPFunctor :=
  [⟨2^k,(0 : Fin (2^k+1))⟩]

def tagBits (tape : PFunctor.TraceList unifSpec.toPFunctor) : Nat :=
  (List.map (fun event => event.1.bits.length) tape).sum

/-- Actual query cost is one; actual collection supports the displayed tape,
which has one event but k+1 binary tag bits. The answer itself is zero. -/
theorem wide_tape (k : Nat) : (wideQuery k).IsTotalQueryBound 1 ∧
    zeroTape k ∈ support (ballotReplayCollectTape (wideQuery k)) ∧
    (zeroTape k).length = 1 ∧ tagBits (zeroTape k) = k+1 := by
  refine ⟨?_,?_,rfl,?_⟩
  · exact ⟨Nat.zero_lt_succ 0,fun _ => trivial⟩
  · change zeroTape k ∈ support
      (liftM (unifSpec.query (2^k)) >>= fun a => pure [⟨2^k,a⟩])
    rw [mem_support_bind_iff]
    exact ⟨0,mem_support_query _ _,by simp [zeroTape]⟩
  · simp [tagBits,zeroTape,Nat.size_eq_bits_len,Nat.size_pow]

/-- No function of tape length alone bounds even the binary uniform tags in
all supported tapes of these one-query computations. -/
theorem no_count_only_tag_bound : ¬ ∃ bound : Nat → Nat, ∀ k tape,
    tape ∈ support (ballotReplayCollectTape (wideQuery k)) →
      tagBits tape ≤ bound tape.length := by
  rintro ⟨bound,h⟩
  have hw := wide_tape (bound 1)
  have he := h (bound 1) (zeroTape (bound 1)) hw.2.1
  rw [hw.2.2.1,hw.2.2.2] at he
  omega

/-- Independent small fixture: a binary coin uses the literal tag bit [true]. -/
theorem coin_tag_fixture :
    List.map (fun event => event.1.bits) (zeroTape 0) = [[true]] ∧
      tagBits (zeroTape 0) = 1 := by decide

#print axioms wide_tape
#print axioms no_count_only_tag_bound
#print axioms coin_tag_fixture
end ExplainableCrypto.Helios.Computational.BallotTapeOperandControls
