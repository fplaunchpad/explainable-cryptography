import ExplainableCrypto.Helios.Computational.PrimeProgramOutputCallerSource
import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine

/-! Actual operand origin for Alice's second-component request. No machine run
is assumed here; the fixed caller derives its entry from these resident words. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptSource
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) : Fin 50 → List Bool :=
  (PrimeProgramOutputCaller.sourceResult slack g pk vote s live out).stk

/-- The selected nonce is the second original draw; its prefix and the first
nonce, encoded p0 and old raw context are already retained. -/
theorem source_inputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let old := words slack g pk vote s live out
    old 6 = p.bits ∧ old 16 = (primeGroupCoordinate g).val.bits ∧
    old 15 = (primeGroupCoordinate pk).val.bits ∧
    old 19 = SamplerOperands.input slack q [] ∧
    old 21 = scalarEncode out.1.2 ∧ old 20 = scalarEncode out.1.1 ∧
    old 22 = (q-1).bits ∧
    old 48 = (ballotProofBitCodec p q).encode (PrimeProgramProofSource.proof g pk vote out) ∧
    old 49 = (ballotBothCachesBitCodec p q).encode
      (PrimeProgramRepackSource.nextState g pk vote s out,live) ∧
    old 14 = PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- All six reused local scratch ports are empty in the actual reached state. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (j : Fin 6) :
    words slack g pk vote s live out ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- The second nonce is an arbitrary typed scalar here; in particular these
bounds do not add a false positivity premise needed by later zero-sum requests. -/
theorem nonce_bound (out : Draws (q:=q)) :
    out.1.2.val ≤ q-1 ∧ out.1.2.val.bits.length ≤ (q-1).size := by
  have h := Nat.le_sub_one_of_lt (ZMod.val_lt out.1.2)
  exact ⟨h,by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h⟩

/-- Runtime widths use the actual selected prefix and enlarged current saved
record; the raw predecessor's stale saved-size bound is not reused. -/
theorem source_lengths (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let old := words slack g pk vote s live out
    let N := (old 14).length
    (old 6).length = p.size ∧
    (old 16).length ≤ (p-1).size ∧ (old 15).length ≤ (p-1).size ∧
    (old 21).length ≤ groupRecordBitBound q ∧
    (old 48).length ≤ proofRecordBitBound p q ∧
    (old 49).length ≤ bothCachesBitBound p q (N+1) (N+1) N := by
  obtain ⟨hp,hg,hpk,_,hn,_,_,hproof,hsaved,hraw⟩ := source_inputs slack g pk vote s live out
  dsimp only at hp hg hpk hn hproof hsaved hraw ⊢
  rw [hp,hg,hpk,hn,hproof,hsaved,hraw]
  exact ⟨Nat.size_eq_bits_len _,
    by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_sub_one_of_lt (ZMod.val_lt (primeGroupCoordinate g))),
    by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_sub_one_of_lt (ZMod.val_lt (primeGroupCoordinate pk))),
    scalarEncode_length_le _,PrimeProgramProofSource.proof_length g pk vote out,
    PrimeProgramRepackSource.saved_length slack g pk vote s live out⟩

/-- Current saved state, not the original raw payload, is the continuation context. -/
theorem saved_not_stale (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    words slack g pk vote s live out 49 ≠ PrimeProgrammedStateSource.saved s live :=
  PrimeProgramRepackSource.saved_changed g pk vote s live out

private theorem present_words (old : Fin 50 → List Bool)
    (hw : ∀ j : Fin 6, old ⟨23+j.val,by omega⟩ = []) :
    old = PrimeSecondTranscriptMachine.inputWords (old 19) (old 21) (old 20)
      (old 22) (old 49) (old 6) (old 16) (old 15)
      (PrimeSecondTranscriptMachine.frame old) := by
  funext k
  fin_cases k
  all_goals first | rfl | exact hw 0 | exact hw 1 | exact hw 2 | exact hw 3 | exact hw 4 | exact hw 5

/-- Complete presentation for the fixed second-component layout. The old
p0 and raw context are in its arbitrary frame; current saved49 is shared directly. -/
theorem source_presentation (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    words slack g pk vote s live out =
      PrimeSecondTranscriptMachine.inputWords (SamplerOperands.input slack q [])
        (scalarEncode out.1.2) (scalarEncode out.1.1) (q-1).bits
        ((ballotBothCachesBitCodec p q).encode (PrimeProgramRepackSource.nextState g pk vote s out,live))
        p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        (PrimeSecondTranscriptMachine.frame (words slack g pk vote s live out)) := by
  obtain ⟨hp,hg,hpk,hr,hn,hn0,hm,_,hc,_⟩ := source_inputs slack g pk vote s live out
  simpa only [hp,hg,hpk,hr,hn,hn0,hm,hc] using
    present_words (words slack g pk vote s live out) (source_work slack g pk vote s live out)

#print axioms source_presentation
#print axioms source_inputs
#print axioms source_work
#print axioms nonce_bound
#print axioms source_lengths
#print axioms saved_not_stale
end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptSource
