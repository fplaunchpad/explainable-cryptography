import ExplainableCrypto.Helios.Computational.CacheRequestMachineRun
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A pointwise polynomial cap for the existing loaded request clock. Public
modulus widths, all three loaded payload lengths and unary sampling slack remain
explicit. This bounds the proved request component, not a whole adaptive caller.
All helper estimates below are local arithmetic on existing cost definitions. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestMachine
set_option maxRecDepth 8192

private theorem size_self (n : Nat) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self

private theorem widths {p q u : Nat} (hu : 1 ≤ u) (hp : p.size ≤ u) (hq : q.size ≤ u) :
    keyRecordBitBound p ≤ 89*u ∧ groupRecordBitBound q ≤ 3*u ∧ cacheEntryBitBound p q ≤ 283*u := by
  have hps := Nat.size_le_size (Nat.sub_le p 1)
  have hqs := Nat.size_le_size (Nat.sub_le q 1)
  have gp : groupRecordBitBound p ≤ 3*u := by unfold groupRecordBitBound; omega
  have gq : groupRecordBitBound q ≤ 3*u := by unfold groupRecordBitBound; omega
  have hgs := size_self (groupRecordBitBound p)
  have hk : keyRecordBitBound p ≤ 89*u := by unfold keyRecordBitBound; omega
  have hks := size_self (keyRecordBitBound p)
  have has := size_self (groupRecordBitBound q)
  refine ⟨hk,gq,?_⟩
  unfold cacheEntryBitBound
  omega

private theorem frame_cost_le {n u c : Nat} (hu : 1 ≤ u) (hn : n ≤ c*u) :
    FrameWriteMachine.cost n ≤ (2*c*c+8*c+5)*u^2 := by
  have hs := size_self n
  have hm := Nat.mul_le_mul_left n hs
  have hn2 := Nat.mul_le_mul hn hn
  have hu2 : u ≤ u^2 := by nlinarith
  unfold FrameWriteMachine.cost
  nlinarith

private theorem iteration_le {p q n u : Nat} (hu : 1 ≤ u)
    (hp : p.size ≤ u) (hq : q.size ≤ u) (hn : n ≤ u) :
    CacheLookupMachine.iterationCost p q n ≤ 178599*u^2 := by
  obtain ⟨hk,ha,he⟩ := widths hu hp hq
  have hks := size_self (keyRecordBitBound p)
  have has := size_self (groupRecordBitBound q)
  have hes := size_self (cacheEntryBitBound p q)
  have hns := (size_self n).trans hn
  have hk2 := Nat.mul_le_mul hk hk
  have ha2 := Nat.mul_le_mul ha ha
  have he2 := Nat.mul_le_mul he he
  have hkm := Nat.mul_le_mul_left (keyRecordBitBound p) hks
  have ham := Nat.mul_le_mul_left (groupRecordBitBound q) has
  have hem := Nat.mul_le_mul_left (cacheEntryBitBound p q) hes
  have hu2 : u ≤ u^2 := by nlinarith
  unfold CacheLookupMachine.iterationCost CacheLookupMachine.fieldCost CacheLookupMachine.entryCost
  nlinarith

private theorem read_cost_le {p q u C : Nat} (hu : 1 ≤ u)
    (hp : p.size ≤ u) (hq : q.size ≤ u) (hc : C ≤ u) :
    CacheReadMachine.cost p q C C ≤ 178620*u^3 := by
  have hi := iteration_le hu hp hq hc
  have hm := Nat.mul_le_mul hc hi
  have hs := (size_self C).trans hc
  have hq' := (Nat.size_le_size (Nat.sub_le q 1)).trans hq
  have hu3 : u ≤ u^3 := by nlinarith [Nat.mul_le_mul_left (u*u) hu]
  unfold CacheReadMachine.cost
  nlinarith

private theorem insert_cost_le {p q u C : Nat} (hu : 1 ≤ u)
    (hp : p.size ≤ u) (hq : q.size ≤ u) (hc : C ≤ u) :
    CacheInsertMachine.cost p q C C ≤ 357882*u^3 := by
  obtain ⟨hk,ha,he⟩ := widths hu hp hq
  have hfk := frame_cost_le hu hk
  have hfa := frame_cost_le hu ha
  have hfe := frame_cost_le hu he
  have hi := iteration_le hu hp hq hc
  have hm := Nat.mul_le_mul hc hi
  have hs := (size_self C).trans hc
  have ht : (C+1).size ≤ 2*u := by have := size_self (C+1); omega
  have hu2 : u ≤ u^2 := by nlinarith
  have hu3 : u^2 ≤ u^3 := by nlinarith [Nat.mul_le_mul_left (u*u) hu]
  unfold CacheInsertMachine.cost CacheInsertMachine.builderCost
  norm_num at hfk hfa hfe
  nlinarith

private theorem append_cost_le {p q u L : Nat} (hu : 1 ≤ u)
    (hp : p.size ≤ u) (hq : q.size ≤ u) (hl : L ≤ u) :
    LogAppendMachine.cost L (keyRecordBitBound p) L ≤ 16767*u^2 := by
  have hk := (widths hu hp hq).1
  have hf := frame_cost_le hu hk
  have hs := (size_self L).trans hl
  have ht : (L+1).size ≤ 2*u := by have := size_self (L+1); omega
  have hu2 : u ≤ u^2 := by nlinarith
  unfold LogAppendMachine.cost
  norm_num at hf
  nlinarith

private theorem appended_size_le {p q u L : Nat} (hu : 1 ≤ u)
    (hp : p.size ≤ u) (hq : q.size ≤ u) (hl : L ≤ u) :
    bitListSize (keyRecordBitBound p) (L+1) ≤ 541*u^2 := by
  have hk := (widths hu hp hq).1
  have hs := size_self (keyRecordBitBound p)
  have hl' : L+1 ≤ 2*u := by omega
  have ht : (L+1).size ≤ 2*u := (size_self _).trans hl'
  have hj : 2*(keyRecordBitBound p).size+1+keyRecordBitBound p ≤ 268*u := by omega
  have hm := Nat.mul_le_mul hl' hj
  have hu2 : u ≤ u^2 := by nlinarith
  unfold bitListSize
  nlinarith

private theorem sampler_clock_le {q slack u : Nat} (hu : 1 ≤ u)
    (hq : q.size ≤ u) (hs : slack ≤ u) :
    CacheHashMachine.sampleClock slack q ≤ 89*u^2 := by
  have hq' := (Nat.size_le_size (Nat.sub_le q 1)).trans hq
  have hw : q.size+slack ≤ 2*u := by omega
  have hb : 8*q.size+17 ≤ 8*u+17 := by omega
  have hm := Nat.mul_le_mul hw hb
  have hu2 : u ≤ u^2 := by nlinarith
  unfold CacheHashMachine.sampleClock PreparedScalarMachine.clock PreparedScalarMachine.width
    SamplerOperands.clock SamplerOperands.range CoinScalarMachine.clock CoinModuloMachine.clock
  simp only [Bool.false_eq_true,ite_false,SamplerOperands.input,List.length_append,
    List.length_replicate,List.length_cons,List.length_nil,uniformNatEncode_length]
  nlinarith

private theorem loader_clock_le {K C L R u : Nat} (hu : 1 ≤ u)
    (hk : K ≤ u) (hc : C ≤ u) (hl : L ≤ u) (hr : R ≤ 5*u) :
    CacheRequestInput.lengthClock K C L R ≤ 145*u^2 := by
  have bound {n c : Nat} (hn : n ≤ c*u) :
      3*n.size+7+n*(2*n.size+3) ≤ (2*c*c+6*c+7)*u^2 := by
    have hs := size_self n
    have hm := Nat.mul_le_mul_left n hs
    have hn2 := Nat.mul_le_mul hn hn
    have hu2 : u ≤ u^2 := by nlinarith
    nlinarith
  have hK := bound (c := 1) (by simpa using hk)
  have hC := bound (c := 1) (by simpa using hc)
  have hL := bound (c := 1) (by simpa using hl)
  have hR := bound hr
  unfold CacheRequestInput.lengthClock
  norm_num at hK hC hL hR
  nlinarith

/-- Pointwise cubic cap for the existing complete loaded-input request clock.
The fixed probe-access factor and public modulus widths remain explicit. -/
theorem loadedClock_le_cubic (p q K C L slack : Nat) :
    loadedClock p q K C L slack ≤
      1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1)*
        (p.size+q.size+K+C+L+slack+1)^3 := by
  let u := p.size+q.size+K+C+L+slack+1
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hp : p.size ≤ u := by dsimp [u]; omega
  have hq : q.size ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hc : C ≤ u := by dsimp [u]; omega
  have hl : L ≤ u := by dsimp [u]; omega
  have hs : slack ≤ u := by dsimp [u]; omega
  have hr : slack+2*q.size+2 ≤ 5*u := by omega
  have hK := (widths hu hp hq).1
  have hq' := (Nat.size_le_size (Nat.sub_le q 1)).trans hq
  have hload := loader_clock_le hu hk hc hl hr
  have hread := read_cost_le hu hp hq hc
  have hins := insert_cost_le hu hp hq hc
  have happ := append_cost_le hu hp hq hl
  have hj := appended_size_le hu hp hq hl
  have hsample := sampler_clock_le hu hq hs
  have hmul := Nat.mul_le_mul_right (TM2TapeRuns.codeAccesses CacheRoutineCode.readCode) hread
  have hu2 : u ≤ u^2 := by nlinarith
  have hu3 : u^2 ≤ u^3 := by nlinarith [Nat.mul_le_mul_left (u*u) hu]
  have hu30 : 1 ≤ u^3 := by nlinarith
  change loadedClock p q K C L slack ≤ 1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1)*u^3
  unfold loadedClock CacheHashDispatch.loadedClock
  dsimp only
  rw [← Nat.add_max_add_left]
  apply max_le
  · nlinarith [Nat.zero_le (TM2TapeRuns.codeAccesses CacheRoutineCode.readCode*u^3)]
  · nlinarith [Nat.zero_le (TM2TapeRuns.codeAccesses CacheRoutineCode.readCode*u^3)]

/-- Polynomial width/length bounds give a polynomial for the existing request
clock at every security parameter. The hypotheses bound public data sizes;
they do not supply a machine-runtime or caller-correspondence certificate. -/
theorem loadedClock_polynomial (p q K C L slack : Nat → Nat)
    (P Q PK PC PL PS : Polynomial Nat)
    (hp : ∀ n, (p n).size ≤ P.eval n) (hq : ∀ n, (q n).size ≤ Q.eval n)
    (hk : ∀ n, K n ≤ PK.eval n) (hc : ∀ n, C n ≤ PC.eval n)
    (hl : ∀ n, L n ≤ PL.eval n) (hs : ∀ n, slack n ≤ PS.eval n) :
    ∃ R : Polynomial Nat, ∀ n, loadedClock (p n) (q n) (K n) (C n) (L n) (slack n) ≤ R.eval n := by
  refine ⟨Polynomial.C (1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1))*
    (P+Q+PK+PC+PL+PS+1)^3,?_⟩
  intro n
  apply (loadedClock_le_cubic (p n) (q n) (K n) (C n) (L n) (slack n)).trans
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_one]
  gcongr
  · exact hp n
  · exact hq n
  · exact hk n
  · exact hc n
  · exact hl n
  · exact hs n

/-- The clock bound includes zero arithmetic parameters; this is an arithmetic
edge case, not a claim that zero is a valid cryptographic modulus. -/
theorem cubic_zero_control : loadedClock 0 0 0 0 0 0 ≤
    1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1) := by
  simpa using loadedClock_le_cubic 0 0 0 0 0 0

/-- A nonzero public-parameter/loaded-length fixture instantiates the general cap. -/
theorem cubic_loaded_control : loadedClock 23 11 128 256 128 16 ≤
    1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1)*538^3 := by
  simpa [show Nat.size 23 = 5 from rfl,show Nat.size 11 = 4 from rfl] using
    loadedClock_le_cubic 23 11 128 256 128 16

/-- Omitting the loaded key length leaves an insufficient constant cap. This is
the retained native gate's independent key-length omission witness. -/
theorem key_length_omission_control :
    ¬ loadedClock 0 0 1048576 0 0 0 ≤
      1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1) := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Small payload lengths do not bound the ambient public group width. This
arithmetic omission control keeps every loaded payload length at zero. -/
theorem public_width_omission_control :
    ¬ loadedClock (2^4096) 0 0 0 0 0 ≤
      1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1) := by
  decide +kernel

#print axioms loadedClock_le_cubic
#print axioms loadedClock_polynomial
#print axioms cubic_zero_control
#print axioms cubic_loaded_control
#print axioms key_length_omission_control
#print axioms public_width_omission_control

end ExplainableCrypto.Helios.Computational.CacheRequestMachine
