import ExplainableCrypto.Helios.Computational.CacheHashDispatchRun
import ExplainableCrypto.Helios.Computational.CacheHashHandler

/-! Loaded-word bounds for the actual complete dispatcher. The interface takes
cache/log word lengths, public group/modulus parameters and sampling slack. The
parameters occur only through their binary widths; a short key does not bound
the ambient group width. The fixed probe access factor remains explicit.

The callers are the enclosing request loader and supported source-budget
specializations. Canonical codecs and positive p/q derive the count and field
bounds; no runtime, freshness or intermediate-state certificate is supplied. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashDispatch
open CacheRoutineCode
set_option maxRecDepth 8192

/-- Common request clock computed from loaded cache/log lengths and public
parameter widths. The scalar sampler clock includes executed preparation. -/
def loadedClock (p q C L slack : Nat) : Nat :=
  let K := keyRecordBitBound p
  let R := slack+2*q.size+2
  let P := CacheReadMachine.cost p q C C
  let J := bitListSize K (L+1)
  let E := 1+LogAppendMachine.cost L K L+1+(3*J+3)
  let D := 3*(2*(q-1).size+1)+q.size+5+3*C+3+
    CacheInsertMachine.cost p q C C+E
  let H := K+C+L+R
  let A := TM2TapeRuns.codeAccesses readCode
  max (1+P+(2+(CacheHashMachine.sampleClock slack q+D)))
    (1+(P+(1+(2*(H+P*A+1)+(3*(q-1).size+3)))))

private theorem log_count_le {p q : Nat} [NeZero p] [NeZero q]
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) :
    log.length ≤ (((ballotLogEntryBitCodec p q).list).encode log).length := by
  change log.length ≤ (bitFieldsEncode (log.map (ballotLogEntryBitCodec p q).encode)).length
  simpa only [List.length_map] using
    CacheHashHandler.fields_count_le (log.map (ballotLogEntryBitCodec p q).encode)

private theorem appended_length_le {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) :
    (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])).length ≤
      bitListSize (keyRecordBitBound p) ((((ballotLogEntryBitCodec p q).list).encode log).length+1) := by
  apply BitRecordCodec.list_length_le
  · intro e _
    exact ballotKeyBits_length_le e.2
  · have hn := log_count_le log
    simp only [List.length_append,List.length_singleton]
    omega

private theorem record_length (slack q : Nat) :
    (SamplerOperands.input slack q []).length = slack+2*q.size+2 := by
  simp [SamplerOperands.input,uniformNatEncode_length,Nat.add_assoc]

private theorem probe_height_le {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (log record : List Bool) :
    TM2TapeRuns.height (probeStart ((ballotKeyBitCodec p q).encode key)
      ((ballotCacheBitCodec p q).encode cache) log record).stk ≤
      keyRecordBitBound p+((ballotCacheBitCodec p q).encode cache).length+log.length+record.length := by
  apply Finset.sup_le
  intro k _
  have hk := ballotKeyBits_length_le key
  fin_cases k <;> dsimp [probeStart] <;> omega

/-- The already executed sampler's charge is bounded by its actual analysis
clock. This is arithmetic on its proved costs, not an assumed certificate. -/
private theorem sample_cost_le (slack q : Nat) :
    CacheHashMachine.sampleCost slack q ≤ 32*CacheHashMachine.sampleClock slack q := by
  unfold CacheHashMachine.sampleCost CacheHashMachine.sampleClock
    PreparedScalarMachine.cost PreparedScalarMachine.clock PreparedScalarMachine.width
    SamplerOperands.clock SamplerOperands.range CoinScalarMachine.cost CoinScalarMachine.clock
    CoinModuloMachine.cost CoinModuloMachine.clock
  simp only [Bool.false_eq_true,ite_false,Nat.mul_add,Nat.add_mul]
  omega

/-- The declared complete-request charge is at most 32 times its declared clock,
including both hit cleanup and the prepared sampling/mutation miss branch. -/
theorem request_cost_le_clock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    requestCost cache key log slack ≤ 32*requestClock cache key log slack := by
  have hs := sample_cost_le slack q
  have hm : missCost cache key log slack ≤ 32*missClock cache key log slack := by
    unfold missCost missClock
    omega
  have hh : hitCost cache key (((ballotLogEntryBitCodec p q).list).encode log)
      (SamplerOperands.input slack q []) ≤
      32*hitClock cache key (((ballotLogEntryBitCodec p q).list).encode log)
        (SamplerOperands.input slack q []) := by
    unfold hitCost hitClock
    omega
  exact max_le (hm.trans (Nat.mul_le_mul_left 32 (Nat.le_max_left _ _)))
    (hh.trans (Nat.mul_le_mul_left 32 (Nat.le_max_right _ _)))

/-- Every typed request derives this bound from its loaded word lengths. The
ambient public group width remains explicit even when the key contains small
values. The retained sampler record is included in the initial probe height. -/
theorem request_clock_le_loaded {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    requestClock cache key log slack ≤ loadedClock p q
      ((ballotCacheBitCodec p q).encode cache).length
      (((ballotLogEntryBitCodec p q).list).encode log).length slack := by
  let C := ((ballotCacheBitCodec p q).encode cache).length
  let L := (((ballotLogEntryBitCodec p q).list).encode log).length
  have hn := CacheHashHandler.entries_le cache
  have hl := log_count_le log
  have hp : probeClock cache ≤ CacheReadMachine.cost p q C C :=
    CacheReadMachine.cost_mono hn le_rfl
  have hi := CacheInsertMachine.cost_mono (p := p) (q := q) hn (le_refl C)
  have ha := LogAppendMachine.cost_mono hl (le_refl (keyRecordBitBound p)) (le_refl L)
  have hj := appended_length_le key log
  have hheight := probe_height_le cache key
    (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])
  rw [record_length] at hheight
  have hspace := Nat.add_le_add hheight
    (Nat.mul_le_mul_right (TM2TapeRuns.codeAccesses readCode) hp)
  change probeSpace cache key (((ballotLogEntryBitCodec p q).list).encode log)
    (SamplerOperands.input slack q []) ≤ _ at hspace
  have htail : appendClock key log ≤ 1+LogAppendMachine.cost L (keyRecordBitBound p) L+1+
      (3*bitListSize (keyRecordBitBound p) (L+1)+3) := by
    unfold appendClock
    dsimp only [L] at *
    omega
  have hm : missClock cache key log slack ≤
      1+CacheReadMachine.cost p q C C+(2+(CacheHashMachine.sampleClock slack q+
        (3*(2*(q-1).size+1)+q.size+5+3*C+3+CacheInsertMachine.cost p q C C+
          (1+LogAppendMachine.cost L (keyRecordBitBound p) L+1+
            (3*bitListSize (keyRecordBitBound p) (L+1)+3))))) := by
    unfold missClock missTailClock
    dsimp only [C] at *
    omega
  have hh : hitClock cache key (((ballotLogEntryBitCodec p q).list).encode log)
      (SamplerOperands.input slack q []) ≤
      1+(CacheReadMachine.cost p q C C+(1+
        (2*(keyRecordBitBound p+C+L+(slack+2*q.size+2)+
          CacheReadMachine.cost p q C C*TM2TapeRuns.codeAccesses readCode+1)+
            (3*(q-1).size+3)))) := by
    unfold hitClock hitTailClock
    dsimp only [C,L] at *
    omega
  exact max_le_max hm hh

/-- Derived combined charge bound for the same complete request, with no
additional runtime premise. -/
theorem request_cost_le_loaded {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    requestCost cache key log slack ≤ 32*loadedClock p q
      ((ballotCacheBitCodec p q).encode cache).length
      (((ballotLogEntryBitCodec p q).list).encode log).length slack :=
  (request_cost_le_clock cache key log slack).trans
    (Nat.mul_le_mul_left 32 (request_clock_le_loaded cache key log slack))

open BallotCacheCodecControls in
/-- Instantiate both derived bounds on the existing nonempty literal cache and
nonempty chronological log, with positive sampler slack. -/
theorem loaded_request_control :
    requestClock cache key [((),otherKey)] 2 ≤ loadedClock 23 11
      ((ballotCacheBitCodec 23 11).encode cache).length
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey)]).length 2 ∧
    requestCost cache key [((),otherKey)] 2 ≤ 32*loadedClock 23 11
      ((ballotCacheBitCodec 23 11).encode cache).length
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey)]).length 2 :=
  ⟨request_clock_le_loaded cache key _ 2,request_cost_le_loaded cache key _ 2⟩

/-- The private retained word occupies eight columns even when the public
key/cache/log words are empty. This pins the physical height convention. -/
theorem private_record_height_control :
    TM2TapeRuns.height (probeStart [] [] [] (List.replicate 8 true)).stk = 8 := by
  decide +kernel

/-- Ignoring the private record cannot justify even a seven-column cap. -/
theorem private_record_omission_control :
    ¬ TM2TapeRuns.height (probeStart [] [] [] (List.replicate 8 true)).stk ≤ 7 := by
  rw [private_record_height_control]
  omega

/-- Incrementing the list count from one to two enlarges the outer header.
Appending an empty field therefore adds three bits, not merely its one-bit frame. -/
theorem append_header_control :
    (bitFieldsEncode [[],[]]).length = (bitFieldsEncode [[]]).length+3 ∧
      (bitFieldsEncode [[],[]]).length ≠ (bitFieldsEncode [[]]).length+1 := by
  decide +kernel

#print axioms request_cost_le_clock
#print axioms request_clock_le_loaded
#print axioms request_cost_le_loaded
#print axioms loaded_request_control
#print axioms private_record_height_control
#print axioms private_record_omission_control
#print axioms append_header_control

end ExplainableCrypto.Helios.Computational.CacheHashDispatch
