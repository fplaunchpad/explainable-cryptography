import ExplainableCrypto.Helios.Computational.CacheRequestMachine
import ExplainableCrypto.Helios.Computational.BitOracleInitialInput

/-! Compose parsing and the complete request through an executed success gate.
All branches retain the original raw oracle tree and complete result state. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 8192

def input {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : List Bool :=
  CacheRequestInput.input ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
    (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])

def loadClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  CacheRequestInput.clock ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
    (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])

def clock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  loadClock cache key log slack+1+CacheHashDispatch.requestClock cache key log slack

def cost {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  32*loadClock cache key log slack+3+CacheHashDispatch.requestCost cache key log slack

private theorem gate_run (key cache log record : List Bool) (fuel : Nat) :
    run code (1+fuel)
      (BitOracleReturnLink.embed inputLabel (some gateLabel) (CacheRequestInput.ready key cache log record)) =
    (fun out => (BitOracleReturnLink.embed requestLabel none out.1,3+out.2)) <$>
      run CacheHashDispatch.code fuel (CacheHashDispatch.start key cache log record) := by
  rw [Nat.add_comm 1,run,enter_request,pure_bind]
  rw [BitOracleReturnLink.rename_run CacheHashDispatch.code code requestLabel request_code]
  simp [map_eq_bind_pure_comp,bind_assoc]

attribute [local irreducible] code CacheHashDispatch.code CacheHashDispatch.requestClock
  CacheHashDispatch.requestCost

/-- Parsing, guarded entry and the entire request execute in one program from a
single serialized input. All reachable leaves halt with the derived charge;
the equality retains the whole query tree and every result port. -/
theorem request_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    let execution := run code (clock cache key log slack) (start (input cache key log slack))
    (Prod.fst <$> execution = BitOracleReturnLink.embed requestLabel none <$>
      CacheHashDispatch.request cache key log slack) ∧
    ∀ out ∈ support execution, out.1.l = none ∧ out.2 ≤ cost cache key log slack := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let R := SamplerOperands.input slack q []
  let F := CacheHashDispatch.requestClock cache key log slack
  let D := run CacheHashDispatch.code F (CacheHashDispatch.start K C L R)
  obtain ⟨f,hf,x,hx,hi⟩ := CacheRequestInput.load_request K C L R
  have hd := CacheHashDispatch.request_run cache key log slack
  have gate := gate_run K C L R F
  have haltD : ∀ out ∈ support D, out.1.l = none := fun out ho => (hd.2 out ho).1
  have hh : ∀ out ∈ support (run CacheRequestInput.code f
      (CacheRequestInput.start (CacheRequestInput.input K C L R))), out.1.l = none := by
    rw [hi]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; rfl
  have ht : ∀ out ∈ support (run CacheRequestInput.code f
      (CacheRequestInput.start (CacheRequestInput.input K C L R))),
      ∀ last ∈ support (run code (1+F) (BitOracleReturnLink.embed inputLabel (some gateLabel) out.1)),
        last.1.l = none := by
    rw [hi]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out
    rw [gate]; intro last hl
    obtain ⟨d,hd,rfl⟩ := mem_support_map_peel _ _ hl
    simp [BitOracleReturnLink.embed,haltD d hd]
  have linked := BitOracleReturnLink.run CacheRequestInput.code code inputLabel gateLabel input_code
    f (1+F) (CacheRequestInput.start (CacheRequestInput.input K C L R)) hh ht
  rw [hi,pure_bind,gate] at linked
  simp only [map_eq_bind_pure_comp,bind_assoc,Function.comp_apply,pure_bind] at linked
  have he : run code (f+(1+F)) (start (input cache key log slack)) =
      (fun out => (BitOracleReturnLink.embed requestLabel none out.1,x+(3+out.2))) <$> D := by
    simpa only [map_eq_bind_pure_comp,Function.comp_def,start,input,D,K,C,L,R] using linked
  have halt : ∀ out ∈ support (run code (f+(1+F)) (start (input cache key log slack))), out.1.l = none := by
    rw [he]; intro out ho
    obtain ⟨d,hd,rfl⟩ := mem_support_map_peel _ _ ho
    simp [BitOracleReturnLink.embed,haltD d hd]
  have hclock : f+(1+F) ≤ clock cache key log slack := by
    change f ≤ loadClock cache key log slack at hf
    unfold clock
    dsimp only [F]
    omega
  have padded := BitOracleReturnLink.padded code (f+(1+F))
    (clock cache key log slack-(f+(1+F))) _ halt
  rw [Nat.sub_add_cancel hclock,he] at padded
  dsimp only
  rw [padded]
  constructor
  · have hp := congrArg (fun oa => BitOracleReturnLink.embed requestLabel none <$> oa) hd.1
    simpa only [Functor.map_map] using hp
  · intro out ho
    obtain ⟨d,hmem,rfl⟩ := mem_support_map_peel _ _ ho
    refine ⟨by simp [BitOracleReturnLink.embed,haltD d hmem],?_⟩
    have hb := (hd.2 d hmem).2
    change f ≤ loadClock cache key log slack at hf
    unfold cost
    omega

/-- External clock uses only loaded payload lengths, public parameters and slack. -/
def loadedClock (p q K C L slack : Nat) : Nat :=
  CacheRequestInput.lengthClock K C L (slack+2*q.size+2)+1+
    CacheHashDispatch.loadedClock p q C L slack

theorem clock_le_loaded {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    clock cache key log slack ≤ loadedClock p q ((ballotKeyBitCodec p q).encode key).length
      ((ballotCacheBitCodec p q).encode cache).length
      (((ballotLogEntryBitCodec p q).list).encode log).length slack := by
  have he := CacheHashDispatch.request_clock_le_loaded cache key log slack
  have hr : (SamplerOperands.input slack q []).length = slack+2*q.size+2 := by
    simp [SamplerOperands.input,uniformNatEncode_length,Nat.add_assoc]
  unfold clock loadClock loadedClock
  rw [CacheRequestInput.clock_lengths,hr]
  exact Nat.add_le_add_left he _

theorem cost_le_clock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    cost cache key log slack ≤ 32*clock cache key log slack := by
  have he := CacheHashDispatch.request_cost_le_clock cache key log slack
  unfold cost clock
  omega

theorem cost_le_loaded {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    cost cache key log slack ≤ 32*loadedClock p q ((ballotKeyBitCodec p q).encode key).length
      ((ballotCacheBitCodec p q).encode cache).length
      (((ballotLogEntryBitCodec p q).list).encode log).length slack :=
  (cost_le_clock cache key log slack).trans (Nat.mul_le_mul_left 32 (clock_le_loaded cache key log slack))

attribute [local irreducible] clock cost

private theorem within_support (limit bound : Nat)
    (oa : OracleComp spec (Config 12 size 3 × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

/-- Derive the physical compiler's contract from the executed serialized request. -/
theorem within {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat) :
    BitOracleLoopBounded.Within limit (cost cache key log slack)
      (run code (clock cache key log slack) (start (input cache key log slack))) :=
  within_support limit _ _ (request_run cache key log slack).2

private theorem start_source (raw : List Bool) :
    BitOracleInitialInput.source 6 (some (inputLabel 0)) 0 raw = start raw := by
  change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- From blank physical work storage and one conventional input tape, the
existing primitive compiler executes loading, parsing, guarded entry and the
whole request. Its startup and execution bounds are derived from the actual run. -/
theorem physical_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat) :
    let raw := input cache key log slack
    let B := cost cache key log slack
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height (start raw).stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 6 (some (inputLabel 0)) 0 (startup+T)
          (BitOracleInitialInput.initial raw)) =
      (some ∘ BitOracleReturnLink.embed requestLabel none) <$>
        simulateQ (BitOracleLoopBounded.adapter limit) (CacheHashDispatch.request cache key log slack) := by
  dsimp only
  have hw := within cache key log slack limit
  rw [← start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 6 (some (inputLabel 0)) 0
    (input cache key log slack) (clock cache key log slack) limit (cost cache key log slack) hw
  rw [start_source] at he
  simp only [Nat.add_zero] at he
  refine ⟨startup,hs,?_⟩
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (request_run cache key log slack).1
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms request_run
#print axioms clock_le_loaded
#print axioms cost_le_loaded
#print axioms within
#print axioms physical_run

end ExplainableCrypto.Helios.Computational.CacheRequestMachine
