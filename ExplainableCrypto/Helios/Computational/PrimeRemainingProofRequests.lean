import ExplainableCrypto.Helios.Computational.PrimeProofRequest
import ExplainableCrypto.Helios.Computational.PrimeProofRequestReentry
import ExplainableCrypto.Helios.Computational.PrimeProgramOutputCallerSource
import ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSource
import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptSource

/-! Two distinct instances of the same request executor. These are exact resident
state presentations; the remaining submission continuation is not executed here. -/
namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
open PrimeProgramProofSource (State Cache Draws)
abbrev Scalars := ZMod q × ZMod q × ZMod q × ZMod q
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

def p1Layout : Fin 50 ⊕ Fin 8 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [55, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 54, 51, 19, 50, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 52, 49, 0, 17, 18, 20, 48, 53, 56, 57] (by decide +kernel) (by decide +kernel))

def totalLayout : Fin 50 ⊕ Fin 8 ≃ Fin 58 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [57, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 56, 51, 19, 50, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 53, 49, 0, 17, 18, 20, 48, 52, 54, 55] (by decide +kernel) (by decide +kernel))

def frame (layout : Fin 50 ⊕ Fin 8 ≃ Fin 58) (words : Fin 58 → List Bool) : Fin 8 → List Bool :=
  fun i => words (layout (.inr i))
def raw (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :=
  PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
def firstState (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q)) (out : Draws (q:=q)) :=
  PrimeProgramRepackSource.nextState g pk vote s out
/-- Actual completed p0 source result followed by eight blank caller ports. -/
def initialWords (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) : Fin 58 → List Bool :=
  fun k => if h : k.val < 50 then
    (PrimeProgramOutputCaller.sourceResult slack g pk vote s live out).stk ⟨k.val,h⟩ else []
def p1Prepared (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :=
  PrimeProofRequestReentry.resultWords (initialWords slack g pk vote s live out)
    (scalarEncode out.1.2) [false]
def p1Start (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :=
  PrimeProofRequest.start slack g pk false out.1.2 (firstState g pk vote s out) live
    (scalarEncode out.1.2) (raw slack g pk vote s live)
def p1Result (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs1 : Scalars (q:=q)) :=
  BitOracleStackFrame.embed p1Layout
    (PrimeProofRequest.fullResult slack g pk false out.1.2 (firstState g pk vote s out) live
      (scalarEncode out.1.2) (raw slack g pk vote s live) cs1)
    (frame p1Layout (p1Prepared slack g pk vote s live out))
def secondState (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q))
    (out : Draws (q:=q)) (cs1 : Scalars (q:=q)) :=
  PrimeProofRequest.next (honestProofStatement g pk (false,out.1.2)) cs1 (firstState g pk vote s out)
def totalPrepared (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs1 : Scalars (q:=q)) :=
  PrimeProofRequestReentry.resultWords (p1Result slack g pk vote s live out cs1).stk
    (scalarEncode (out.1.1+out.1.2)) [vote]
def totalStart (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs1 : Scalars (q:=q)) :=
  PrimeProofRequest.start slack g pk vote (out.1.1+out.1.2) (secondState g pk vote s out cs1) live
    (scalarEncode out.1.2) (raw slack g pk vote s live)
def totalResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 csT : Scalars (q:=q)) :=
  BitOracleStackFrame.embed totalLayout
    (PrimeProofRequest.fullResult slack g pk vote (out.1.1+out.1.2) (secondState g pk vote s out cs1) live
      (scalarEncode out.1.2) (raw slack g pk vote s live) csT)
    (frame totalLayout (totalPrepared slack g pk vote s live out cs1))

private theorem first_fields (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let w := initialWords slack g pk vote s live out
    let st := firstState g pk vote s out
    w 44 = (ballotCacheBitCodec p q).encode st.cache ∧ w 46 = [st.bad] ∧
    w 45 = (ballotCacheBitCodec p q).encode live ∧
    w 47 = (ballotStatementBitCodec p q).list.encode st.programmed :=
  PrimeProgramCaller.source_state slack g pk vote s live out

private theorem first_inputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let w := initialWords slack g pk vote s live out
    w 6 = p.bits ∧ w 16 = (primeGroupCoordinate g).val.bits ∧
    w 15 = (primeGroupCoordinate pk).val.bits ∧ w 19 = SamplerOperands.input slack q [] ∧
    w 21 = scalarEncode out.1.2 ∧ w 22 = (q-1).bits ∧ w 14 = raw slack g pk vote s live := by
  obtain ⟨hp,hg,hpk,hr,hn,_,hm,_,_,hraw⟩ := PrimeSecondTranscriptSource.source_inputs slack g pk vote s live out
  exact ⟨hp,hg,hpk,hr,hn,hm,hraw⟩

private theorem first_blank (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (i : Fin 12) :
    let k : Fin 58 := (![4,5,8,9,30,31,32,33,34,35,36,41] : Fin 12 → Fin 58) i
    initialWords slack g pk vote s live out k = [] := by
  fin_cases i <;> rfl

/-- Full current state is the canonical generic executor entry after actual reset. -/
theorem p1_start (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    BitOracleStackFrame.embed p1Layout (p1Start slack g pk vote s live out)
      (frame p1Layout (p1Prepared slack g pk vote s live out)) =
    (⟨(p1Start slack g pk vote s live out).l,2,p1Prepared slack g pk vote s live out⟩ :
      BitOracleMachine.Config 58 PrimeProofRequest.size 3) := by
  obtain ⟨hc,hb,hl,hh⟩ := first_fields slack g pk vote s live out
  obtain ⟨hp,hg,hpk,hr,hn,hm,hraw⟩ := first_inputs slack g pk vote s live out
  have hz := first_blank slack g pk vote s live out
  have hw (k : Fin 58) :
      (BitOracleStackFrame.embed p1Layout (p1Start slack g pk vote s live out)
        (frame p1Layout (p1Prepared slack g pk vote s live out))).stk k =
      p1Prepared slack g pk vote s live out k := by
    obtain ⟨x,rfl⟩ := p1Layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hz 0).symm
      · exact (hz 1).symm
      · exact hp.symm
      · rfl
      · exact (hz 2).symm
      · exact (hz 3).symm
      · rfl
      · rfl
      · rfl
      · rfl
      · exact hraw.symm
      · exact hpk.symm
      · exact hg.symm
      · rfl
      · rfl
      · exact hr.symm
      · rfl
      · exact hn.symm
      · exact hm.symm
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hz 4).symm
      · exact (hz 5).symm
      · exact (hz 6).symm
      · exact (hz 7).symm
      · exact (hz 8).symm
      · exact (hz 9).symm
      · exact (hz 10).symm
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hz 11).symm
      · rfl
      · rfl
      · exact hc.symm
      · exact hl.symm
      · exact hb.symm
      · exact hh.symm
      · rfl
      · rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      rfl
  exact congrArg (fun w => (⟨(p1Start slack g pk vote s live out).l,2,w⟩ :
    BitOracleMachine.Config 58 PrimeProofRequest.size 3)) (funext hw)

/-- Full current state is the canonical generic executor entry after actual reset. -/
theorem total_start (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (cs1 : Scalars (q:=q)) :
    BitOracleStackFrame.embed totalLayout (totalStart slack g pk vote s live out cs1)
      (frame totalLayout (totalPrepared slack g pk vote s live out cs1)) =
    (⟨(totalStart slack g pk vote s live out cs1).l,2,totalPrepared slack g pk vote s live out cs1⟩ :
      BitOracleMachine.Config 58 PrimeProofRequest.size 3) := by
  have hw (k : Fin 58) :
      (BitOracleStackFrame.embed totalLayout (totalStart slack g pk vote s live out cs1)
        (frame totalLayout (totalPrepared slack g pk vote s live out cs1))).stk k =
      totalPrepared slack g pk vote s live out cs1 k := by
    obtain ⟨x,rfl⟩ := totalLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      rfl
  exact congrArg (fun w => (⟨(totalStart slack g pk vote s live out cs1).l,2,w⟩ :
    BitOracleMachine.Config 58 PrimeProofRequest.size 3)) (funext hw)

#print axioms p1_start
#print axioms total_start

/-- The actual p0 endpoint supplies every retained scalar and blank-work condition
required by the common reentry program. -/
theorem initial_reentry_inputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let w := initialWords slack g pk vote s live out
    w 2 = q.bits ∧ w 20 = scalarEncode out.1.1 ∧ w 21 = scalarEncode out.1.2 ∧
    w 18 = [vote] ∧ (∀ j : Fin 7, w ⟨23+j.val,by omega⟩ = []) ∧ w 37 = [] := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl⟩
  intro j
  fin_cases j <;> rfl

/-- Reentry for total uses the actual first-request successor, while original
nonces and vote stay in their retained caller ports. -/
theorem p1_reentry_inputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 : Scalars (q:=q)) :
    let w := (p1Result slack g pk vote s live out cs1).stk
    w 2 = q.bits ∧ w 20 = scalarEncode out.1.1 ∧ w 21 = scalarEncode out.1.2 ∧
    w 18 = [vote] ∧ (∀ j : Fin 7, w ⟨23+j.val,by omega⟩ = []) ∧ w 37 = [] := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl⟩
  intro j
  fin_cases j <;> rfl

theorem sum_prefix (out : Draws (q:=q)) :
    scalarEncode (out.1.1+out.1.2) = uniformNatEncode ((out.1.1.val+out.1.2.val)%q) := by
  simp only [scalarEncode,ZMod.val_add]

/-- Both encodings are returned by the same generic request theorem, with the
current state resulting from the prior operation. -/
theorem p1_outputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 : Scalars (q:=q)) :
    let stmt := honestProofStatement g pk (false,out.1.2)
    let op := (firstState g pk vote s out).program stmt (PrimeProofRequest.transcript stmt cs1)
    let w := (p1Result slack g pk vote s live out cs1).stk
    w 52 = (ballotProofBitCodec p q).encode op.1 ∧
    w 49 = (ballotBothCachesBitCodec p q).encode (op.2,live) := by
  exact PrimeProofRequest.fullResult_return slack g pk false out.1.2
    (firstState g pk vote s out) live (scalarEncode out.1.2) (raw slack g pk vote s live) cs1

theorem total_outputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 csT : Scalars (q:=q)) :
    let stmt := honestProofStatement g pk (vote,out.1.1+out.1.2)
    let op := (secondState g pk vote s out cs1).program stmt (PrimeProofRequest.transcript stmt csT)
    let w := (totalResult slack g pk vote s live out cs1 csT).stk
    w 53 = (ballotProofBitCodec p q).encode op.1 ∧
    w 49 = (ballotBothCachesBitCodec p q).encode (op.2,live) := by
  exact PrimeProofRequest.fullResult_return slack g pk vote (out.1.1+out.1.2)
    (secondState g pk vote s out cs1) live (scalarEncode out.1.2) (raw slack g pk vote s live) csT

/-- Every original ciphertext, nonce, vote, raw word and p0 proof is retained
across both later requests. Updated state is deliberately not read from raw14. -/
theorem original_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 csT : Scalars (q:=q)) (i : Fin 7) :
    let k : Fin 58 := (![0,17,18,20,21,48,14] : Fin 7 → Fin 58) i
    (totalResult slack g pk vote s live out cs1 csT).stk k =
      initialWords slack g pk vote s live out k := by
  fin_cases i <;> rfl

/-- The second component ciphertext and returned proof survive the total call. -/
theorem p1_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 csT : Scalars (q:=q)) (i : Fin 3) :
    let k : Fin 58 := (![54,55,52] : Fin 3 → Fin 58) i
    (totalResult slack g pk vote s live out cs1 csT).stk k =
      (p1Result slack g pk vote s live out cs1).stk k := by
  fin_cases i
  · change (totalResult slack g pk vote s live out cs1 csT).stk (totalLayout (.inr 6)) = _
    simp only [totalResult,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
      Equiv.symm_apply_apply,Sum.elim_inr,frame]
    change PrimeProofRequestReentry.resultWords (p1Result slack g pk vote s live out cs1).stk
      (scalarEncode (out.1.1+out.1.2)) [vote] 54 = _
    rfl
  · change (totalResult slack g pk vote s live out cs1 csT).stk (totalLayout (.inr 7)) = _
    simp only [totalResult,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
      Equiv.symm_apply_apply,Sum.elim_inr,frame]
    change PrimeProofRequestReentry.resultWords (p1Result slack g pk vote s live out cs1).stk
      (scalarEncode (out.1.1+out.1.2)) [vote] 55 = _
    rfl
  · change (totalResult slack g pk vote s live out cs1 csT).stk (totalLayout (.inr 5)) = _
    simp only [totalResult,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
      Equiv.symm_apply_apply,Sum.elim_inr,frame]
    change PrimeProofRequestReentry.resultWords (p1Result slack g pk vote s live out cs1).stk
      (scalarEncode (out.1.1+out.1.2)) [vote] 52 = _
    rfl

omit [Fact p.Prime] in
/-- Recomputed total encryption is the historical homomorphic aggregate,
including a zero sum of the original nonces. -/
theorem total_statement (g pk : PrimeGroup p q) (vote : Bool) (rs : ZMod q × ZMod q)
    (p0 p1 pt : Proof01 (ZMod q) (PrimeGroup p q)) :
    (honestProofStatement g pk (vote,rs.1+rs.2)).ciphertext =
      (assembleHonestBallot g pk vote rs p0 p1 pt).aggregate := by
  simp [honestProofStatement,assembleHonestBallot,Ballot.aggregate,Fin.sum_univ_two,encryptWith_add]

#print axioms initial_reentry_inputs
#print axioms p1_reentry_inputs
#print axioms sum_prefix
#print axioms p1_outputs
#print axioms total_outputs
#print axioms original_retained
#print axioms p1_retained
#print axioms total_statement

end ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests
