import ExplainableCrypto.Helios.Computational.PrimeProofRequest
import ExplainableCrypto.Helios.Computational.BitOracleTapeCap

/-! Common resident-word bounds for the two remaining executions of the same
proof-request program. These derive size and charge bounds from resident
encodings and actual execution; they add no instructions or source assumptions. -/

set_option maxHeartbeats 600000

namespace ExplainableCrypto.Helios.Computational.PrimeProgramMachine

private theorem insert_clock_mono (p q : Nat) {N M : Nat} (h : N ≤ M) :
    PrimeProgrammedInsertMachine.clock p q N ≤ PrimeProgrammedInsertMachine.clock p q M := by
  have hi : PrimeProgrammedInsertMachine.insertBound p q N ≤
      PrimeProgrammedInsertMachine.insertBound p q M := CacheInsertMachine.cost_mono h h
  have hh : PrimeProgrammedInsertMachine.inputBound p q N ≤
      PrimeProgrammedInsertMachine.inputBound p q M := by
    unfold PrimeProgrammedInsertMachine.inputBound
    omega
  have hc := CacheProgrammedInsertMachine.clock_mono hi hh
  have hp : PrimeProgrammedInsertMachine.prepareClock N ≤
      PrimeProgrammedInsertMachine.prepareClock M := by
    unfold PrimeProgrammedInsertMachine.prepareClock
    omega
  exact Nat.add_le_add hp hc

theorem clock_mono (p q : Nat) {N M : Nat} (h : N ≤ M) : clock p q N ≤ clock p q M :=
  Nat.add_le_add (insert_clock_mono p q h) (PrimeProgrammedHistoryMachine.clock_mono p h)

theorem cost_mono (p q : Nat) {N M : Nat} (h : N ≤ M) : cost p q N ≤ cost p q M := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 32 (insert_clock_mono p q h))
    (Nat.mul_le_mul_left 32 (PrimeProgrammedHistoryMachine.clock_mono p h))

#print axioms clock_mono
#print axioms cost_mono
end ExplainableCrypto.Helios.Computational.PrimeProgramMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

private theorem vector8_le {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3)
    (h4 : a4 ≤ b4) (h5 : a5 ≤ b5) (h6 : a6 ≤ b6) (h7 : a7 ≤ b7) (i : Fin 8) :
    ![a0,a1,a2,a3,a4,a5,a6,a7] i ≤ ![b0,b1,b2,b3,b4,b5,b6,b7] i := by
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

private theorem pair_bound_mono {a b c d : Nat} (ha : a ≤ c) (hb : b ≤ d) :
    bitPairSize a b ≤ bitPairSize c d := by
  have hs := Nat.size_le_size ha
  have ht := Nat.size_le_size hb
  unfold bitPairSize
  omega

theorem clock_mono (p q : Nat) {N M : Nat} (h : N ≤ M) : clock p q N ≤ clock p q M := by
  have hn := Nat.add_le_add_right h 1
  have hs := Nat.size_le_size hn
  have hc : shadowBound p q N ≤ shadowBound p q M := by
    have hm := Nat.mul_le_mul_right (2*(cacheEntryBitBound p q).size+1+cacheEntryBitBound p q) hn
    unfold shadowBound cacheRecordBitBound
    omega
  have hh : historyBound p N ≤ historyBound p M := by
    have hm := Nat.mul_le_mul_right (2*(statementRecordBitBound p).size+1+statementRecordBitBound p) hn
    unfold historyBound bitListSize
    omega
  have hf : flagHistoryBound p N ≤ flagHistoryBound p M := pair_bound_mono (Nat.le_refl 1) hh
  have hp : programmedBound p q N ≤ programmedBound p q M := pair_bound_mono hc hf
  have hl (i : Fin 8) : pairLeftBounds p q N i ≤ pairLeftBounds p q M i :=
    vector8_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) hc hp i
  have hr (i : Fin 8) : pairRightBounds p q N i ≤ pairRightBounds p q M i :=
    vector8_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) hh hf h i
  have ht (i : Fin 8) : tempBounds p q N i ≤ tempBounds p q M i :=
    vector8_le (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) hf hp i
  have hpair : (∑ i : Fin 8, BitPairWriterMachine.clock (pairLeftBounds p q N i) (pairRightBounds p q N i)) ≤
      ∑ i : Fin 8, BitPairWriterMachine.clock (pairLeftBounds p q M i) (pairRightBounds p q M i) :=
    Finset.sum_le_sum (fun i _ => BitPairWriterMachine.clock_mono (hl i) (hr i))
  have htemp : (∑ i : Fin 8, tempBounds p q N i) ≤ ∑ i : Fin 8, tempBounds p q M i :=
    Finset.sum_le_sum (fun i _ => ht i)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hpair _) htemp) 11

theorem cost_mono (p q : Nat) {N M : Nat} (h : N ≤ M) : cost p q N ≤ cost p q M :=
  Nat.mul_le_mul_left 32 (clock_mono p q h)

#print axioms clock_mono
#print axioms cost_mono
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequest

theorem tailClock_mono (p q : Nat) {I I' O O' : Nat} (hi : I ≤ I') (ho : O ≤ O') :
    tailClock p q I O ≤ tailClock p q I' O' :=
  Nat.add_le_add_left (Nat.add_le_add (PrimeProgramMachine.clock_mono p q hi)
    (PrimeProgramOutputMachine.clock_mono p q ho)) _

theorem tailCost_mono (p q : Nat) {I I' O O' : Nat} (hi : I ≤ I') (ho : O ≤ O') :
    tailCost p q I O ≤ tailCost p q I' O' :=
  Nat.add_le_add_left (Nat.add_le_add (PrimeProgramMachine.cost_mono p q hi)
    (PrimeProgramOutputMachine.cost_mono p q ho)) _

#print axioms tailClock_mono
#print axioms tailCost_mono
end ExplainableCrypto.Helios.Computational.PrimeProofRequest

namespace ExplainableCrypto.Helios.Computational.PrimeProofRequest
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

/-- Only the three resident encodings are needed to bound both request size
parameters; no reachability or supplied execution certificate is assumed. -/
theorem resident_bounds (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (W : Fin 58 → List Bool) (N : Nat)
    (h44 : W 44 = (ballotCacheBitCodec p q).encode s.cache)
    (h45 : W 45 = (ballotCacheBitCodec p q).encode live)
    (h47 : W 47 = (ballotStatementBitCodec p q).list.encode s.programmed)
    (hN : ∀ k, (W k).length ≤ N) :
    PrimeProgramRequestRun.inputSize s live ≤ N ∧ outputBound s live ≤ N := by
  have hc : ((ballotCacheBitCodec p q).encode s.cache).length ≤ N := by
    rw [←h44]; exact hN 44
  have hl : ((ballotCacheBitCodec p q).encode live).length ≤ N := by
    rw [←h45]; exact hN 45
  have hh : ((ballotStatementBitCodec p q).list.encode s.programmed).length ≤ N := by
    rw [←h47]; exact hN 47
  have hn := (CacheHashHandler.entries_le s.cache).trans hc
  have hcount : s.programmed.length ≤
      ((ballotStatementBitCodec p q).list.encode s.programmed).length := by
    change s.programmed.length ≤
      (bitFieldsEncode (s.programmed.map (ballotStatementBitCodec p q).encode)).length
    simpa only [List.length_map] using
      CacheHashHandler.fields_count_le (s.programmed.map (ballotStatementBitCodec p q).encode)
  exact ⟨max_le hc (max_le hl hh), max_le hn (max_le (hcount.trans hh) hl)⟩

#print axioms resident_bounds
end ExplainableCrypto.Helios.Computational.PrimeProofRequest
namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests
open OracleComp OracleSpec BitOracleMachine TM2TapeRuns
set_option maxRecDepth 65536
attribute [local irreducible] BitOracleMachine.run

/-- Compose existing paid per-instruction growth for the common bound needed
by the second request's executed reset. -/
private theorem step_height {s l m : Nat} (code : Code s l m) (cfg : Config s l m)
    (out : Config s l m × Nat) (h : out ∈ support (BitOracleMachine.step code cfg)) :
    height out.1.stk ≤ height cfg.stk+out.2 := by
  cases hlabel : cfg.l with
  | none =>
    simp only [BitOracleMachine.step,hlabel] at h
    obtain rfl := eq_of_mem_support_pure _ h
    exact Nat.le_refl _
  | some label =>
    cases hcode : code label with
    | compute stmt =>
      simp only [BitOracleMachine.step,hlabel,hcode] at h
      obtain rfl := eq_of_mem_support_pure _ h
      exact BitOracleTapeCap.compute_growth stmt cfg
    | coin dest next =>
      simp only [BitOracleMachine.step,hlabel,hcode] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨bit,_,h⟩ := h
      obtain rfl := eq_of_mem_support_pure _ h
      exact BitOracleTapeCap.reply_growth cfg dest next [bit] (2+(cfg.stk dest).length)
        (by change 1 ≤ 2+(cfg.stk dest).length; omega)
    | hash req dest next =>
      simp only [BitOracleMachine.step,hlabel,hcode] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨answer,_,h⟩ := h
      obtain rfl := eq_of_mem_support_pure _ h
      exact BitOracleTapeCap.reply_growth cfg dest next answer _ (by omega)

theorem run_height {s l m : Nat} (code : Code s l m) (fuel : Nat) (cfg : Config s l m)
    (out : Config s l m × Nat) (h : out ∈ support (BitOracleMachine.run code fuel cfg)) :
    height out.1.stk ≤ height cfg.stk+out.2 := by
  induction fuel generalizing cfg out with
  | zero =>
    rw [BitOracleMachine.run] at h
    obtain rfl := eq_of_mem_support_pure _ h
    exact Nat.le_refl _
  | succ fuel ih =>
    rw [BitOracleMachine.run,mem_support_bind_iff] at h
    obtain ⟨first,hfirst,h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨last,hlast,h⟩ := h
    obtain rfl := eq_of_mem_support_pure _ h
    have ha := step_height code cfg first hfirst
    have hb := ih first.1 last hlast
    dsimp only
    omega

#print axioms run_height
end ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests
namespace ExplainableCrypto.Helios.Computational.PrimeProofRequest
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
attribute [local irreducible] BitOracleMachine.run

/-- One clock for a request whose resident size parameters are bounded by `N`. -/
def boundedClock (slack p q N : Nat) : Nat :=
  PrimeRequestDraws.clock slack p q + tailClock p q N N

/-- The corresponding sum of actual component charge bounds. -/
def boundedCost (slack p q N : Nat) : Nat :=
  PrimeRequestDraws.cost slack p q + tailCost p q N N

theorem clock_le_bounded (slack : Nat) (s : State (p:=p) (q:=q))
    (live : Cache (p:=p) (q:=q)) (N : Nat)
    (hi : PrimeProgramRequestRun.inputSize s live ≤ N) (ho : outputBound s live ≤ N) :
    clock slack s live ≤ boundedClock slack p q N :=
  Nat.add_le_add_left (tailClock_mono p q hi ho) _

theorem cost_le_bounded (slack : Nat) (s : State (p:=p) (q:=q))
    (live : Cache (p:=p) (q:=q)) (N : Nat)
    (hi : PrimeProgramRequestRun.inputSize s live ≤ N) (ho : outputBound s live ≤ N) :
    cost slack s live ≤ boundedCost slack p q N :=
  Nat.add_le_add_left (tailCost_mono p q hi ho) _

/-- The additional ticks occur only after every actual request branch halts. -/
theorem padded_run_bounded (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (N : Nat) (hi : PrimeProgramRequestRun.inputSize s live ≤ N) (ho : outputBound s live ≤ N) :
    BitOracleMachine.run code (boundedClock slack p q N) (start slack g pk vote r s live second extra) =
      BitOracleMachine.run code (clock slack s live) (start slack g pk vote r s live second extra) := by
  have hclock := clock_le_bounded slack s live N hi ho
  have hp := BitOracleReturnLink.padded code (clock slack s live)
    (boundedClock slack p q N - clock slack s live) (start slack g pk vote r s live second extra)
    (fun last h => (run_support slack g pk vote r s live second extra last h).1)
  simpa only [Nat.sub_add_cancel hclock] using hp

/-- Common-clock execution retains the complete fair-bit source query tree. -/
theorem execution_source_bounded (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (N : Nat) (hi : PrimeProgramRequestRun.inputSize s live ≤ N) (ho : outputBound s live ≤ N) :
    Prod.fst <$> BitOracleMachine.run code (boundedClock slack p q N)
      (start slack g pk vote r s live second extra) =
      simulateQ CoinWordLoader.liftCoins
        (fullResult slack g pk vote r s live second extra <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  rw [padded_run_bounded slack g pk vote r s live second extra N hi ho]
  exact execution_source slack g pk vote r s live second extra

/-- Every common-clock branch halts with its actual charge bounded by the same
resident-size parameter; no externally supplied cost certificate is used. -/
theorem run_support_bounded (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (N : Nat) (hi : PrimeProgramRequestRun.inputSize s live ≤ N) (ho : outputBound s live ≤ N) :
    ∀ last ∈ support (BitOracleMachine.run code (boundedClock slack p q N)
      (start slack g pk vote r s live second extra)),
      last.1.l = none ∧ last.2 ≤ boundedCost slack p q N := by
  rw [padded_run_bounded slack g pk vote r s live second extra N hi ho]
  intro last h
  obtain ⟨hh,hc⟩ := run_support slack g pk vote r s live second extra last h
  exact ⟨hh,hc.trans (cost_le_bounded slack s live N hi ho)⟩

#print axioms clock_le_bounded
#print axioms cost_le_bounded
#print axioms padded_run_bounded
#print axioms execution_source_bounded
#print axioms run_support_bounded
end ExplainableCrypto.Helios.Computational.PrimeProofRequest
