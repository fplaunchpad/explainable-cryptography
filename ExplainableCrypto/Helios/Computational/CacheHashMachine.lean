import ExplainableCrypto.Helios.Computational.PreparedScalarMachine
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame
import ExplainableCrypto.Helios.Computational.BitCopyMachine

/-! Fixed cache-request workspace. The sampler branch executes the operand-record
copy from caller storage, then preparation/sampling while retaining key/cache/log.
The complete probe/hit/insert/append dispatcher is still to be assembled. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

/-- Work 0–7; retained key 8, cache 9, chronological log 10, operand record 11. -/
def sampleLayout : Fin 8 ⊕ Fin 4 ≃ Fin 12 := finSumFinEquiv

def frame (key cache log record : List Bool) : Fin 4 → List Bool := ![key,cache,log,record]

def samplerCode : Code 12 44 3 := BitOracleStackFrame.code sampleLayout PreparedScalarMachine.code

def samplerStart (record key cache log : List Bool) : Config 12 44 3 :=
  BitOracleStackFrame.embed sampleLayout (PreparedScalarMachine.startWord false record) (frame key cache log record)

def samplerResult (word modulus key cache log record : List Bool) : Config 12 44 3 :=
  BitOracleStackFrame.embed sampleLayout (PreparedScalarMachine.result word modulus) (frame key cache log record)

private def copyPorts : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun k := if k = 0 then .source else if k = 1 then .destination else .scratch
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def copyLabels : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := k == 1
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def copyLayout : BitCopyMachine.Stack ⊕ Fin 9 ≃ Fin 12 :=
  ((Equiv.sumCongr copyPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((Equiv.swap 0 11).trans ((Equiv.swap 1 4).trans (Equiv.swap 2 0)))

private def copyFrame (key cache log : List Bool) : Fin 9 → List Bool :=
  ![[],[],[],[],[],key,cache,log,[]]

private def copyProgram := TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) copyLabels
  BinaryModuloCode.memory (fun label => TM2StackFrame.relocate copyLayout (BitCopyMachine.program label))

private def copyState (phase : Option Bool) (record input key cache log : List Bool) : Config 12 2 3 :=
  TM2FiniteCoordinates.present (Equiv.refl _) copyLabels BinaryModuloCode.memory
    (TM2StackFrame.embed copyLayout (BitCopyMachine.config phase record input []) (copyFrame key cache log))

private theorem copy_cost (label : Fin 2) : localCost (copyProgram label) ≤ 5 := by
  fin_cases label <;> decide

private theorem copy_run (record key cache log : List Bool) :
    ∃ charge ≤ 5*(2*record.length+2),
      run (fun label => .compute (copyProgram label)) (2*record.length+2)
        (copyState (some false) record [] key cache log) =
      pure (copyState none record record key cache log,charge) := by
  obtain ⟨charge,hc,hr⟩ := compute_run_cost copyProgram 5 copy_cost (2*record.length+2)
    (copyState (some false) record [] key cache log)
  refine ⟨charge,hc,?_⟩
  rw [hr]
  congr 2
  rw [copyState,copyProgram,TM2FiniteCoordinates.run,TM2StackFrame.run]
  have h := BitCopyMachine.run record [] none
  simp only [List.append_nil] at h
  change BitCopyMachine.tick^[2*record.length+2] _ = _ at h
  rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*record.length+2]
    (BitCopyMachine.config (some false) record [] []) = BitCopyMachine.config none record record [] from h]
  rfl

private def copyLabel (l : Fin 2) : Fin 47 := ⟨l.val,by omega⟩
private def sampleLabel (l : Fin 44) : Fin 47 := ⟨l.val+3,by omega⟩

/-- The operand copy and sampler form one fixed program with actual return labels. -/
def sampleCode (label : Fin 47) : Command 12 47 3 :=
  if h : label.val < 2 then
    BitOracleReturnLink.command copyLabel (some 2) (.compute (copyProgram ⟨label.val,h⟩))
  else if label = 2 then .compute (.load (fun _ => 0) (.goto (fun _ => 3)))
  else BitOracleReturnLink.command sampleLabel none (samplerCode ⟨label.val-3,by omega⟩)

/-- Initially the sampler record is only on retained port 11; its input port is empty. -/
def sampleStart (record key cache log : List Bool) : Config 12 47 3 :=
  BitOracleReturnLink.embed copyLabel (some 2) (copyState (some false) record [] key cache log)

def sampleResult (word modulus key cache log record : List Bool) : Config 12 47 3 :=
  BitOracleReturnLink.embed sampleLabel none (samplerResult word modulus key cache log record)

def sampleClock (slack q : Nat) : Nat :=
  (2*(SamplerOperands.input slack q []).length+2)+(1+PreparedScalarMachine.clock false slack q)

def sampleCost (slack q : Nat) : Nat :=
  5*(2*(SamplerOperands.input slack q []).length+2)+2+PreparedScalarMachine.cost false slack q

private theorem copy_code (label : Fin 2) : sampleCode (copyLabel label) =
    BitOracleReturnLink.command copyLabel (some 2) (.compute (copyProgram label)) := by
  simp [sampleCode,copyLabel,label.isLt]

private theorem sample_code (label : Fin 44) : sampleCode (sampleLabel label) =
    BitOracleReturnLink.command sampleLabel none (samplerCode label) := by
  have ha : ¬ (sampleLabel label).val < 2 := by simp only [sampleLabel]; omega
  have hb : sampleLabel label ≠ 2 := by
    intro h
    have he := congrArg Fin.val h
    change label.val+3 = 2 at he
    omega
  rw [sampleCode,dif_neg ha,if_neg hb]
  rfl

private theorem gate_step (record key cache log : List Bool) :
    step sampleCode (BitOracleReturnLink.embed copyLabel (some 2) (copyState none record record key cache log)) =
      pure (BitOracleReturnLink.embed sampleLabel none (samplerStart record key cache log),2) := by
  change pure ((⟨some 3,0,_⟩ : Config 12 47 3),2) = pure (_,2)
  congr 2
  change (⟨_,_,_⟩ : Config 12 47 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem tail_run (slack q : Nat) (hq : 0 < q) (key cache log : List Bool) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack → charge bits ≤ 2+PreparedScalarMachine.cost false slack q) ∧
      run sampleCode (1+PreparedScalarMachine.clock false slack q)
        (BitOracleReturnLink.embed copyLabel (some 2)
          (copyState none (SamplerOperands.input slack q []) (SamplerOperands.input slack q []) key cache log)) =
      (fun bits => (sampleResult (uniformNatEncode (bitsValue bits % q)) q.bits key cache log
        (SamplerOperands.input slack q []),charge bits)) <$> CoinWordLoader.word (q.size+slack) := by
  obtain ⟨charge,hc,hr⟩ := PreparedScalarMachine.run_source false slack q hq
  refine ⟨fun bits => 2+charge bits,fun bits hb => Nat.add_le_add_left (hc bits hb) 2,?_⟩
  rw [Nat.add_comm 1,run,gate_step,pure_bind]
  rw [BitOracleReturnLink.rename_run samplerCode sampleCode sampleLabel sample_code]
  rw [samplerStart,samplerCode,BitOracleStackFrame.run,hr]
  simp [sampleResult,samplerResult,Functor.map_map,PreparedScalarMachine.width,SamplerOperands.range]

/-- Actual transfer from caller port 11, preparation and sampling, preserving
all four retained records and the complete charged coin tree. -/
theorem sample_run (slack q : Nat) (hq : 0 < q) (key cache log : List Bool) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack → charge bits ≤ sampleCost slack q) ∧
      run sampleCode (sampleClock slack q) (sampleStart (SamplerOperands.input slack q []) key cache log) =
      (fun bits => (sampleResult (uniformNatEncode (bitsValue bits % q)) q.bits key cache log
        (SamplerOperands.input slack q []),charge bits)) <$> CoinWordLoader.word (q.size+slack) := by
  obtain ⟨first,hf,he⟩ := copy_run (SamplerOperands.input slack q []) key cache log
  obtain ⟨last,hl,ht⟩ := tail_run slack q hq key cache log
  have hh : ∀ out ∈ support (run (fun label => .compute (copyProgram label))
      (2*(SamplerOperands.input slack q []).length+2)
      (copyState (some false) (SamplerOperands.input slack q []) [] key cache log)), out.1.l = none := by
    intro out ho
    rw [he] at ho
    have ho' := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have hc : ∀ out ∈ support (run (fun label => .compute (copyProgram label))
      (2*(SamplerOperands.input slack q []).length+2)
      (copyState (some false) (SamplerOperands.input slack q []) [] key cache log)),
      ∀ done ∈ support (run sampleCode (1+PreparedScalarMachine.clock false slack q)
        (BitOracleReturnLink.embed copyLabel (some 2) out.1)), done.1.l = none := by
    intro out ho
    rw [he] at ho
    have ho' := eq_of_mem_support_pure _ ho
    subst out
    intro done hd
    rw [ht] at hd
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ hd
    rfl
  have hrun := BitOracleReturnLink.run (fun label => .compute (copyProgram label)) sampleCode
    copyLabel 2 copy_code (2*(SamplerOperands.input slack q []).length+2)
    (1+PreparedScalarMachine.clock false slack q)
    (copyState (some false) (SamplerOperands.input slack q []) [] key cache log) hh hc
  refine ⟨fun bits => first+last bits,?_,?_⟩
  · intro bits hb
    have h := hl bits hb
    change first+last bits ≤ sampleCost slack q
    unfold sampleCost
    omega
  · change run sampleCode (sampleClock slack q) (sampleStart _ key cache log) = _ at hrun
    rw [hrun,he,pure_bind,ht]
    simp [Functor.map_map]

/-- The word returned after the executed caller transfer is the original sampler
observation. Arbitrary retained key/cache/log words do not affect its coin tree. -/
theorem sample_value (slack q : Nat) [NeZero q] (key cache log : List Bool) :
    (fun out => out.1.stk 5) <$>
      run sampleCode (sampleClock slack q) (sampleStart (SamplerOperands.input slack q []) key cache log) =
      simulateQ CoinWordLoader.liftCoins ((fun a => uniformNatEncode a.val) <$> sampleFairBitRange q slack) := by
  obtain ⟨charge,_,hr⟩ := sample_run slack q (Nat.pos_of_ne_zero (NeZero.ne _)) key cache log
  rw [hr,Functor.map_map]
  change (fun bits => uniformNatEncode (bitsValue bits % q)) <$> CoinWordLoader.word (q.size+slack) = _
  have h := congrArg (fun oa : OracleComp spec Nat => (fun v => uniformNatEncode (v % q)) <$> oa)
    (CoinWordLoader.word_index (q.size+slack))
  simpa only [simulateQ_map,Functor.map_map,sampleFairBitRange,sampleFairBitModulo,Function.comp_def] using h

end ExplainableCrypto.Helios.Computational.CacheHashMachine
