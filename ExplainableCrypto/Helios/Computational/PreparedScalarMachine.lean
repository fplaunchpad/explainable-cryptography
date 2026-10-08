import ExplainableCrypto.Helios.Computational.SamplerOperands
import ExplainableCrypto.Helios.Computational.BitOracleInitialInput

/-! One fixed program from serialized operands through actual scalar sampling.
The gate rejects failed preparation or unconsumed input before any coin query. -/
namespace ExplainableCrypto.Helios.Computational.PreparedScalarMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private def prepLabel (l : Fin 15) : Fin 44 := ⟨l.val,by omega⟩
private def sampleLabel (l : Fin 28) : Fin 44 := ⟨l.val+16,by omega⟩

private def fail : Turing.TM2.Stmt (fun _ : Fin 8 => Bool) (Fin 44) (Fin 3) :=
  .load (fun _ => 1) .halt

def gate : Turing.TM2.Stmt (fun _ : Fin 8 => Bool) (Fin 44) (Fin 3) :=
  .branch (fun v => v == 0)
    (.peek 4 (fun _ b => CoinWordLoader.encode b)
      (.branch (fun v => v == 0) (.load (fun _ => 0) (.goto (fun _ => 31))) fail)) fail

def code (l : Fin 44) : Command 8 44 3 :=
  if h : l.val < 15 then
    BitOracleReturnLink.command prepLabel (some 15) (.compute (SamplerOperands.compiled ⟨l.val,h⟩))
  else if l = 15 then .compute gate
  else BitOracleReturnLink.command sampleLabel none (CoinScalarMachine.code ⟨l.val-16,by omega⟩)

def startWord (mode : Bool) (word : List Bool) : Config 8 44 3 :=
  BitOracleReturnLink.embed prepLabel (some 15)
    (SamplerOperands.present (SamplerOperands.start mode word (fun _ => [])))

def result (word modulus : List Bool) : Config 8 44 3 :=
  BitOracleReturnLink.embed sampleLabel none (CoinScalarMachine.result word modulus)

def width (mode : Bool) (slack n : Nat) : Nat := (SamplerOperands.range mode n).size+slack
def clock (mode : Bool) (slack n : Nat) : Nat :=
  SamplerOperands.clock mode slack n+ (1+CoinScalarMachine.clock (width mode slack n) (SamplerOperands.range mode n))
def cost (mode : Bool) (slack n : Nat) : Nat :=
  32*SamplerOperands.clock mode slack n+5+CoinScalarMachine.cost (width mode slack n) (SamplerOperands.range mode n)

private theorem prep_code (l : Fin 15) : code (prepLabel l) =
    BitOracleReturnLink.command prepLabel (some 15) (.compute (SamplerOperands.compiled l)) := by
  simp [code,prepLabel,l.isLt]

private theorem sample_code (l : Fin 28) : code (sampleLabel l) =
    BitOracleReturnLink.command sampleLabel none (CoinScalarMachine.code l) := by
  have ha : ¬ (sampleLabel l).val < 15 := by simp only [sampleLabel]; omega
  have hb : sampleLabel l ≠ 15 := by
    intro h
    have he := congrArg Fin.val h
    change l.val+16 = 15 at he
    omega
  rw [code,dif_neg ha,if_neg hb]
  rfl

private theorem sample_run (fuel : Nat) (cfg : CoinScalarMachine.Config) :
    run code fuel (BitOracleReturnLink.embed sampleLabel none cfg) =
      (fun out => (BitOracleReturnLink.embed sampleLabel none out.1,out.2)) <$>
        run CoinScalarMachine.code fuel cfg :=
  BitOracleReturnLink.rename_run _ code sampleLabel sample_code fuel cfg

private theorem gate_step (slack q : Nat) :
    step code (BitOracleReturnLink.embed prepLabel (some 15)
      (SamplerOperands.present (SamplerOperands.result slack q [] (fun _ => [])))) =
      pure (BitOracleReturnLink.embed sampleLabel none
        (CoinScalarMachine.start (List.replicate (q.size+slack) true) q),5) := by
  simp [step,code,gate,fail,localCost,SamplerOperands.present,SamplerOperands.result,
    SamplerOperands.state,TM2FiniteCoordinates.present,TM2FiniteCoordinates.data,
    BinaryModuloCode.memory,BitOracleReturnLink.embed,CoinWordLoader.encode,Turing.TM2.stepAux,
    CoinScalarMachine.start,sampleLabel]
  rfl

private theorem continuation (slack q : Nat) (hq : 0 < q) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack → charge bits ≤ 5+CoinScalarMachine.cost (q.size+slack) q) ∧
      run code (1+CoinScalarMachine.clock (q.size+slack) q)
        (BitOracleReturnLink.embed prepLabel (some 15)
          (SamplerOperands.present (SamplerOperands.result slack q [] (fun _ => [])))) =
        (fun bits => (result (uniformNatEncode (bitsValue bits % q)) q.bits,charge bits)) <$>
          CoinWordLoader.word (q.size+slack) := by
  obtain ⟨charge,hc,he⟩ := CoinScalarMachine.run_source (List.replicate (q.size+slack) true) q hq
  refine ⟨fun bits => 5+charge bits,?_,?_⟩
  · intro bits hb
    have h := hc bits (by simpa using hb)
    simpa using Nat.add_le_add_left h 5
  · rw [Nat.add_comm 1,run,gate_step,pure_bind,sample_run]
    simp only [List.length_replicate] at he
    rw [he]
    simp [result,Functor.map_map]

/-- Complete uninterrupted execution from the original serialized input through
parsing, successor conversion, width construction, coins, division and writing.
Both return-link termination premises and total charge are derived. -/
theorem run_source (mode : Bool) (slack n : Nat) (hq : 0 < SamplerOperands.range mode n) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = width mode slack n → charge bits ≤ cost mode slack n) ∧
      run code (clock mode slack n) (startWord mode (SamplerOperands.input slack n [])) =
        (fun bits => (result (uniformNatEncode (bitsValue bits % SamplerOperands.range mode n))
          (SamplerOperands.range mode n).bits,charge bits)) <$>
          CoinWordLoader.word (width mode slack n) := by
  obtain ⟨prep,hp,he⟩ := SamplerOperands.charged mode slack n hq [] (fun _ => [])
  obtain ⟨tail,ht,htRun⟩ := continuation slack (SamplerOperands.range mode n) hq
  have hh : ∀ out ∈ support (run (fun l => .compute (SamplerOperands.compiled l))
      (SamplerOperands.clock mode slack n)
      (SamplerOperands.present (SamplerOperands.start mode (SamplerOperands.input slack n []) (fun _ => [])))),
      out.1.l = none := by
    intro out ho
    rw [he] at ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have hc : ∀ out ∈ support (run (fun l => .compute (SamplerOperands.compiled l))
      (SamplerOperands.clock mode slack n)
      (SamplerOperands.present (SamplerOperands.start mode (SamplerOperands.input slack n []) (fun _ => [])))),
      ∀ last ∈ support (run code (1+CoinScalarMachine.clock (width mode slack n) (SamplerOperands.range mode n))
        (BitOracleReturnLink.embed prepLabel (some 15) out.1)), last.1.l = none := by
    intro out ho
    rw [he] at ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    intro last hl
    dsimp only [width] at hl
    rw [htRun] at hl
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ hl
    rfl
  have hr := BitOracleReturnLink.run (fun l => .compute (SamplerOperands.compiled l)) code
    prepLabel 15 prep_code (SamplerOperands.clock mode slack n)
    (1+CoinScalarMachine.clock (width mode slack n) (SamplerOperands.range mode n))
    (SamplerOperands.present (SamplerOperands.start mode (SamplerOperands.input slack n []) (fun _ => []))) hh hc
  refine ⟨fun bits => prep+tail bits,?_,?_⟩
  · intro bits hb
    have h := ht bits hb
    change prep+tail bits ≤ 32*SamplerOperands.clock mode slack n+5+
      CoinScalarMachine.cost ((SamplerOperands.range mode n).size+slack) (SamplerOperands.range mode n)
    omega
  · change run code (clock mode slack n) (startWord mode (SamplerOperands.input slack n [])) = _ at hr
    rw [hr,he,pure_bind]
    dsimp only [width]
    rw [htRun]
    simp [Functor.map_map]

/-- Original fair-bit range sampler observed through its actual encoded output.
The proof removes neither operand preparation nor its executed cost from the run. -/
theorem sampler_value (mode : Bool) (slack n : Nat) [NeZero (SamplerOperands.range mode n)] :
    (fun out => out.1.stk 5) <$>
      run code (clock mode slack n) (startWord mode (SamplerOperands.input slack n [])) =
      simulateQ CoinWordLoader.liftCoins ((fun a => uniformNatEncode a.val) <$>
        sampleFairBitRange (SamplerOperands.range mode n) slack) := by
  obtain ⟨charge,_,hr⟩ := run_source mode slack n (Nat.pos_of_ne_zero (NeZero.ne _))
  rw [hr,Functor.map_map]
  change (fun bits => uniformNatEncode (bitsValue bits % SamplerOperands.range mode n)) <$>
    CoinWordLoader.word (width mode slack n) = _
  have h := congrArg (fun oa : OracleComp spec Nat =>
    (fun v => uniformNatEncode (v % SamplerOperands.range mode n)) <$> oa)
      (CoinWordLoader.word_index (width mode slack n))
  simpa only [simulateQ_map,Functor.map_map,sampleFairBitRange,sampleFairBitModulo,
    Function.comp_def,width] using h

private theorem word_within (limit bound w : Nat) (f : List Bool → Config 8 44 3 × Nat)
    (hf : ∀ bits, bits.length = w → (f bits).1.l = none ∧ (f bits).2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound (f <$> CoinWordLoader.word w) := by
  induction w generalizing f with
  | zero => exact hf [] rfl
  | succ w ih =>
    simp only [CoinWordLoader.word,map_bind,map_pure]
    change ∀ b : Bool, True → BitOracleLoopBounded.Within limit bound
      (CoinWordLoader.word w >>= fun bits => pure (f (b::bits)))
    intro b _
    simpa only [map_eq_bind_pure_comp,Function.comp_def] using
      ih (fun bits => f (b::bits)) (fun bits hb => hf (b::bits) (by simp [hb]))

/-- Actual source termination and charge, on every coin branch, discharge the
existing physical compiler's algorithmic contract. No supplied cost certificate. -/
theorem within (mode : Bool) (slack n limit : Nat) (hq : 0 < SamplerOperands.range mode n) :
    BitOracleLoopBounded.Within limit (cost mode slack n)
      (run code (clock mode slack n) (startWord mode (SamplerOperands.input slack n []))) := by
  obtain ⟨charge,hc,hr⟩ := run_source mode slack n hq
  rw [hr]
  apply word_within
  intro bits hb
  exact ⟨rfl,hc bits hb⟩

def entry (mode : Bool) : Fin 44 := if mode then 1 else 0

private theorem initial_source (mode : Bool) (word : List Bool) :
    startWord mode word = BitOracleInitialInput.source 4 (some (entry mode)) 0 word := by
  have he : Function.update (fun _ : Fin 8 => ([] : List Bool)) 4 word =
      ![[],[],[],[],word,[],[],[]] := by
    funext k; fin_cases k <;> simp [Function.update]
  cases mode <;>
    change (⟨_,0,![[],[],[],[],word,[],[],[]]⟩ : Config 8 44 3) =
      ⟨_,0,Function.update (fun _ => []) 4 word⟩
  all_goals rw [he]; rfl

private theorem initial_height (mode : Bool) (word : List Bool) :
    TM2TapeRuns.height (startWord mode word).stk = word.length := by
  rw [initial_source]
  change Finset.univ.sup (fun k : Fin 8 => (Function.update (fun _ => ([] : List Bool)) 4 word k).length) = word.length
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k _
    fin_cases k <;> simp
  · simpa using Finset.le_sup
      (f := fun k : Fin 8 => (Function.update (fun _ => ([] : List Bool)) 4 word k).length) (Finset.mem_univ 4)

/-- Physical raw input and blank work storage execute the complete prepared
sampler. The existing compiler supplies a polynomial clock from the derived
source cost; no input-loading, source-correspondence or runtime premise remains
for this sampler component. All bounded-handler coin effects are retained. -/
theorem physical_run (mode : Bool) (slack n limit : Nat) (hq : 0 < SamplerOperands.range mode n) :
    let word := SamplerOperands.input slack n []
    let B := cost mode slack n
    let T := BitOracleTapeCap.unitCost (word.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*word.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 4 (some (entry mode)) 0 (startup+T)
          (BitOracleInitialInput.initial word)) =
      (fun out => some out.1) <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (run code (clock mode slack n) (startWord mode word)) := by
  dsimp only
  have hw := within mode slack n limit hq
  rw [initial_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 4 (some (entry mode)) 0
    (SamplerOperands.input slack n []) (clock mode slack n) limit (cost mode slack n) hw
  rw [← initial_source mode,initial_height] at he
  exact ⟨startup,hs,by simpa only [Nat.add_zero] using he⟩

end ExplainableCrypto.Helios.Computational.PreparedScalarMachine
