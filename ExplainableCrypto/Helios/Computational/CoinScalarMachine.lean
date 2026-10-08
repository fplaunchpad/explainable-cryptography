import ExplainableCrypto.Helios.Computational.BitOracleReturnLink
import ExplainableCrypto.Helios.Computational.ScalarWriteCode

/-! One fixed program for coin loading, division and scalar prefix writing.
The actual source-return and final-writer termination premises are derived. -/
namespace ExplainableCrypto.Helios.Computational.CoinScalarMachine
open OracleComp OracleSpec BitOracleMachine
abbrev Config := BitOracleMachine.Config 8 28 3

private def samplerLabel (l : Fin 20) : Fin 28 := ⟨l.val,by omega⟩
private def writerLabel (l : Fin 8) : Fin 28 := ⟨l.val+20,by omega⟩

def code (l : Fin 28) : Command 8 28 3 :=
  if h : l.val < 20 then
    BitOracleReturnLink.command samplerLabel (some 25) (CoinModuloMachine.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command writerLabel none
    (.compute (ScalarWriteCode.program ⟨l.val-20,by omega⟩))

private theorem sampler_code (l : Fin 20) :
    code (samplerLabel l) = BitOracleReturnLink.command samplerLabel (some 25)
      (CoinModuloMachine.code l) := by
  simp [code,samplerLabel,l.isLt]

private theorem writer_code (l : Fin 8) :
    code (writerLabel l) = BitOracleReturnLink.command writerLabel none
      (.compute (ScalarWriteCode.program l)) := by
  simp [code,writerLabel]

/-- All input operands are exactly those of the existing coin-to-remainder program. -/
def start (width : List Bool) (q : Nat) : Config :=
  ⟨some 15,0,![[],q.bits,width,[],[],[],[],[]]⟩

def result (word modulus : List Bool) : Config :=
  ⟨none,2,![[],modulus,[],[],[],word,[],[]]⟩

def clock (w q : Nat) : Nat := CoinModuloMachine.clock w q + (3*(q-1).size+3)
def cost (w q : Nat) : Nat := CoinModuloMachine.cost w q + 32*(3*(q-1).size+3)

private theorem enter_writer (digits modulus : List Bool) :
    BitOracleReturnLink.embed samplerLabel (some 25) (CoinModuloMachine.result digits modulus) =
      BitOracleReturnLink.embed writerLabel none
        (ScalarWriteCode.resumeSampler (CoinModuloMachine.result digits modulus)) := by
  rfl

private theorem writer_run (fuel : Nat) (cfg : ScalarWriteCode.Config) :
    run code fuel (BitOracleReturnLink.embed writerLabel none cfg) =
      (fun out => (BitOracleReturnLink.embed writerLabel none out.1,out.2)) <$>
        run (fun l => .compute (ScalarWriteCode.program l)) fuel cfg :=
  BitOracleReturnLink.rename_run _ code writerLabel writer_code fuel cfg

private theorem writer_done (bits : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge ≤ 32*(3*(q-1).size+3),
      run code (3*(q-1).size+3)
        (BitOracleReturnLink.embed samplerLabel (some 25)
          (CoinModuloMachine.result (bitsValue bits % q).bits q.bits)) =
        pure (result (uniformNatEncode (bitsValue bits % q)) q.bits,charge) := by
  obtain ⟨charge,hc,he⟩ := ScalarWriteCode.from_sampler bits q hq
  refine ⟨charge,hc,?_⟩
  rw [enter_writer,writer_run,he,map_pure]
  rfl

/-- Exact whole-state and charge equality with the previously checked driver.
Both termination premises of return linking are derived from actual source runs. -/
theorem run_eq (width : List Bool) (q : Nat) (hq : 0 < q) :
    run code (clock width.length q) (start width q) =
      (fun out => (BitOracleReturnLink.embed writerLabel none out.1,out.2)) <$>
        ScalarWriteCode.sampleWord width q := by
  obtain ⟨sampled,hs,he⟩ := CoinModuloMachine.run_source width q hq
  have hh : ∀ out ∈ support (run CoinModuloMachine.code (CoinModuloMachine.clock width.length q)
      (CoinModuloMachine.loading (some 15) width [] [] [] q.bits)), out.1.l = none := by
    intro out ho
    rw [he] at ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  have hc : ∀ out ∈ support (run CoinModuloMachine.code (CoinModuloMachine.clock width.length q)
      (CoinModuloMachine.loading (some 15) width [] [] [] q.bits)),
      ∀ last ∈ support (run code (3*(q-1).size+3)
        (BitOracleReturnLink.embed samplerLabel (some 25) out.1)), last.1.l = none := by
    intro out ho
    rw [he] at ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    obtain ⟨charge,_,hr⟩ := writer_done bits q hq
    intro last hl
    rw [hr] at hl
    have hv := eq_of_mem_support_pure _ hl
    subst last
    rfl
  have h := BitOracleReturnLink.run CoinModuloMachine.code code samplerLabel 25 sampler_code
    (CoinModuloMachine.clock width.length q) (3*(q-1).size+3)
    (CoinModuloMachine.loading (some 15) width [] [] [] q.bits) hh hc
  change run code (clock width.length q) (start width q) = _ at h
  rw [h]
  simp only [ScalarWriteCode.sampleWord,he,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  apply bind_congr
  intro bits
  rw [enter_writer,writer_run]
  simp [map_eq_bind_pure_comp,bind_assoc]

/-- The uninterrupted fixed program returns the original prefix with the original
coin tree, cleared scratch, retained modulus, and a derived total charge. -/
theorem run_source (width : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = width.length → charge bits ≤ cost width.length q) ∧
      run code (clock width.length q) (start width q) =
        (fun bits => (result (uniformNatEncode (bitsValue bits % q)) q.bits,charge bits)) <$>
          CoinWordLoader.word width.length := by
  obtain ⟨charge,hc,he⟩ := ScalarWriteCode.sampleWord_source width q hq
  refine ⟨charge,hc,?_⟩
  rw [run_eq width q hq,he,Functor.map_map]
  rfl

/-- The final word observation retains the existing sampler's exact query syntax. -/
theorem sampler_value (q : Nat) [NeZero q] (width : List Bool) :
    (fun out => out.1.stk 5) <$> run code (clock width.length q) (start width q) =
      simulateQ CoinWordLoader.liftCoins
        ((fun a => uniformNatEncode a.val) <$> sampleFairBitModulo q width.length) := by
  rw [run_eq width q (Nat.pos_of_ne_zero (NeZero.ne q)),Functor.map_map]
  exact ScalarWriteCode.sampleWord_value q width

end ExplainableCrypto.Helios.Computational.CoinScalarMachine
