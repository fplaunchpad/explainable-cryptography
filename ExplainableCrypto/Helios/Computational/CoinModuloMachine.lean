import ExplainableCrypto.Helios.Computational.BinaryModuloCode
import ExplainableCrypto.Helios.Computational.CoinWordLoader

/-! One fixed raw-port program linking the actual coin loader and division.
Width and canonical modulus are loaded operands; the produced scalar is a word. -/
namespace ExplainableCrypto.Helios.Computational.CoinModuloMachine
open OracleComp OracleSpec BitOracleMachine
abbrev Config := BitOracleMachine.Config 8 20 3

private def divLabel (l : Fin 15) : Fin 20 := ⟨l.val, by omega⟩
private def loadLabel (l : Fin 4) : Fin 20 := ⟨l.val+15, by omega⟩

private def layout : Fin 5 ⊕ Fin 3 ≃ Fin 8 where
  toFun | .inl k => ![2,4,5,6,1] k | .inr k => ![0,3,7] k
  invFun := ![.inr 0,.inl 4,.inl 0,.inr 1,.inl 1,.inl 2,.inl 3,.inr 2]
  left_inv k := by cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def loadCode (l : Fin 4) : Command 8 20 3 :=
  match CoinWordLoader.code l with
  | .compute stmt => .compute (TM2ReturnLink.redirect loadLabel 11
      (TM2StackFrame.relocate layout stmt))
  | .coin dest next => .coin (layout (.inl dest)) (loadLabel next)
  | .hash req dest next => .hash (layout (.inl req)) (layout (.inl dest)) (loadLabel next)

/-- Deterministic division region; its return label halts. -/
def division (l : Fin 20) : Turing.TM2.Stmt (fun _ : Fin 8 => Bool) (Fin 20) (Fin 3) :=
  if h : l.val < 15 then
    TM2ReturnLink.redirect divLabel 19 (BinaryModuloCode.program ⟨l.val,h⟩)
  else .halt

/-- No instruction depends on the security parameter or a host natural operand. -/
def code (l : Fin 20) : Command 8 20 3 :=
  if h : 15 ≤ l.val ∧ l.val < 19 then loadCode ⟨l.val-15, by omega⟩
  else .compute (division l)

def loading (phase : Option (Fin 20)) (width response acc out modulus : List Bool) : Config :=
  ⟨phase, 0, ![[],modulus,width,[],response,acc,out,[]]⟩

def result (digits modulus : List Bool) : Config :=
  ⟨none, 0, ![digits,modulus,[],[],[],[],[],[]]⟩

private theorem div_eq (l : Fin 15) :
    division (divLabel l) = TM2ReturnLink.redirect divLabel 19 (BinaryModuloCode.program l) := by
  simp [division, divLabel, l.isLt]

private theorem code_div (l : Fin 20) (h : l.val < 15 ∨ l = 19) :
    code l = .compute (division l) := by
  unfold code
  split
  · rename_i hh
    rcases h with h | rfl
    · omega
    · norm_num at hh
  · rfl

private theorem count_step (b : Bool) (width acc out modulus : List Bool) :
    step code (loading (some 15) (b::width) [] acc out modulus) =
      pure (loading (some 16) width [] acc out modulus, 4) := by
  cases b <;> simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout,
    TM2StackFrame.relocate, TM2ReturnLink.redirect, loadLabel, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem count_done (acc out modulus : List Bool) :
    step code (loading (some 15) [] [] acc out modulus) =
      pure (loading (some 18) [] [] acc out modulus, 4) := by
  simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout,
    TM2StackFrame.relocate, TM2ReturnLink.redirect, loadLabel, localCost, Turing.TM2.stepAux]

private theorem coin_step (width acc out modulus : List Bool) :
    step code (loading (some 16) width [] acc out modulus) = (do
      let b ← liftM (spec.query .coin)
      pure (loading (some 17) width [b] acc out modulus, 2)) := by
  simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout, loadLabel, resume]
  congr 1
  funext b
  congr 2
  funext j; fin_cases j <;> rfl

private theorem collect_step (b : Bool) (width acc out modulus : List Bool) :
    step code (loading (some 17) width [b] acc out modulus) =
      pure (loading (some 15) width [] (b::acc) out modulus, 4) := by
  cases b <;> simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout,
    TM2StackFrame.relocate, TM2ReturnLink.redirect, loadLabel, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem reverse_step (b : Bool) (acc out modulus : List Bool) :
    step code (loading (some 18) [] [] (b::acc) out modulus) =
      pure (loading (some 18) [] [] acc (b::out) modulus, 5) := by
  cases b <;> simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout,
    TM2StackFrame.relocate, TM2ReturnLink.redirect, loadLabel, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem reverse_done (out modulus : List Bool) :
    step code (loading (some 18) [] [] [] out modulus) =
      pure (loading (some 11) [] [] [] out modulus, 5) := by
  simp [step, code, loadCode, CoinWordLoader.code, CoinWordLoader.encode, loading, layout,
    TM2StackFrame.relocate, TM2ReturnLink.redirect, localCost, Turing.TM2.stepAux]

private theorem reverse_run (acc out modulus : List Bool) :
    run code (acc.length+1) (loading (some 18) [] [] acc out modulus) =
      pure (loading (some 11) [] [] [] (acc.reverse ++ out) modulus, 5*acc.length+5) := by
  induction acc generalizing out with
  | nil => simp [run, reverse_done]
  | cons b acc ih =>
    rw [List.length_cons, Nat.add_right_comm, run, reverse_step]
    simp only [pure_bind]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_comm]

private theorem loop (width acc out modulus : List Bool) :
    run code (4*width.length+acc.length+2) (loading (some 15) width [] acc out modulus) =
      (fun bits => (loading (some 11) [] [] [] (acc.reverse ++ bits ++ out) modulus,
        15*width.length+5*acc.length+9)) <$> CoinWordLoader.word width.length := by
  induction width generalizing acc with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, CoinWordLoader.word, map_pure]
    rw [show acc.length+2 = (acc.length+1)+1 by omega, run, count_done]
    simp only [pure_bind, reverse_run]
    simp only [List.append_nil]
    apply congrArg (pure : Config × Nat → OracleComp spec _)
    apply Prod.ext
    · rfl
    · omega
  | cons token width ih =>
    rw [show 4*(token::width).length+acc.length+2 =
      ((4*width.length+(false::acc).length+2)+1)+1+1 by simp; omega,
      run, count_step]
    simp only [pure_bind]
    rw [run, coin_step]
    simp only [bind_assoc, pure_bind]
    rw [show (token::width).length = width.length+1 from rfl, CoinWordLoader.word]
    simp only [map_bind]
    apply bind_congr
    intro b
    change Bool at b
    rw [run, collect_step]
    simp only [pure_bind]
    rw [show (false::acc).length = (b::acc).length from rfl, ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr
    intro bits
    apply congrArg (pure : Config × Nat → OracleComp spec _)
    apply Prod.ext
    · simp [List.reverse_cons, List.append_assoc]
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- The actual relocated loader reaches division on the same stacks.
The first coin is still the least-significant bit; all loader scratch is cleared. -/
theorem load_run (width modulus : List Bool) :
    run code (4*width.length+2) (loading (some 15) width [] [] [] modulus) =
      (fun bits => (loading (some 11) [] [] [] bits modulus, 15*width.length+9)) <$>
        CoinWordLoader.word width.length := by
  simpa using loop width [] [] modulus

private def safeSet : Finset (Fin 20) := Finset.univ.filter (fun l => l.val < 15 ∨ l = 19)

private theorem division_supports : Turing.TM2.Supports division safeSet := by
  have hs (stmt : Turing.TM2.Stmt (fun _ : Fin 8 => Bool) (Fin 15) (Fin 3)) :
      Turing.TM2.SupportsStmt safeSet (TM2ReturnLink.redirect divLabel 19 stmt) := by
    induction stmt <;> simp_all [TM2ReturnLink.redirect, Turing.TM2.SupportsStmt,
      safeSet, divLabel]
  refine ⟨by decide, ?_⟩
  intro l _
  unfold division
  split
  · exact hs _
  · trivial

private theorem division_safe (cfg : Config) (h : cfg.l ∈ Finset.insertNone safeSet) :
    (TM2ReturnLink.tick division cfg).l ∈ Finset.insertNone safeSet := by
  cases he : Turing.TM2.step division cfg with
  | none => simpa [TM2ReturnLink.tick, he] using h
  | some next =>
    have hn := Turing.TM2.step_supports division division_supports
      (show next ∈ Turing.TM2.step division cfg by rw [he]; rfl) h
    simpa [TM2ReturnLink.tick, he] using hn

private theorem redirect_cost (stmt : Turing.TM2.Stmt (fun _ : Fin 8 => Bool) (Fin 15) (Fin 3)) :
    localCost (TM2ReturnLink.redirect divLabel 19 stmt) = localCost stmt := by
  induction stmt <;> simp_all [TM2ReturnLink.redirect, localCost]

private theorem division_cost (l : Fin 20) : localCost (division l) ≤ 32 := by
  unfold division
  split
  · rw [redirect_cost]
    exact BinaryModuloCode.local_cost _
  · decide

private theorem compute_run (fuel : Nat) (cfg : Config)
    (h : cfg.l ∈ Finset.insertNone safeSet) :
    ∃ charge ≤ 32*fuel, run code fuel cfg =
      pure ((TM2ReturnLink.tick division)^[fuel] cfg, charge) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ fuel ih =>
    have hn := division_safe cfg h
    obtain ⟨charge,hcharge,he⟩ := ih (TM2ReturnLink.tick division cfg) hn
    cases cfg with
    | mk label v words =>
      cases label with
      | none =>
        refine ⟨charge,by rw [Nat.mul_succ]; omega,?_⟩
        simpa only [run, step, pure_bind, TM2ReturnLink.tick, Turing.TM2.step,
          Option.getD_none, Nat.zero_add, Function.iterate_succ_apply, Prod.mk.eta, bind_pure] using he
      | some l =>
        have hl : l.val < 15 ∨ l = 19 := by simpa [safeSet] using h
        refine ⟨localCost (division l)+charge,?_,?_⟩
        · have := division_cost l
          rw [Nat.mul_succ]
          omega
        · simpa only [run, step, code_div l hl, pure_bind, TM2ReturnLink.tick,
            Turing.TM2.step, Option.getD_some, he, Function.iterate_succ_apply] using
            congrArg (fun computation : OracleComp spec (Config × Nat) =>
              computation >>= fun out => pure (out.1, localCost (division l)+out.2)) he

private theorem present_initial (bits : List Bool) (q : Nat) :
    TM2ReturnLink.embed divLabel 19
      (BinaryModuloCode.present (BinaryModuloMachine.state (some .reverseInput) [] q.bits [] [] bits [])) =
        loading (some 11) [] [] [] bits q.bits := by
  apply congrArg (fun tapes => (⟨some 11,0,tapes⟩ : Config))
  funext k; fin_cases k <;> rfl

private theorem present_result (bits : List Bool) (q : Nat) :
    TM2ReturnLink.embed divLabel 19
      (BinaryModuloCode.present (BinaryModuloMachine.state none bits q.bits [] [] [] [])) =
        ⟨some 19, 0, (result bits q.bits).stk⟩ := by
  apply congrArg (fun tapes => (⟨some 19,0,tapes⟩ : Config))
  funext k; fin_cases k <;> rfl

private theorem division_complete (bits : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ used ≤ bits.length*(8*q.size+13)+3,
      (TM2ReturnLink.tick division)^[used] (loading (some 11) [] [] [] bits q.bits) =
        result (bitsValue bits % q).bits q.bits := by
  obtain ⟨u,hu,he⟩ := BinaryModuloMachine.run bits q hq
  have hc := BinaryModuloCode.run u
    (BinaryModuloMachine.state (some .reverseInput) [] q.bits [] [] bits [])
  rw [he] at hc
  obtain ⟨v,hv,hvRun⟩ := TM2ReturnLink.run BinaryModuloCode.program division divLabel 19
    div_eq u (BinaryModuloCode.present
      (BinaryModuloMachine.state (some .reverseInput) [] q.bits [] [] bits []))
    (by rw [hc]; rfl)
  rw [hc, present_initial, present_result] at hvRun
  refine ⟨1+v,by omega,?_⟩
  rw [Function.iterate_add_apply, hvRun]
  simp [TM2ReturnLink.tick, Turing.TM2.step, division,
    Turing.TM2.stepAux, result]

/-- Division within the combined oracle program halts without any oracle event.
Its fixed observation clock and complete local charge are derived. -/
theorem divide_run (bits : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge ≤ 32*(bits.length*(8*q.size+13)+3),
      run code (bits.length*(8*q.size+13)+3) (loading (some 11) [] [] [] bits q.bits) =
        pure (result (bitsValue bits % q).bits q.bits, charge) := by
  obtain ⟨u,hu,he⟩ := division_complete bits q hq
  obtain ⟨charge,hcharge,hRun⟩ := compute_run (bits.length*(8*q.size+13)+3)
    (loading (some 11) [] [] [] bits q.bits) (by simp [loading, safeSet])
  refine ⟨charge,hcharge,?_⟩
  rw [hRun]
  have ht : bits.length*(8*q.size+13)+3 = (bits.length*(8*q.size+13)+3-u)+u := by omega
  rw [ht, Function.iterate_add_apply, he]
  rw [Function.iterate_fixed (show TM2ReturnLink.tick division
    (result (bitsValue bits % q).bits q.bits) = result (bitsValue bits % q).bits q.bits from rfl)]

private theorem run_add (a b : Nat) (cfg : Config) :
    run code (a+b) cfg = (do
      let first ← run code a cfg
      let rest ← run code b first.1
      pure (rest.1, first.2+rest.2)) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc, Nat.add_assoc]

def clock (w q : Nat) : Nat := (4*w+2)+(w*(8*q.size+13)+3)
def cost (w q : Nat) : Nat := 15*w+9+32*(w*(8*q.size+13)+3)

/-- The one fixed machine queries the actual coin word, executes division,
returns canonical digits and clears scratch. Both clock and leaf charges are
derived; the same full oracle tree is retained before choosing a handler. -/
theorem run_source (width : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = width.length → charge bits ≤ cost width.length q) ∧
      run code (clock width.length q) (loading (some 15) width [] [] [] q.bits) =
        (fun bits => (result (bitsValue bits % q).bits q.bits, charge bits)) <$>
          CoinWordLoader.word width.length := by
  choose spent hspent hrun using fun bits => divide_run bits q hq
  refine ⟨fun bits => 15*width.length+9+spent bits,?_,?_⟩
  · intro bits hlen
    simpa [cost,hlen] using Nat.add_le_add_left (hspent bits) (15*width.length+9)
  · rw [clock,run_add,load_run]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr_of_forall_mem_support
    intro bits hb
    have hlen := CoinWordLoader.word_length width.length bits hb
    rw [← hlen,hrun]
    simp

/-- Numeric observation of executed division equals the original modulo sampler.
The machine's instructions have already produced the canonical digits. -/
theorem sampler_value (q : Nat) [NeZero q] (width : List Bool) :
    (fun out => bitsValue (out.1.stk 0)) <$>
      run code (clock width.length q) (loading (some 15) width [] [] [] q.bits) =
      simulateQ CoinWordLoader.liftCoins (Fin.val <$> sampleFairBitModulo q width.length) := by
  obtain ⟨charge,_,he⟩ := run_source width q (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [he]
  have h := congrArg (fun computation : OracleComp spec Nat =>
    (fun n => n % q) <$> computation) (CoinWordLoader.word_index width.length)
  simpa [sampleFairBitModulo, simulateQ_map, Functor.map_map, result, bitsValue_bits] using h

end ExplainableCrypto.Helios.Computational.CoinModuloMachine
