import ExplainableCrypto.Helios.Computational.NonceOperands

/-! Changed-program correspondence for predecessor preparation. Prefix parsing
and decrement use their original executed routines; a scoped instruction-
agreement proof transfers only the unchanged width-collection region. -/
namespace ExplainableCrypto.Helios.Computational.NonceOperands
open Turing.TM2
open SamplerOperands (state)
set_option maxRecDepth 8192

private def finishing (label : Option Label) : Prop :=
  label = none ∨ label = some .ready ∨ label = some .collect ∨ label = some .restore

private theorem finishing_step (cfg : Config) (h : finishing cfg.l) :
    tick cfg = SamplerOperands.tick cfg ∧ finishing (tick cfg).l := by
  rcases cfg with ⟨label,v,words⟩
  change label = none ∨ label = some .ready ∨ label = some .collect ∨ label = some .restore at h
  rcases h with h | h | h | h <;> subst label
  · exact ⟨rfl,Or.inl rfl⟩
  · refine ⟨rfl,?_⟩
    cases hh : (words 1).head? <;>
      simp [finishing,tick,TM2ReturnLink.tick,program,SamplerOperands.program,step,stepAux,hh]
    exact Or.inl rfl
  · refine ⟨rfl,?_⟩
    cases hh : (words 1).head? <;>
      simp [finishing,tick,TM2ReturnLink.tick,program,SamplerOperands.program,step,stepAux,hh]
  · refine ⟨rfl,?_⟩
    cases hh : (words 3).head? <;>
      simp [finishing,tick,TM2ReturnLink.tick,program,SamplerOperands.program,step,stepAux,hh]

private theorem finishing_run (fuel : Nat) (cfg : Config) (h : finishing cfg.l) :
    tick^[fuel] cfg = SamplerOperands.tick^[fuel] cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    rw [ih (tick cfg) (finishing_step cfg h).2,(finishing_step cfg h).1]

private theorem ready_run (slack q : Nat) (hq : 0 < q) (suffix : List Bool) (frame : Frame)
    (v : Option Bool) :
    tick^[2*q.size+3] (state (some .ready) suffix q.bits (List.replicate slack true) [] [] frame v) =
      SamplerOperands.result slack q suffix frame := by
  rw [finishing_run _ _ (Or.inr (Or.inl rfl))]
  exact SamplerOperands.ready_run slack q hq suffix frame v

private theorem slack_run (n : Nat) (word width : List Bool) (frame : Frame) (v : Option Bool) :
    tick^[n+1] (state (some (.slack false)) (List.replicate n true ++ false::word)
      [] width [] [] frame v) =
      state (some (.parse false .width)) word [] (List.replicate n true ++ width) [] [] frame (some false) := by
  induction n generalizing width v with
  | zero =>
    simp [tick,TM2ReturnLink.tick,state,program,SamplerOperands.program,stepAux]
    funext k; fin_cases k <;> rfl
  | succ n ih =>
    have hs : tick (state (some (.slack false)) (true::(List.replicate n true ++ false::word))
        [] width [] [] frame v) =
        state (some (.slack false)) (List.replicate n true ++ false::word)
          [] (true::width) [] [] frame (some true) := by
      simp [tick,TM2ReturnLink.tick,state,program,SamplerOperands.program,stepAux]
      funext k; fin_cases k <;> rfl
    rw [List.replicate_succ,List.cons_append,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    rw [show List.replicate n true ++ true::width = List.replicate (n+1) true ++ width by
      rw [List.replicate_succ',List.append_assoc]; rfl]
    rfl

private def parserFrame (width : List Bool) (frame : Frame) : Fin 4 → List Bool :=
  ![width,frame 0,frame 1,frame 2]

private theorem parse_run (n : Nat) (suffix width : List Bool) (frame : Frame) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (state (some (.parse false .width)) (uniformNatEncode n++suffix)
        [] width [] [] frame (some false)) =
        state (some (.parsed false)) suffix n.bits width [] [] frame (some true) := by
  let c := NatPrefixMachine.config (some .width) (uniformNatEncode n++suffix) [] [] [] (some false)
  have hstart : NatPrefixMachine.tick c = NatPrefixMachine.tick (NatPrefixMachine.start (uniformNatEncode n++suffix)) := rfl
  have hr : NatPrefixMachine.tick^[3*n.size+3] c =
      NatPrefixMachine.config none suffix [] [] n.bits (some true) := by
    rw [Function.iterate_succ_apply,hstart,← Function.iterate_succ_apply]
    exact NatPrefixMachine.encoded_run n suffix
  have he := TM2StackFrame.run SamplerOperands.layout NatPrefixMachine.program (3*n.size+3)
    c (parserFrame width frame)
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate SamplerOperands.layout (NatPrefixMachine.program l)))^[_]
    (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) = _ at he
  change _ = TM2StackFrame.embed SamplerOperands.layout (NatPrefixMachine.tick^[3*n.size+3] c)
    (parserFrame width frame) at he
  rw [hr] at he
  obtain ⟨u,hu,hh⟩ := TM2ReturnLink.run
    (fun l => TM2StackFrame.relocate SamplerOperands.layout (NatPrefixMachine.program l)) program
    (.parse false) (.parsed false) (fun _ => rfl) (3*n.size+3)
    (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) (by rw [he]; rfl)
  rw [he] at hh
  refine ⟨u,hu,?_⟩
  have ha : TM2ReturnLink.embed (.parse false) (.parsed false)
      (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) =
      state (some (.parse false .width)) (uniformNatEncode n++suffix) [] width [] [] frame (some false) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  have hb : TM2ReturnLink.embed (.parse false) (.parsed false)
      (TM2StackFrame.embed SamplerOperands.layout
        (NatPrefixMachine.config none suffix [] [] n.bits (some true)) (parserFrame width frame)) =
      state (some (.parsed false)) suffix n.bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  rw [ha,hb] at hh
  exact hh

private theorem decrement_run (n : Nat) (hn : 0 < n) (suffix width : List Bool) (frame : Frame) :
    ∃ used ≤ 2*n.size+1,
      tick^[used] (state (some (.increment false)) suffix n.bits width [] [] frame (some true)) =
        state (some .ready) suffix (n-1).bits width [] [] frame (some true) := by
  obtain ⟨u,hu,hr⟩ := BitCounterMachine.run n suffix [] (some true)
  simp only [show n ≠ 0 by omega,ne_eq,not_false_eq_true,decide_true] at hr
  let c := BitCounterMachine.config (some false) n.bits [] suffix [] (some true)
  have he := TM2StackFrame.run SamplerOperands.layout BitCounterMachine.program u c (parserFrame width frame)
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate SamplerOperands.layout (BitCounterMachine.program l)))^[u]
    (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) = _ at he
  change _ = TM2StackFrame.embed SamplerOperands.layout (BitCounterMachine.tick^[u] c) (parserFrame width frame) at he
  rw [show BitCounterMachine.tick^[u] c = BitCounterMachine.config none (n-1).bits [] suffix [] (some true) from hr] at he
  obtain ⟨v,hv,hh⟩ := TM2ReturnLink.run
    (fun l => TM2StackFrame.relocate SamplerOperands.layout (BitCounterMachine.program l)) program
    .increment .ready (fun _ => rfl) u
    (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) (by rw [he]; rfl)
  rw [he] at hh
  refine ⟨v,hv.trans hu,?_⟩
  have ha : TM2ReturnLink.embed .increment .ready
      (TM2StackFrame.embed SamplerOperands.layout c (parserFrame width frame)) =
      state (some (.increment false)) suffix n.bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  have hb : TM2ReturnLink.embed .increment .ready
      (TM2StackFrame.embed SamplerOperands.layout
        (BitCounterMachine.config none (n-1).bits [] suffix [] (some true)) (parserFrame width frame)) =
      state (some .ready) suffix (n-1).bits width [] [] frame (some true) := by
    apply congrArg (Cfg.mk _ _); funext k; fin_cases k <;> rfl
  rw [ha,hb] at hh
  exact hh

/-- Canonical public q is parsed and decremented before its actual width is
collected. Every suffix and saved word survives; only final halt is padded. -/
theorem run (slack q : Nat) (hq : 2 ≤ q) (suffix : List Bool) (frame : Frame) :
    tick^[clock slack q] (SamplerOperands.start false (SamplerOperands.input slack q suffix) frame) =
      SamplerOperands.result slack (q-1) suffix frame := by
  obtain ⟨u,hu,hr⟩ := parse_run q suffix (List.replicate slack true) frame
  obtain ⟨v,hv,hvRun⟩ := decrement_run q (by omega) suffix (List.replicate slack true) frame
  have hs : tick (state (some (.parsed false)) suffix q.bits (List.replicate slack true) [] [] frame (some true)) =
      state (some (.increment false)) suffix q.bits (List.replicate slack true) [] [] frame (some true) := by
    simp [tick,TM2ReturnLink.tick,state,program,stepAux]
  have he : tick^[(2*(q-1).size+3)+(v+(1+(u+(slack+1))))]
      (SamplerOperands.start false (SamplerOperands.input slack q suffix) frame) =
      SamplerOperands.result slack (q-1) suffix frame := by
    rw [Function.iterate_add_apply (m := 2*(q-1).size+3),Function.iterate_add_apply (m := v),
      Function.iterate_add_apply (m := 1),Function.iterate_add_apply (m := u)]
    unfold SamplerOperands.start SamplerOperands.input
    rw [slack_run]
    simp only [List.append_nil]
    rw [hr,Function.iterate_one,hs,hvRun,ready_run slack (q-1) (by omega)]
  have hb : (2*(q-1).size+3)+(v+(1+(u+(slack+1)))) ≤ clock slack q := by unfold clock; omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
  rw [hd,Nat.add_comm _ d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

/-- All actual local statements have a fixed finite charge bound. -/
theorem local_cost (l : Fin size) : BitOracleMachine.localCost (compiled l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Complete canonical predecessor preparation starts with blank work ports and
has derived termination and charge. No modulus conversion is supplied by a caller. -/
theorem charged (slack q : Nat) (hq : 2 ≤ q) :
    ∃ charge ≤ cost slack q,
      BitOracleMachine.run code (clock slack q) (startWord (SamplerOperands.input slack q [])) =
        pure (result slack q [] (fun _ => []),charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost compiled 32 local_cost
    (clock slack q) (startWord (SamplerOperands.input slack q []))
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run (fun l => .compute (compiled l)) (clock slack q)
    (startWord (SamplerOperands.input slack q [])) = _
  rw [he]
  rw [startWord,compiled,SamplerOperands.present,TM2FiniteCoordinates.run]
  change pure (SamplerOperands.present (tick^[clock slack q]
    (SamplerOperands.start false (SamplerOperands.input slack q []) (fun _ => []))),charge) = _
  rw [run slack q hq [] (fun _ => [])]
  rfl

#print axioms run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.NonceOperands
