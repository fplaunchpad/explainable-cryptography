import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
import ExplainableCrypto.Helios.Computational.NatFieldWriterMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def words (old : Fin 43 → List Bool) (word : List Bool) : Fin 44 → List Bool :=
  Function.update (initialWords old) 43 word

def state (phase : Option (Fin 169)) (old : Fin 43 → List Bool) (word : List Bool) : Config :=
  ⟨phase,2,words old word⟩

def frame (which : Fin 8) (old : Fin 43 → List Bool) : Fin 37 → List Bool :=
  fun k => initialWords old (layout which (.inr k))

private theorem output_port (which : Fin 8) : layout which (.inl 1) = 43 := by
  fin_cases which <;> rfl

private theorem local_words (which : Fin 8) (old : Fin 43 → List Bool)
    (word : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (j : Fin 7) :
    words old word (layout which (.inl j)) = ![old (sourcePort which),word,[],[],[],[],[]] j := by
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have h3 := hw 3
  have h4 := hw 4
  fin_cases which <;> fin_cases j <;>
    first | rfl | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

private theorem data_words (which : Fin 8) (old : Fin 43 → List Bool)
    (word : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    TM2StackFrame.data (layout which) ![old (sourcePort which),word,[],[],[],[],[]]
      (frame which old) = words old word := by
  funext k
  obtain ⟨k,rfl⟩ := (layout which).surjective k
  cases k with
  | inl j =>
    simpa only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl] using
      (local_words which old word hw j).symm
  | inr j =>
    have hn : layout which (.inr j) ≠ 43 := by
      rw [←output_port which]
      intro h
      have he := (layout which).injective h
      cases he
    simp only [TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr,frame,
      words,Function.update_of_ne hn]

private theorem program_field (which : Fin 8) (l : Fin 21) :
    program (fieldLabel which l) = TM2ReturnLink.redirect (fieldLabel which) (next which)
      (fieldProgram which l) := by
  have h : (fieldLabel which l).val < 168 := by
    dsimp only [fieldLabel]
    have := which.isLt
    have := l.isLt
    omega
  have hd : (fieldLabel which l).val / 21 = which.val := by
    dsimp only [fieldLabel]
    omega
  have hm : (fieldLabel which l).val % 21 = l.val := by
    dsimp only [fieldLabel]
    omega
  simp only [program,dif_pos h,hd,hm]

/-- One actual field run preserves all old ports; its only live update is the
new encoded suffix. Workspace assumptions describe the actual reusable ports. -/
theorem field_run (which : Fin 8) (n : Nat) (old : Fin 43 → List Bool)
    (suffix : List Bool) (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : old (sourcePort which) = n.bits) :
    ∃ used ≤ NatFieldWriterMachine.clock n,
      tick^[used] (state (some (fieldLabel which 0)) old suffix) =
        state (some (next which)) old (NatFieldWriterMachine.encoded n suffix) := by
  have he := TM2StackFrame.run (layout which) NatFieldWriterMachine.program
    (NatFieldWriterMachine.clock n) (NatFieldWriterMachine.start n.bits suffix)
    (frame which old)
  change (TM2ReturnLink.tick (fieldProgram which))^[_] _ =
    TM2StackFrame.embed (layout which)
      (NatFieldWriterMachine.tick^[_] _) (frame which old) at he
  rw [NatFieldWriterMachine.padded_run] at he
  have hh : ((TM2ReturnLink.tick (fieldProgram which))^[NatFieldWriterMachine.clock n]
      (TM2StackFrame.embed (layout which) (NatFieldWriterMachine.start n.bits suffix)
        (frame which old))).l = none := by rw [he]; rfl
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run (fieldProgram which) program
    (fieldLabel which) (next which) (program_field which)
    (NatFieldWriterMachine.clock n) _ hh
  rw [he] at hr
  have hi : TM2ReturnLink.embed (fieldLabel which) (next which)
      (TM2StackFrame.embed (layout which) (NatFieldWriterMachine.start n.bits suffix)
        (frame which old)) = state (some (fieldLabel which 0)) old suffix := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact data_words which old suffix hw
  have ho : TM2ReturnLink.embed (fieldLabel which) (next which)
      (TM2StackFrame.embed (layout which)
        (NatFieldWriterMachine.result n.bits (NatFieldWriterMachine.encoded n suffix))
        (frame which old)) =
      state (some (next which)) old (NatFieldWriterMachine.encoded n suffix) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    rw [←hn]
    exact data_words which old (NatFieldWriterMachine.encoded n suffix) hw
  rw [hi,ho] at hr
  exact ⟨used,hu,hr⟩

#print axioms field_run
end ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Numeric record in the codec's forward order; fields execute in reverse. -/
def encoded (v : Fin 8 → Nat) : List Bool :=
  uniformNatEncode 8 ++ bitFramesEncode
    [uniformNatEncode (v 7),uniformNatEncode (v 6),uniformNatEncode (v 5),uniformNatEncode (v 4),
     uniformNatEncode (v 3),uniformNatEncode (v 2),uniformNatEncode (v 1),uniformNatEncode (v 0)]

private theorem start_eq (old : Fin 43 → List Bool) :
    start old = state (some 0) old [] := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem finish_step (old : Fin 43 → List Bool) (word : List Bool) :
    tick (state (some 168) old word) = result (uniformNatEncode 8 ++ word) old := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The fixed eight-field controller executes the complete original flat key
encoding, retaining all earlier words and clearing its reused workspace. -/
theorem run (p : Nat) (v : Fin 8 → Nat) (old : Fin 43 → List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hv : ∀ i, v i < p) :
    ∃ used ≤ clock p, tick^[used] (start old) = result (encoded v) old := by
  let w0 : List Bool := []
  let w1 := NatFieldWriterMachine.encoded (v 0) w0
  let w2 := NatFieldWriterMachine.encoded (v 1) w1
  let w3 := NatFieldWriterMachine.encoded (v 2) w2
  let w4 := NatFieldWriterMachine.encoded (v 3) w3
  let w5 := NatFieldWriterMachine.encoded (v 4) w4
  let w6 := NatFieldWriterMachine.encoded (v 5) w5
  let w7 := NatFieldWriterMachine.encoded (v 6) w6
  let w8 := NatFieldWriterMachine.encoded (v 7) w7
  obtain ⟨a,ha,ea⟩ := field_run 0 (v 0) old w0 hw (hn 0)
  have ba := ha.trans (NatFieldWriterMachine.clock_mono (show v 0 ≤ p-1 by have := hv 0; omega))
  change tick^[a] (state (some 0) old w0) = state (some 21) old w1 at ea
  obtain ⟨b,hb,eb⟩ := field_run 1 (v 1) old w1 hw (hn 1)
  have bb := hb.trans (NatFieldWriterMachine.clock_mono (show v 1 ≤ p-1 by have := hv 1; omega))
  change tick^[b] (state (some 21) old w1) = state (some 42) old w2 at eb
  obtain ⟨c,hc,ec⟩ := field_run 2 (v 2) old w2 hw (hn 2)
  have bc := hc.trans (NatFieldWriterMachine.clock_mono (show v 2 ≤ p-1 by have := hv 2; omega))
  change tick^[c] (state (some 42) old w2) = state (some 63) old w3 at ec
  obtain ⟨d,hd,ed⟩ := field_run 3 (v 3) old w3 hw (hn 3)
  have bd := hd.trans (NatFieldWriterMachine.clock_mono (show v 3 ≤ p-1 by have := hv 3; omega))
  change tick^[d] (state (some 63) old w3) = state (some 84) old w4 at ed
  obtain ⟨e,he,ee⟩ := field_run 4 (v 4) old w4 hw (hn 4)
  have be := he.trans (NatFieldWriterMachine.clock_mono (show v 4 ≤ p-1 by have := hv 4; omega))
  change tick^[e] (state (some 84) old w4) = state (some 105) old w5 at ee
  obtain ⟨f,hf,ef⟩ := field_run 5 (v 5) old w5 hw (hn 5)
  have bf := hf.trans (NatFieldWriterMachine.clock_mono (show v 5 ≤ p-1 by have := hv 5; omega))
  change tick^[f] (state (some 105) old w5) = state (some 126) old w6 at ef
  obtain ⟨g,hg,eg⟩ := field_run 6 (v 6) old w6 hw (hn 6)
  have bg := hg.trans (NatFieldWriterMachine.clock_mono (show v 6 ≤ p-1 by have := hv 6; omega))
  change tick^[g] (state (some 126) old w6) = state (some 147) old w7 at eg
  obtain ⟨h,hh,eh⟩ := field_run 7 (v 7) old w7 hw (hn 7)
  have bh := hh.trans (NatFieldWriterMachine.clock_mono (show v 7 ≤ p-1 by have := hv 7; omega))
  change tick^[h] (state (some 147) old w7) = state (some 168) old w8 at eh
  refine ⟨1+(h+(g+(f+(e+(d+(c+(b+a))))))),by unfold clock; omega,?_⟩
  rw [start_eq]
  change tick^[_] (state (some 0) old w0) = _
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick h,
    Function.iterate_add_apply tick g,Function.iterate_add_apply tick f,
    Function.iterate_add_apply tick e,Function.iterate_add_apply tick d,
    Function.iterate_add_apply tick c,Function.iterate_add_apply tick b,
    ea,eb,ec,ed,ee,ef,eg,eh,Function.iterate_one,finish_step]
  simp only [w8,w7,w6,w5,w4,w3,w2,w1,w0,NatFieldWriterMachine.encoded,
    encoded,bitFramesEncode,List.append_assoc]

/-- A fixed public-modulus clock pads only after the derived successful halt. -/
theorem padded_run (p : Nat) (v : Fin 8 → Nat) (old : Fin 43 → List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hv : ∀ i, v i < p) :
    tick^[clock p] (start old) = result (encoded v) old := by
  obtain ⟨u,hu,he⟩ := run p v old hw hn hv
  rw [show clock p = (clock p-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result (encoded v) old) = _ from rfl) _

theorem local_cost (l : Fin 169) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Actual instruction charge is bounded for the full concrete controller. -/
theorem charged (p : Nat) (v : Fin 8 → Nat) (old : Fin 43 → List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = [])
    (hn : ∀ i, old (sourcePort i) = (v i).bits)
    (hv : ∀ i, v i < p) :
    ∃ charge ≤ cost p,
      BitOracleMachine.run code (clock p) (start old) = pure (result (encoded v) old,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock p) (start old)
  rw [show (TM2ReturnLink.tick program)^[clock p] (start old) = result (encoded v) old
    from padded_run p v old hw hn hv] at he
  exact ⟨charge,hc,he⟩

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
