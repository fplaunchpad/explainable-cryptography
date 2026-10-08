import ExplainableCrypto.Helios.Computational.BitIncrementMachine
import ExplainableCrypto.Helios.Computational.RecordFieldStepMachine

/-! Write the original length framing from loaded payload bits. Length counting,
carry, payload restoration and prefix output are actual finite-control steps. -/
namespace ExplainableCrypto.Helios.Computational.FrameWriteMachine
open Turing.TM2
abbrev Stack := NatPrefixMachine.Stack ⊕ Unit
abbrev input : Stack := .inl .input
abbrev carry : Stack := .inl .count
abbrev buffer : Stack := .inl .scratch
abbrev output : Stack := .inl .output
abbrev counter : Stack := .inr ()

def incrementLayout : NatPrefixMachine.Stack ⊕ Unit ≃ Stack :=
  (Equiv.swap carry buffer).trans (Equiv.swap output counter)

inductive Label where
  | increment (b : Bool) | resume | collect | restore | digits | putbits | width
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨collect⟩
instance : Fintype Label where
  elems := {increment false,increment true,resume,collect,restore,digits,putbits,width}
  complete l := by cases l with
    | increment b => cases b <;> simp
    | _ => simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | increment b => TM2ReturnLink.redirect increment resume
      (TM2StackFrame.relocate incrementLayout (BitIncrementMachine.program b))
  | resume => .goto (fun _ => collect)
  | collect => .pop input (fun _ b => b) <| .branch Option.isSome
      (.push buffer (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => increment false))))
      (.goto (fun _ => restore))
  | restore => .pop buffer (fun _ b => b) <| .branch Option.isSome
      (.push output (fun b => b.getD false) (.goto (fun _ => restore))) (.goto (fun _ => digits))
  | digits => .pop counter (fun _ b => b) <| .branch Option.isSome
      (.push buffer (fun b => b.getD false) (.push carry (fun _ => true) (.goto (fun _ => digits))))
      (.goto (fun _ => putbits))
  | putbits => .pop buffer (fun _ b => b) <| .branch Option.isSome
      (.push output (fun b => b.getD false) (.goto (fun _ => putbits)))
      (.push output (fun _ => false) (.goto (fun _ => width)))
  | width => .pop carry (fun _ b => b) <| .branch Option.isSome
      (.push output (fun _ => true) (.goto (fun _ => width))) (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (source marks rev word count : List Bool) (v : Option Bool) : Config :=
  ⟨phase,v,fun
    | .inl .input => source | .inl .count => marks | .inl .scratch => rev
    | .inl .output => word | .inr _ => count⟩
def start (payload suffix : List Bool) : Config := state (some collect) payload [] [] suffix [] none

def readout (c : Config) : Option (List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk output) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l <;> simp [program,redirect_supports,SupportsStmt]

private theorem width_run (marks word : List Bool) (v : Option Bool) :
    tick^[marks.length+1] (state (some width) [] marks [] word [] v) =
      state none [] [] [] (List.replicate marks.length true++word) [] (some true) := by
  induction marks generalizing word v with
  | nil => simp [tick,state,program,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some width) [] (b::bs) [] word [] v) =
        state (some width) [] bs [] (true::word) [] (some b) := by
      simp [tick,state,program,stepAux]
      funext k
      rcases k with (k|⟨⟩)
      · cases k <;> simp
      · simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp [List.replicate_succ',List.append_assoc]

private theorem putbits_run (bits marks word : List Bool) (v : Option Bool) :
    tick^[bits.length+1] (state (some putbits) [] marks bits word [] v) =
      state (some width) [] marks [] (false::(bits.reverse++word)) [] none := by
  induction bits generalizing word v with
  | nil =>
    simp [tick,state,program,stepAux]
    funext k
    rcases k with (k|⟨⟩)
    · cases k <;> simp
    · simp
  | cons b bs ih =>
    have hs : tick (state (some putbits) [] marks (b::bs) word [] v) =
        state (some putbits) [] marks bs (b::word) [] (some b) := by
      simp [tick,state,program,stepAux]
      funext k
      rcases k with (k|⟨⟩)
      · cases k <;> simp
      · simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

private theorem digits_run (bits marks rev word : List Bool) (v : Option Bool) :
    tick^[bits.length+1] (state (some digits) [] marks rev word bits v) =
      state (some putbits) [] (List.replicate bits.length true++marks)
        (bits.reverse++rev) word [] none := by
  induction bits generalizing marks rev v with
  | nil => simp [tick,state,program,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some digits) [] marks rev word (b::bs) v) =
        state (some digits) [] (true::marks) (b::rev) word bs (some b) := by
      simp [tick,state,program,stepAux]
      funext k
      rcases k with (k|⟨⟩)
      · cases k <;> simp
      · simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp [List.replicate_succ',List.append_assoc]

/-- Write the exact original natural prefix from its canonical binary digits.
This is also the entry point needed to replace a cache's outer count. -/
theorem prefix_run (n : Nat) (suffix : List Bool) (v : Option Bool) :
    tick^[3*n.size+3] (state (some digits) [] [] [] suffix n.bits v) =
      state none [] [] [] (uniformNatEncode n++suffix) [] (some true) := by
  have hd := digits_run n.bits [] [] suffix v
  simp only [List.append_nil] at hd
  have hp := putbits_run n.bits.reverse (List.replicate n.bits.length true) suffix none
  simp only [List.length_reverse,List.reverse_reverse] at hp
  have hw := width_run (List.replicate n.bits.length true) (false::(n.bits++suffix)) none
  simp only [List.length_replicate] at hw
  have hn : 3*n.size+3 = (n.bits.length+1)+((n.bits.length+1)+(n.bits.length+1)) := by
    rw [Nat.size_eq_bits_len]; omega
  rw [hn,Function.iterate_add_apply tick (n.bits.length+1),
    Function.iterate_add_apply tick (n.bits.length+1),hd,hp,hw]
  simp [uniformNatEncode,List.append_assoc]

private theorem restore_run (rev word count : List Bool) (v : Option Bool) :
    tick^[rev.length+1] (state (some restore) [] [] rev word count v) =
      state (some digits) [] [] [] (rev.reverse++word) count none := by
  induction rev generalizing word v with
  | nil => simp [tick,state,program,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some restore) [] [] (b::bs) word count v) =
        state (some restore) [] [] bs (b::word) count (some b) := by
      simp [tick,state,program,stepAux]
      funext k
      rcases k with (k|⟨⟩)
      · cases k <;> simp
      · simp
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,hs,ih]
    simp

private theorem increment_run (n : Nat) (source rev word : List Bool) (v : Option Bool) :
    ∃ fuel ≤ 2*n.size+2,
      tick^[fuel] (state (some (increment false)) source [] rev word n.bits v) =
        state (some resume) source [] rev word (n+1).bits (some true) := by
  obtain ⟨j,hj,hr⟩ := BitIncrementMachine.run n source rev v
  have he := TM2StackFrame.run incrementLayout BitIncrementMachine.program j
    (BitIncrementMachine.config (some false) n.bits [] source rev v) (fun _ => word)
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate incrementLayout (BitIncrementMachine.program l)))^[j] _ =
    TM2StackFrame.embed incrementLayout (BitIncrementMachine.tick^[j] _) _ at he
  rw [hr] at he
  have hh : ((TM2ReturnLink.tick (fun l => TM2StackFrame.relocate incrementLayout (BitIncrementMachine.program l)))^[j]
      (TM2StackFrame.embed incrementLayout (BitIncrementMachine.config (some false) n.bits [] source rev v)
        (fun _ => word))).l = none := by rw [he]; rfl
  obtain ⟨u,hu,ht⟩ := TM2ReturnLink.run (fun l => TM2StackFrame.relocate incrementLayout (BitIncrementMachine.program l))
    program increment resume (fun _ => rfl) _ _ hh
  rw [he] at ht
  have hs : TM2ReturnLink.embed increment resume (TM2StackFrame.embed incrementLayout
      (BitIncrementMachine.config (some false) n.bits [] source rev v) (fun _ => word)) =
      state (some (increment false)) source [] rev word n.bits v := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with (k|⟨⟩)
    · cases k <;> rfl
    · rfl
  rw [hs] at ht
  refine ⟨u,hu.trans hj,ht.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with (k|⟨⟩)
  · cases k <;> rfl
  · rfl

private theorem collect_run (n : Nat) (payload rev word : List Bool) (v : Option Bool) :
    ∃ fuel ≤ payload.length*(2*(n+payload.length).size+4)+1,
      tick^[fuel] (state (some collect) payload [] rev word n.bits v) =
        state (some restore) [] [] (payload.reverse++rev) word (n+payload.length).bits none := by
  induction payload generalizing n rev v with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simp [tick,state,program,stepAux]
  | cons b bs ih =>
    have hs : tick (state (some collect) (b::bs) [] rev word n.bits v) =
        state (some (increment false)) bs [] (b::rev) word n.bits none := by
      simp [tick,state,program,stepAux]
      funext k
      rcases k with (k|⟨⟩)
      · cases k <;> simp
      · simp
    obtain ⟨i,hi,hr⟩ := increment_run n bs (b::rev) word none
    obtain ⟨j,hj,he⟩ := ih (n+1) (b::rev) (some true)
    have hn : n+1+bs.length = n+(bs.length+1) := by omega
    rw [hn] at hj he
    have hsize := Nat.size_le_size (show n ≤ n+(bs.length+1) by omega)
    have enter : tick (state (some resume) bs [] (b::rev) word (n+1).bits (some true)) =
        state (some collect) bs [] (b::rev) word (n+1).bits (some true) := rfl
    refine ⟨j+(1+(i+1)),?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Function.iterate_add_apply tick j,Function.iterate_add_apply tick 1,
        Function.iterate_one,Function.iterate_succ_apply tick i,hs,hr,enter,he]
      simp

def cost (n : Nat) : Nat := n*(2*n.size+5)+3*n.size+5

theorem cost_mono {n m : Nat} (h : n ≤ m) : cost n ≤ cost m := by
  have hs := Nat.size_le_size h
  have hm := Nat.mul_le_mul h (show 2*n.size+5 ≤ 2*m.size+5 by omega)
  unfold cost
  omega

/-- Compute and write the original complete field frame on an arbitrary suffix.
The returned configuration has every work stack empty, not just equal readout. -/
theorem run (payload suffix : List Bool) :
    ∃ fuel ≤ cost payload.length,
      tick^[fuel] (start payload suffix) =
        state none [] [] [] (uniformNatEncode payload.length++(payload++suffix)) [] (some true) := by
  obtain ⟨i,hi,hr⟩ := collect_run 0 payload [] suffix none
  simp only [Nat.zero_add,List.append_nil] at hi hr
  have he := restore_run payload.reverse suffix payload.length.bits none
  simp only [List.length_reverse,List.reverse_reverse] at he
  refine ⟨(3*payload.length.size+3)+((payload.length+1)+i),?_,?_⟩
  · unfold cost
    have hm : payload.length*(2*payload.length.size+5) =
        payload.length*(2*payload.length.size+4)+payload.length := by ring
    omega
  · change tick^[_] (state (some collect) payload [] [] suffix (0 : Nat).bits none) = _
    rw [Function.iterate_add_apply tick (3*payload.length.size+3),Function.iterate_add_apply tick (payload.length+1),
      hr,he,prefix_run]

/-- Existing full-key bit bounds discharge the writer's operand-size bound. -/
theorem key_field_run {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q)) (suffix : List Bool) :
    ∃ fuel ≤ cost (keyRecordBitBound p),
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) suffix) =
        state none [] [] [] (uniformNatEncode (((ballotKeyBitCodec p q).encode key).length)++
          (((ballotKeyBitCodec p q).encode key)++suffix)) [] (some true) := by
  obtain ⟨fuel,hf,hr⟩ := run ((ballotKeyBitCodec p q).encode key) suffix
  exact ⟨fuel,hf.trans (cost_mono (ballotKeyBits_length_le key)),hr⟩

/-- The answer field uses the original scalar encoding, including its own
canonical scalar framing. No numeric-value conversion is a writer operation. -/
theorem scalar_field_run {q : Nat} [NeZero q] (answer : ZMod q) (suffix : List Bool) :
    ∃ fuel ≤ cost (groupRecordBitBound q),
      tick^[fuel] (start ((primeScalarBitCodec q).encode answer) suffix) =
        state none [] [] [] (uniformNatEncode (((primeScalarBitCodec q).encode answer).length)++
          (((primeScalarBitCodec q).encode answer)++suffix)) [] (some true) := by
  obtain ⟨fuel,hf,hr⟩ := run ((primeScalarBitCodec q).encode answer) suffix
  have h : ((primeScalarBitCodec q).encode answer).length ≤ groupRecordBitBound q := scalarEncode_length_le answer
  exact ⟨fuel,hf.trans (cost_mono h),hr⟩

/-- Write the original scalar encoding from its loaded canonical binary digits.
Loading/conversion to those digits is outside this prefix operation. -/
theorem scalar_prefix_run {q : Nat} [NeZero q] (a : ZMod q) (suffix : List Bool) :
    ∃ fuel ≤ 3*(q-1).size+3,
      tick^[fuel] (state (some .digits) [] [] [] suffix a.val.bits none) =
        state none [] [] [] (scalarEncode a++suffix) [] (some true) := by
  have hn : a.val ≤ q-1 := Nat.le_sub_one_of_lt a.val_lt
  have hs := Nat.size_le_size hn
  exact ⟨3*a.val.size+3,by omega,prefix_run a.val suffix none⟩

/-- Scalar six modulo eleven uses the literal little-endian prefix 1110011. -/
theorem scalar_prefix_control :
    tick^[12] (state (some .digits) [] [] [] [false,true] [false,true,true] none) =
      state none [] [] [] [true,true,true,false,false,true,true,false,true] [] (some true) := by
  exact prefix_run 6 [false,true] none

/-- Scalar zero has an explicit delimiter even though its digit stack is empty. -/
theorem scalar_zero_control :
    tick^[3] (state (some .digits) [] [] [] [true,false] [] none) =
      state none [] [] [] [false,true,false] [] (some true) := by
  exact prefix_run 0 [true,false] none

theorem field_control :
    ∃ fuel ≤ 38, tick^[fuel] (start [true,false,false] [false,true]) =
      state none [] [] [] [true,true,false,true,true,true,false,false,false,true] [] (some true) := by
  exact run [true,false,false] [false,true]

theorem boundary_control :
    ∃ fuel ≤ 58, tick^[fuel] (start [true,true,false,true] [false]) =
      state none [] [] [] [true,true,true,false,false,false,true,true,true,false,true,false] [] (some true) := by
  exact run [true,true,false,true] [false]

theorem empty_control :
    ∃ fuel ≤ 5, tick^[fuel] (start [] [true,false]) =
      state none [] [] [] [false,true,false] [] (some true) := by
  exact run [] [true,false]

theorem prefix_control :
    tick^[15] (state (some digits) [] [] [] [true,false] [false,false,false,true] (some false)) =
      state none [] [] [] [true,true,true,true,false,false,false,false,true,true,false] [] (some true) := by
  exact prefix_run 8 [true,false] (some false)

/-- Zero length still emits a delimiter and reaches an actual successful halt. -/
theorem empty_not_omitted :
    ∃ fuel ≤ 5,
      let c := tick^[fuel] (start [] [])
      c.l = none ∧ readout c = some [false] ∧ readout c ≠ some [] := by
  obtain ⟨fuel,hf,hr⟩ := run [] []
  refine ⟨fuel,hf,?_⟩
  dsimp only
  rw [hr]
  exact ⟨rfl,rfl,by decide⟩

#print axioms cost_mono
#print axioms supports
#print axioms prefix_run
#print axioms run
#print axioms key_field_run
#print axioms scalar_field_run
#print axioms scalar_prefix_run
#print axioms scalar_prefix_control
#print axioms scalar_zero_control
#print axioms field_control
#print axioms boundary_control
#print axioms empty_control
#print axioms prefix_control
#print axioms empty_not_omitted
end ExplainableCrypto.Helios.Computational.FrameWriteMachine
