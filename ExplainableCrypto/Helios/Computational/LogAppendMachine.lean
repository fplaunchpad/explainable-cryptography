import ExplainableCrypto.Helios.Computational.FrameWriteMachine
import ExplainableCrypto.Helios.Computational.BitCopyMachine
import ExplainableCrypto.Helios.Computational.BallotStateBitSize
import ExplainableCrypto.Helios.Computational.BallotCacheCodecControls

/-! Chronological append in the original counted key-log encoding. -/
namespace ExplainableCrypto.Helios.Computational.LogAppendMachine
open Turing.TM2
inductive Stack where
  | src | carry | scratch | out | count | temp | key | body
  deriving DecidableEq
open Stack
inductive Extra where
  | count | key | body
  deriving DecidableEq

def writerLayout : FrameWriteMachine.Stack ⊕ Extra ≃ Stack where
  toFun
    | .inl (.inl .input) => src | .inl (.inl .count) => carry
    | .inl (.inl .scratch) => scratch | .inl (.inl .output) => out
    | .inl (.inr _) => temp
    | .inr .count => count | .inr .key => key | .inr .body => body
  invFun
    | .src => .inl (.inl .input) | .carry => .inl (.inl .count)
    | .scratch => .inl (.inl .scratch) | .out => .inl (.inl .output)
    | .temp => .inl (.inr ())
    | .count => .inr .count | .key => .inr .key | .body => .inr .body
  left_inv x := by
    rcases x with ((k|⟨⟩)|e)
    · cases k <;> rfl
    · rfl
    · cases e <;> rfl
  right_inv x := by cases x <;> rfl

def parseLayout : NatPrefixMachine.Stack ⊕ (Unit ⊕ Extra) ≃ Stack :=
  ((Equiv.sumAssoc NatPrefixMachine.Stack Unit Extra).symm.trans writerLayout).trans
    ((Equiv.swap src body).trans (Equiv.swap out count))
def finalLayout := writerLayout.trans (Equiv.swap temp count)

inductive CopyExtra where
  | carry | out | count | temp | body
  deriving DecidableEq

def copyLayout : BitCopyMachine.Stack ⊕ CopyExtra ≃ Stack where
  toFun
    | .inl .source => key | .inl .destination => src | .inl .scratch => scratch
    | .inr .carry => carry | .inr .out => out | .inr .count => count
    | .inr .temp => temp | .inr .body => body
  invFun
    | .key => .inl .source | .src => .inl .destination | .scratch => .inl .scratch
    | .carry => .inr .carry | .out => .inr .out | .count => .inr .count
    | .temp => .inr .temp | .body => .inr .body
  left_inv x := by rcases x with (k|e); cases k <;> rfl; cases e <;> rfl
  right_inv x := by cases x <;> rfl

inductive Label where
  | parse (l : NatPrefixMachine.Label) | increment (b : Bool) | copy (b : Bool)
  | write (l : FrameWriteMachine.Label) | finish (l : FrameWriteMachine.Label)
  | parseDone | incDone | copyDone | writeDone | reverse | restore | done
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨parse default⟩
instance : Fintype Label where
  elems := Finset.univ.image parse ∪ Finset.univ.image increment ∪ Finset.univ.image copy ∪
    Finset.univ.image write ∪ Finset.univ.image finish ∪
    {parseDone,incDone,copyDone,writeDone,reverse,restore,done}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | parse l => TM2ReturnLink.redirect parse parseDone (TM2StackFrame.relocate parseLayout (NatPrefixMachine.program l))
  | increment b => TM2ReturnLink.redirect increment incDone (TM2StackFrame.relocate parseLayout (BitIncrementMachine.program b))
  | copy b => TM2ReturnLink.redirect copy copyDone (TM2StackFrame.relocate copyLayout (BitCopyMachine.program b))
  | write l => TM2ReturnLink.redirect write writeDone (TM2StackFrame.relocate writerLayout (FrameWriteMachine.program l))
  | finish l => TM2ReturnLink.redirect finish done (TM2StackFrame.relocate finalLayout (FrameWriteMachine.program l))
  | parseDone => .branch (fun v => decide (v = some true))
      (.load (fun _ => none) (.goto (fun _ => increment false))) (.load (fun _ => none) .halt)
  | incDone => .load (fun _ => none) (.goto (fun _ => copy false))
  | copyDone => .goto (fun _ => write default)
  | writeDone => .goto (fun _ => reverse)
  | reverse => .pop body (fun _ b => b) <| .branch Option.isSome
      (.push src (fun b => b.getD false) (.goto (fun _ => reverse))) (.goto (fun _ => restore))
  | restore => .pop src (fun _ b => b) <| .branch Option.isSome
      (.push out (fun b => b.getD false) (.goto (fun _ => restore)))
      (.load (fun _ => none) (.goto (fun _ => finish .digits)))
  | done => .load (fun _ => some true) .halt

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (x c t w n a k b : List Bool) (v : Option Bool) : Config :=
  ⟨phase,v,fun
    | .src => x | .carry => c | .scratch => t | .out => w
    | .count => n | .temp => a | .key => k | .body => b⟩
def start (k log : List Bool) : Config := state (some (parse default)) [] [] [] [] [] [] k log none

def readout (c : Config) : Option (List Bool) :=
  if c.l = none ∧ c.var = some true then some (c.stk out) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _; cases l <;> simp [program,redirect_supports,SupportsStmt]

private theorem call_run {K E L : Type} [DecidableEq K]
    (layout : K ⊕ E ≃ Stack) (p : L → Stmt (fun _ : K => Bool) L (Option Bool))
    (f : L → Label) (ret : Label)
    (hp : ∀ l, program (f l) = TM2ReturnLink.redirect f ret (TM2StackFrame.relocate layout (p l)))
    (fuel : Nat) (c : Cfg (fun _ : K => Bool) L (Option Bool)) (frame : E → List Bool)
    (hh : ((TM2ReturnLink.tick p)^[fuel] c).l = none) :
    ∃ used ≤ fuel, tick^[used] (TM2ReturnLink.embed f ret (TM2StackFrame.embed layout c frame)) =
      TM2ReturnLink.embed f ret (TM2StackFrame.embed layout ((TM2ReturnLink.tick p)^[fuel] c) frame) := by
  have he := TM2StackFrame.run layout p fuel c frame
  have hl : ((TM2ReturnLink.tick (fun l => TM2StackFrame.relocate layout (p l)))^[fuel]
      (TM2StackFrame.embed layout c frame)).l = none := by
    rw [he]; exact hh
  obtain ⟨used,hu,hr⟩ := TM2ReturnLink.run (fun l => TM2StackFrame.relocate layout (p l)) program f ret hp _ _ hl
  rw [he] at hr
  exact ⟨used,hu,hr⟩

def parserFrame (k : List Bool) : Unit ⊕ Extra → List Bool
  | .inr .key => k | _ => []
def writerFrame (k b n : List Bool) : Extra → List Bool
  | .key => k | .body => b | .count => n
def copyFrame (b n : List Bool) : CopyExtra → List Bool
  | .body => b | .count => n | _ => []

private theorem parse_run (n : Nat) (k b : List Bool) :
    ∃ fuel ≤ 3*n.size+3,
      tick^[fuel] (state (some (parse default)) [] [] [] [] [] [] k (uniformNatEncode n++b) none) =
        state (some parseDone) [] [] [] [] n.bits [] k b (some true) := by
  have hr := NatPrefixMachine.encoded_run n b
  have hh : (NatPrefixMachine.tick^[3*n.size+3] (NatPrefixMachine.start (uniformNatEncode n++b))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run parseLayout NatPrefixMachine.program parse parseDone
    (fun _ => rfl) (3*n.size+3) (NatPrefixMachine.start (uniformNatEncode n++b)) (parserFrame k) hh
  change tick^[u] _ = TM2ReturnLink.embed parse parseDone
    (TM2StackFrame.embed parseLayout (NatPrefixMachine.tick^[3*n.size+3] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed parse parseDone
      (TM2StackFrame.embed parseLayout (NatPrefixMachine.start (uniformNatEncode n++b)) (parserFrame k)) =
      state (some (parse default)) [] [] [] [] [] [] k (uniformNatEncode n++b) none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; cases k <;> rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; cases k <;> rfl

private theorem increment_run (n : Nat) (k b : List Bool) :
    ∃ fuel ≤ 2*n.size+2,
      tick^[fuel] (state (some (increment false)) [] [] [] [] n.bits [] k b none) =
        state (some incDone) [] [] [] [] (n+1).bits [] k b (some true) := by
  obtain ⟨j,hj,hr⟩ := BitIncrementMachine.run n b [] none
  have hh : (BitIncrementMachine.tick^[j] (BitIncrementMachine.config (some false) n.bits [] b [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run parseLayout BitIncrementMachine.program increment incDone
    (fun _ => rfl) (j) (BitIncrementMachine.config (some false) n.bits [] b [] none) (parserFrame k) hh
  change tick^[u] _ = TM2ReturnLink.embed increment incDone
    (TM2StackFrame.embed parseLayout (BitIncrementMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed increment incDone
      (TM2StackFrame.embed parseLayout (BitIncrementMachine.config (some false) n.bits [] b [] none) (parserFrame k)) =
      state (some (increment false)) [] [] [] [] n.bits [] k b none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; cases k <;> rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; cases k <;> rfl

private theorem copy_run (k b n : List Bool) :
    ∃ fuel ≤ 2*k.length+2,
      tick^[fuel] (state (some (copy false)) [] [] [] [] n [] k b none) =
        state (some copyDone) k [] [] [] n [] k b none := by
  have hr := BitCopyMachine.run k [] none
  simp only [List.append_nil] at hr
  have hh : (BitCopyMachine.tick^[2*k.length+2] (BitCopyMachine.config (some false) k [] [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run copyLayout BitCopyMachine.program copy copyDone
    (fun _ => rfl) (2*k.length+2) (BitCopyMachine.config (some false) k [] [] none) (copyFrame b n) hh
  change tick^[u] _ = TM2ReturnLink.embed copy copyDone
    (TM2StackFrame.embed copyLayout (BitCopyMachine.tick^[2*k.length+2] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed copy copyDone
      (TM2StackFrame.embed copyLayout (BitCopyMachine.config (some false) k [] [] none) (copyFrame b n)) =
      state (some (copy false)) [] [] [] [] n [] k b none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; cases k <;> rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; cases k <;> rfl

private theorem write_run (k b n : List Bool) :
    ∃ fuel ≤ FrameWriteMachine.cost k.length,
      tick^[fuel] (state (some (write default)) k [] [] [] n [] k b none) =
        state (some writeDone) [] [] [] (uniformNatEncode k.length++k) n [] k b (some true) := by
  obtain ⟨j,hj,hr⟩ := FrameWriteMachine.run k []
  simp only [List.append_nil] at hr
  have hh : (FrameWriteMachine.tick^[j] (FrameWriteMachine.start k [])).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run writerLayout FrameWriteMachine.program write writeDone
    (fun _ => rfl) (j) (FrameWriteMachine.start k []) (writerFrame k b n) hh
  change tick^[u] _ = TM2ReturnLink.embed write writeDone
    (TM2StackFrame.embed writerLayout (FrameWriteMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed write writeDone
      (TM2StackFrame.embed writerLayout (FrameWriteMachine.start k []) (writerFrame k b n)) =
      state (some (write default)) k [] [] [] n [] k b none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; cases k <;> rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; cases k <;> rfl

private theorem finish_run (n : Nat) (k w : List Bool) :
    ∃ fuel ≤ 3*n.size+3,
      tick^[fuel] (state (some (finish .digits)) [] [] [] w n.bits [] k [] none) =
        state (some done) [] [] [] (uniformNatEncode n++w) [] [] k [] (some true) := by
  have hr := FrameWriteMachine.prefix_run n w none
  have hh : (FrameWriteMachine.tick^[3*n.size+3] (FrameWriteMachine.state (some .digits) [] [] [] w n.bits none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run finalLayout FrameWriteMachine.program finish done
    (fun _ => rfl) (3*n.size+3) (FrameWriteMachine.state (some .digits) [] [] [] w n.bits none) (writerFrame k [] []) hh
  change tick^[u] _ = TM2ReturnLink.embed finish done
    (TM2StackFrame.embed finalLayout (FrameWriteMachine.tick^[3*n.size+3] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed finish done
      (TM2StackFrame.embed finalLayout (FrameWriteMachine.state (some .digits) [] [] [] w n.bits none) (writerFrame k [] [])) =
      state (some (finish .digits)) [] [] [] w n.bits [] k [] none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; cases k <;> rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; cases k <;> rfl


private theorem reverse_run (b rev w n k : List Bool) (v : Option Bool) :
    tick^[b.length+1] (state (some reverse) rev [] [] w n [] k b v) =
      state (some restore) (b.reverse++rev) [] [] w n [] k [] none := by
  induction b generalizing rev v with
  | nil =>
    simp [tick,state,program,stepAux]
  | cons x xs ih =>
    have hs : tick (state (some reverse) rev [] [] w n [] k (x::xs) v) =
        state (some reverse) (x::rev) [] [] w n [] k xs (some x) := by
      simp [tick,state,program,stepAux]
      funext t; cases t <;> simp
    rw [List.length_cons,Function.iterate_succ_apply,hs,ih]
    simp [List.reverse_cons,List.append_assoc]

private theorem restore_run (xs w n k : List Bool) (v : Option Bool) :
    tick^[xs.length+1] (state (some restore) xs [] [] w n [] k [] v) =
      state (some (finish .digits)) [] [] [] (xs.reverse++w) n [] k [] none := by
  induction xs generalizing w v with
  | nil =>
    simp [tick,state,program,stepAux]
  | cons x xs ih =>
    have hs : tick (state (some restore) (x::xs) [] [] w n [] k [] v) =
        state (some restore) xs [] [] (x::w) n [] k [] (some x) := by
      simp [tick,state,program,stepAux]
      funext t; cases t <;> simp
    rw [List.length_cons,Function.iterate_succ_apply,hs,ih]
    simp [List.reverse_cons,List.append_assoc]

private theorem move_run (b w n k : List Bool) (v : Option Bool) :
    tick^[2*b.length+2] (state (some reverse) [] [] [] w n [] k b v) =
      state (some (finish .digits)) [] [] [] (b++w) n [] k [] none := by
  have h := reverse_run b [] w n k v
  simp only [List.append_nil] at h
  rw [show 2*b.length+2 = (b.length+1)+(b.length+1) by omega,Function.iterate_add_apply,h]
  have r := restore_run b.reverse w n k none
  simpa only [List.length_reverse,List.reverse_reverse] using r

def cost (N K B : Nat) : Nat :=
  5*N.size+3*(N+1).size+2*K+FrameWriteMachine.cost K+2*B+17

private theorem build_run (n : Nat) (k b : List Bool) :
    ∃ fuel ≤ cost n k.length b.length,
      tick^[fuel] (start k (uniformNatEncode n++b)) =
        state none [] [] [] (uniformNatEncode (n+1)++(b++(uniformNatEncode k.length++k)))
          [] [] k [] (some true) := by
  obtain ⟨i,hi,hr⟩ := parse_run n k b
  obtain ⟨j,hj,hjrun⟩ := increment_run n k b
  obtain ⟨l,hl,hlrun⟩ := copy_run k b (n+1).bits
  obtain ⟨m,hm,hmrun⟩ := write_run k b (n+1).bits
  have move := move_run b (uniformNatEncode k.length++k) (n+1).bits k (some true)
  obtain ⟨z,hz,hzrun⟩ := finish_run (n+1) k (b++(uniformNatEncode k.length++k))
  have enterInc : tick (state (some parseDone) [] [] [] [] n.bits [] k b (some true)) =
      state (some (increment false)) [] [] [] [] n.bits [] k b none := rfl
  have enterCopy : tick (state (some incDone) [] [] [] [] (n+1).bits [] k b (some true)) =
      state (some (copy false)) [] [] [] [] (n+1).bits [] k b none := rfl
  have enterWrite : tick (state (some copyDone) k [] [] [] (n+1).bits [] k b none) =
      state (some (write default)) k [] [] [] (n+1).bits [] k b none := rfl
  have enterMove : tick (state (some writeDone) [] [] [] (uniformNatEncode k.length++k) (n+1).bits [] k b (some true)) =
      state (some reverse) [] [] [] (uniformNatEncode k.length++k) (n+1).bits [] k b (some true) := rfl
  have haltStep : tick (state (some done) [] [] [] (uniformNatEncode (n+1)++(b++(uniformNatEncode k.length++k)))
      [] [] k [] (some true)) =
      state none [] [] [] (uniformNatEncode (n+1)++(b++(uniformNatEncode k.length++k)))
        [] [] k [] (some true) := rfl
  refine ⟨1+(z+((2*b.length+2)+(1+(m+(1+(l+(1+(j+(1+i))))))))),by unfold cost; omega,?_⟩
  change tick^[_] (state (some (parse default)) [] [] [] [] [] [] k (uniformNatEncode n++b) none) = _
  rw [Function.iterate_add_apply tick 1,Function.iterate_add_apply tick z,
    Function.iterate_add_apply tick (2*b.length+2),Function.iterate_add_apply tick 1,
    Function.iterate_add_apply tick m,Function.iterate_add_apply tick 1,
    Function.iterate_add_apply tick l,Function.iterate_add_apply tick 1,
    Function.iterate_add_apply tick j,Function.iterate_add_apply tick 1,
    hr,Function.iterate_one,enterInc,hjrun,enterCopy,hlrun,enterWrite,hmrun,enterMove,move,hzrun,haltStep]

private theorem frames_append (ws : List (List Bool)) (k : List Bool) :
    bitFramesEncode (ws++[k]) = bitFramesEncode ws++(uniformNatEncode k.length++k) := by
  induction ws with
  | nil => simp [bitFramesEncode]
  | cons w ws ih => simp [bitFramesEncode,ih,List.append_assoc]

/-- Exact chronological append with retained key and completely cleared workspace. -/
theorem run (ws : List (List Bool)) (k : List Bool) :
    ∃ fuel ≤ cost ws.length k.length (bitFramesEncode ws).length,
      tick^[fuel] (start k (bitFieldsEncode ws)) =
        state none [] [] [] (bitFieldsEncode (ws++[k])) [] [] k [] (some true) := by
  obtain ⟨fuel,hf,hr⟩ := build_run ws.length k (bitFramesEncode ws)
  refine ⟨fuel,hf,?_⟩
  simpa only [bitFieldsEncode,List.length_append,List.length_singleton,frames_append] using hr

/-- Monotonicity needed to derive the executable bound from loaded word sizes. -/
theorem cost_mono {N N' K K' B B' : Nat} (hn : N ≤ N') (hk : K ≤ K') (hb : B ≤ B') :
    cost N K B ≤ cost N' K' B' := by
  have hs := Nat.size_le_size hn
  have ht := Nat.size_le_size (Nat.add_le_add_right hn 1)
  have hj := FrameWriteMachine.cost_mono hk
  unfold cost
  omega

/-- Original typed log codec, including count and chronological field order. -/
theorem log_run {p q : Nat} [NeZero p] [NeZero q]
    (log : List (Unit × BallotForkPoint (PrimeGroup p q)))
    (k : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ cost log.length (keyRecordBitBound p) (((ballotLogEntryBitCodec p q).list).encode log).length,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode k) (((ballotLogEntryBitCodec p q).list).encode log)) =
        state none [] [] [] (((ballotLogEntryBitCodec p q).list).encode (log++[((),k)]))
          [] [] ((ballotKeyBitCodec p q).encode k) [] (some true) := by
  obtain ⟨fuel,hf,hr⟩ := run (log.map (ballotLogEntryBitCodec p q).encode) ((ballotKeyBitCodec p q).encode k)
  have hb : (bitFramesEncode (log.map (ballotLogEntryBitCodec p q).encode)).length ≤
      (((ballotLogEntryBitCodec p q).list).encode log).length := by
    change _ ≤ (uniformNatEncode _++bitFramesEncode _).length
    simp only [List.length_append]; omega
  simp only [List.length_map] at hf
  refine ⟨fuel,hf.trans (cost_mono (le_refl _) (ballotKeyBits_length_le k) hb),?_⟩
  have he : (((ballotLogEntryBitCodec p q).list).encode (log++[((),k)])) =
      bitFieldsEncode ((log.map (ballotLogEntryBitCodec p q).encode)++[(ballotKeyBitCodec p q).encode k]) := by
    change bitFieldsEncode ((log++[((),k)]).map (ballotLogEntryBitCodec p q).encode) = _
    rw [List.map_append]; rfl
  rw [he]
  exact hr

open OracleComp OracleSpec in
/-- Supported repaired-source logs derive their bounds from the hash budget. -/
theorem source_log_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (result : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (hs : result ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[])))
    (k : BallotForkPoint (PrimeGroup p q)) :
    ∃ fuel ≤ cost (n+15) (keyRecordBitBound p) (bitListSize (keyRecordBitBound p) (n+15)),
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode k) (((ballotLogEntryBitCodec p q).list).encode result.2.2)) =
        state none [] [] [] (((ballotLogEntryBitCodec p q).list).encode (result.2.2++[((),k)]))
          [] [] ((ballotKeyBitCodec p q).encode k) [] (some true) := by
  obtain ⟨fuel,hf,hr⟩ := log_run result.2.2 k
  have hn := runBallotFiniteLogged_log_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) result hs
  simp only [List.length_nil,Nat.zero_add] at hn
  have hw := BitRecordCodec.list_length_le (ballotLogEntryBitCodec p q) result.2.2
    (keyRecordBitBound p) (n+15) (fun e _ => ballotKeyBits_length_le e.2) hn
  exact ⟨fuel,hf.trans (cost_mono hn (le_refl _) hw),hr⟩

open BallotCacheCodecControls in
/-- Literal chronological order includes repeated keys without erasing history. -/
theorem order_control :
    ∃ fuel ≤ cost 2 (keyRecordBitBound 23)
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)]).length,
      tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode otherKey)
        (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)])) =
        state none [] [] [] (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key),((),otherKey)])
          [] [] ((ballotKeyBitCodec 23 11).encode otherKey) [] (some true) :=
  log_run [((),otherKey),((),key)] otherKey

/-- An empty field still contributes its delimiter and increments the count. -/
theorem empty_control :
    ∃ fuel ≤ cost 0 0 0,
      tick^[fuel] (start [] [false]) =
        state none [] [] [] [true,false,true,false] [] [] [] [] (some true) := by
  exact run [] []

/-- Nonpalindromic body and field exercise both transfer reversals. -/
theorem order_bits_control :
    ∃ fuel ≤ cost 2 2 11,
      tick^[fuel] (start [true,false] (bitFieldsEncode [[false,true],[true]])) =
        state none [] [] [] (bitFieldsEncode [[false,true],[true],[true,false]]) [] [] [true,false] [] (some true) := by
  exact run [[false,true],[true]] [true,false]

/-- Chronological append cannot be the tempting prepend implementation. -/
theorem not_prepend_control :
    ∃ fuel ≤ cost 2 2 11,
      let c := tick^[fuel] (start [true,false] (bitFieldsEncode [[false,true],[true]]))
      c.l = none ∧ readout c = some (bitFieldsEncode [[false,true],[true],[true,false]]) ∧
        readout c ≠ some (bitFieldsEncode [[true,false],[false,true],[true]]) := by
  obtain ⟨fuel,hf,hr⟩ := order_bits_control
  refine ⟨fuel,hf,?_⟩
  dsimp only
  rw [hr]
  exact ⟨rfl,rfl,by decide⟩

/-- The outer count crosses a binary-width boundary, while field order survives. -/
theorem boundary_control :
    ∃ fuel ≤ cost 3 1 12,
      tick^[fuel] (start [true] (bitFieldsEncode [[false],[false],[false]])) =
        state none [] [] [] (bitFieldsEncode [[false],[false],[false],[true]]) [] [] [true] [] (some true) := by
  exact run [[false],[false],[false]] [true]

#print axioms supports
#print axioms run
#print axioms cost_mono
#print axioms log_run
#print axioms source_log_run
#print axioms order_control
#print axioms empty_control
#print axioms order_bits_control
#print axioms not_prepend_control
#print axioms boundary_control
end ExplainableCrypto.Helios.Computational.LogAppendMachine
