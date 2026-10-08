import ExplainableCrypto.Helios.Computational.CacheLookupMachine
import ExplainableCrypto.Helios.Computational.FrameWriteMachine

/-! Guarded insertion for the actual source's cache-miss branches. Lookup derives
freshness; all new entry/count framing is executed from loaded key/scalar words. -/
namespace ExplainableCrypto.Helios.Computational.CacheInsertMachine
open Turing.TM2
abbrev Stack := CacheLookupMachine.Stack ⊕ Unit
abbrev src : Stack := .inl CacheLookupMachine.src
abbrev cnt : Stack := .inl CacheLookupMachine.cnt
abbrev temp : Stack := .inl CacheLookupMachine.temp
abbrev out : Stack := .inl CacheLookupMachine.out
abbrev outer : Stack := .inl CacheLookupMachine.outer
abbrev archive : Stack := .inl CacheLookupMachine.archive
abbrev query : Stack := .inl CacheLookupMachine.query
abbrev saved : Stack := .inl CacheLookupMachine.saved
abbrev answer : Stack := .inr ()

inductive Extra where
  | count | query | cache | answer
  deriving DecidableEq

def writerLayout : FrameWriteMachine.Stack ⊕ Extra ≃ Stack where
  toFun
    | .inl (.inl k) => .inl (.inl (.inl (.inl k)))
    | .inl (.inr _) => archive
    | .inr .count => outer | .inr .query => query
    | .inr .cache => saved | .inr .answer => answer
  invFun
    | .inl (.inl (.inl (.inl k))) => .inl (.inl k)
    | .inl (.inl (.inl (.inr false))) => .inr .count
    | .inl (.inl (.inl (.inr true))) => .inl (.inr ())
    | .inl (.inl (.inr _)) => .inr .query
    | .inl (.inr _) => .inr .cache
    | .inr _ => .inr .answer
  left_inv x := by
    rcases x with ((k|⟨⟩)|e)
    · rfl
    · rfl
    · cases e <;> rfl
  right_inv x := by
    rcases x with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl

def parseLayout : NatPrefixMachine.Stack ⊕ (Unit ⊕ Extra) ≃ Stack :=
  ((Equiv.sumAssoc NatPrefixMachine.Stack Unit Extra).symm.trans writerLayout).trans
    ((Equiv.swap src saved).trans (Equiv.swap out outer))
def entryLayout := writerLayout.trans ((Equiv.swap src out).trans (Equiv.swap src saved))
def finalLayout := writerLayout.trans ((Equiv.swap out saved).trans (Equiv.swap archive outer))

def writerFrame (q cache value count : List Bool) : Extra → List Bool
  | .count => count | .query => q | .cache => cache | .answer => value

def parserFrame (q value : List Bool) : Unit ⊕ Extra → List Bool
  | .inl _ => [] | .inr .count => [] | .inr .query => q
  | .inr .cache => [] | .inr .answer => value

inductive CopyExtra where
  | count | output | counter | archive | cache | other
  deriving DecidableEq

def keyCopyLayout : BitCopyMachine.Stack ⊕ CopyExtra ≃ Stack where
  toFun
    | .inl .source => query | .inl .destination => src | .inl .scratch => temp
    | .inr .count => cnt | .inr .output => out | .inr .counter => outer
    | .inr .archive => archive | .inr .cache => saved | .inr .other => answer
  invFun
    | .inl (.inl (.inl (.inl .input))) => .inl .destination
    | .inl (.inl (.inl (.inl .count))) => .inr .count
    | .inl (.inl (.inl (.inl .scratch))) => .inl .scratch
    | .inl (.inl (.inl (.inl .output))) => .inr .output
    | .inl (.inl (.inl (.inr false))) => .inr .counter
    | .inl (.inl (.inl (.inr true))) => .inr .archive
    | .inl (.inl (.inr _)) => .inl .source
    | .inl (.inr _) => .inr .cache
    | .inr _ => .inr .other
  left_inv x := by
    rcases x with (k|e)
    · cases k <;> rfl
    · cases e <;> rfl
  right_inv x := by
    rcases x with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl

def copyLayout (scalar : Bool) := if scalar then keyCopyLayout.trans (Equiv.swap query answer) else keyCopyLayout

def copyFrame (word count cache other : List Bool) : CopyExtra → List Bool
  | .count => [] | .output => word | .counter => count | .archive => []
  | .cache => cache | .other => other

inductive WriteStage where
  | scalar | key | entry | final
  deriving DecidableEq
instance : Fintype WriteStage where
  elems := {.scalar,.key,.entry,.final}
  complete s := by cases s <;> simp

def writeLayout : WriteStage → FrameWriteMachine.Stack ⊕ Extra ≃ Stack
  | .scalar | .key => writerLayout | .entry => entryLayout | .final => finalLayout

def operandStage (scalar : Bool) : WriteStage := if scalar then .scalar else .key

inductive Label where
  | lookup (l : CacheLookupMachine.Label) | parse (l : NatPrefixMachine.Label)
  | increment (b : Bool) | copy (scalar phase : Bool)
  | write (s : WriteStage) (l : FrameWriteMachine.Label)
  | lookupDone | parseDone | incDone | copyDone (scalar : Bool)
  | writeDone (s : WriteStage) | pair
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨lookup default⟩
instance : Fintype Label where
  elems := Finset.univ.image lookup ∪ Finset.univ.image parse ∪ Finset.univ.image increment ∪
    Finset.univ.image (fun p : Bool × Bool => copy p.1 p.2) ∪
    Finset.univ.image (fun p : WriteStage × FrameWriteMachine.Label => write p.1 p.2) ∪
    Finset.univ.image copyDone ∪ Finset.univ.image writeDone ∪ {lookupDone,parseDone,incDone,pair}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def invalid : Stmt (fun _ : Stack => Bool) Label (Option Bool) := .load (fun _ => none) .halt

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | lookup l => TM2ReturnLink.redirect lookup lookupDone
      (TM2StackFrame.relocate (Equiv.refl _) (CacheLookupMachine.program l))
  | parse l => TM2ReturnLink.redirect parse parseDone (TM2StackFrame.relocate parseLayout (NatPrefixMachine.program l))
  | increment b => TM2ReturnLink.redirect increment incDone (TM2StackFrame.relocate parseLayout (BitIncrementMachine.program b))
  | copy b l => TM2ReturnLink.redirect (copy b) (copyDone b) (TM2StackFrame.relocate (copyLayout b) (BitCopyMachine.program l))
  | write s l => TM2ReturnLink.redirect (write s) (writeDone s) (TM2StackFrame.relocate (writeLayout s) (FrameWriteMachine.program l))
  | lookupDone => .branch Option.isSome
      (.branch (fun v => v.getD false) (.load (fun _ => some false) .halt)
        (.load (fun _ => none) (.goto (fun _ => parse default)))) invalid
  | parseDone => .branch (fun v => decide (v = some true))
      (.load (fun _ => none) (.goto (fun _ => increment false))) invalid
  | incDone => .load (fun _ => none) (.goto (fun _ => copy true false))
  | copyDone b => .load (fun _ => none) (.goto (fun _ => write (operandStage b) default))
  | writeDone .scalar => .load (fun _ => none) (.goto (fun _ => copy false false))
  | writeDone .key => .goto (fun _ => pair)
  | pair => .push out (fun _ => true) <| .push out (fun _ => false) <| .push out (fun _ => false) <|
      .push out (fun _ => true) <| .push out (fun _ => true) <|
      .load (fun _ => none) (.goto (fun _ => write .entry default))
  | writeDone .entry => .load (fun _ => none) (.goto (fun _ => write .final .digits))
  | writeDone .final => .load (fun _ => some true) .halt

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (q source count scratch word n value cache a : List Bool) (v : Option Bool) : Config :=
  ⟨phase,v,fun
    | .inl k => (CacheLookupMachine.state none q source count scratch word n value cache v).stk k
    | .inr _ => a⟩
def start (q a cache : List Bool) : Config :=
  TM2ReturnLink.embed lookup lookupDone
    (TM2StackFrame.embed (Equiv.refl _) (CacheLookupMachine.start q cache) (fun _ => a))

def readout (c : Config) : Option (Bool × List Bool) :=
  if c.l = none then c.var.map (fun b => (b,c.stk saved)) else none

private theorem redirect_supports {L : Type*} (f : L → Label) (ret : Label)
    (s : Stmt (fun _ : Stack => Bool) L (Option Bool)) :
    SupportsStmt Finset.univ (TM2ReturnLink.redirect f ret s) := by
  induction s <;> simp_all [TM2ReturnLink.redirect,SupportsStmt]

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _
    cases l with
    | writeDone s => cases s <;> simp [program,SupportsStmt]
    | _ => simp [program,invalid,redirect_supports,SupportsStmt]

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

private theorem parse_run (n : Nat) (q a body : List Bool) :
    ∃ fuel ≤ 3*n.size+3,
      tick^[fuel] (state (some (parse default)) q [] [] [] [] [] [] (uniformNatEncode n++body) a none) =
        state (some parseDone) q [] [] [] [] n.bits [] body a (some true) := by
  have hr := NatPrefixMachine.encoded_run n body
  have hh : (NatPrefixMachine.tick^[3*n.size+3]
      (NatPrefixMachine.start (uniformNatEncode n++body))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run parseLayout NatPrefixMachine.program parse parseDone (fun _ => rfl)
    (3*n.size+3) (NatPrefixMachine.start (uniformNatEncode n++body)) (parserFrame q a) hh
  change tick^[u] _ = TM2ReturnLink.embed parse parseDone
    (TM2StackFrame.embed parseLayout (NatPrefixMachine.tick^[3*n.size+3] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed parse parseDone (TM2StackFrame.embed parseLayout
      (NatPrefixMachine.start (uniformNatEncode n++body)) (parserFrame q a)) =
      state (some (parse default)) q [] [] [] [] [] [] (uniformNatEncode n++body) a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

private theorem increment_run (n : Nat) (q a body : List Bool) :
    ∃ fuel ≤ 2*n.size+2,
      tick^[fuel] (state (some (increment false)) q [] [] [] [] n.bits [] body a none) =
        state (some incDone) q [] [] [] [] (n+1).bits [] body a (some true) := by
  obtain ⟨j,hj,hr⟩ := BitIncrementMachine.run n body [] none
  have hh : (BitIncrementMachine.tick^[j]
      (BitIncrementMachine.config (some false) n.bits [] body [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run parseLayout BitIncrementMachine.program increment incDone (fun _ => rfl)
    j (BitIncrementMachine.config (some false) n.bits [] body [] none) (parserFrame q a) hh
  change tick^[u] _ = TM2ReturnLink.embed increment incDone
    (TM2StackFrame.embed parseLayout (BitIncrementMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed increment incDone (TM2StackFrame.embed parseLayout
      (BitIncrementMachine.config (some false) n.bits [] body [] none) (parserFrame q a)) =
      state (some (increment false)) q [] [] [] [] n.bits [] body a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

private theorem copy_run (scalar : Bool) (q a word count body : List Bool) :
    ∃ fuel ≤ 2*(if scalar then a else q).length+2,
      tick^[fuel] (state (some (copy scalar false)) q [] [] [] word count [] body a none) =
        state (some (copyDone scalar)) q (if scalar then a else q) [] [] word count [] body a none := by
  have hr := BitCopyMachine.run (if scalar then a else q) [] none
  simp only [List.append_nil] at hr
  have hh : (BitCopyMachine.tick^[2*(if scalar then a else q).length+2]
      (BitCopyMachine.config (some false) (if scalar then a else q) [] [] none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run (copyLayout scalar) BitCopyMachine.program (copy scalar) (copyDone scalar) (fun _ => rfl)
    (2*(if scalar then a else q).length+2)
    (BitCopyMachine.config (some false) (if scalar then a else q) [] [] none)
    (copyFrame word count body (if scalar then q else a)) hh
  change tick^[u] _ = TM2ReturnLink.embed (copy scalar) (copyDone scalar)
    (TM2StackFrame.embed (copyLayout scalar) (BitCopyMachine.tick^[2*(if scalar then a else q).length+2] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed (copy scalar) (copyDone scalar) (TM2StackFrame.embed (copyLayout scalar)
      (BitCopyMachine.config (some false) (if scalar then a else q) [] [] none)
      (copyFrame word count body (if scalar then q else a))) =
      state (some (copy scalar false)) q [] [] [] word count [] body a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    cases scalar <;> rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    all_goals first | (cases k <;> rfl) | (cases b <;> rfl) | rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  cases scalar <;> rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  all_goals first | (cases k <;> rfl) | (cases b <;> rfl) | rfl

private theorem operand_run (scalar : Bool) (q a bytes word count body : List Bool) :
    ∃ fuel ≤ FrameWriteMachine.cost bytes.length,
      tick^[fuel] (state (some (write (operandStage scalar) default)) q bytes [] [] word count [] body a none) =
        state (some (writeDone (operandStage scalar))) q [] [] []
          (uniformNatEncode bytes.length++(bytes++word)) count [] body a (some true) := by
  obtain ⟨j,hj,hr⟩ := FrameWriteMachine.run bytes word
  have hh : (FrameWriteMachine.tick^[j] (FrameWriteMachine.start bytes word)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run writerLayout FrameWriteMachine.program
    (write (operandStage scalar)) (writeDone (operandStage scalar)) (fun _ => by cases scalar <;> rfl)
    j (FrameWriteMachine.start bytes word) (writerFrame q body a count) hh
  change tick^[u] _ = TM2ReturnLink.embed (write (operandStage scalar)) (writeDone (operandStage scalar))
    (TM2StackFrame.embed writerLayout (FrameWriteMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed (write (operandStage scalar)) (writeDone (operandStage scalar))
      (TM2StackFrame.embed writerLayout (FrameWriteMachine.start bytes word) (writerFrame q body a count)) =
      state (some (write (operandStage scalar) default)) q bytes [] [] word count [] body a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

private theorem entry_run (q a bytes count body : List Bool) :
    ∃ fuel ≤ FrameWriteMachine.cost bytes.length,
      tick^[fuel] (state (some (write .entry default)) q [] [] [] bytes count [] body a none) =
        state (some (writeDone .entry)) q [] [] [] [] count []
          (uniformNatEncode bytes.length++(bytes++body)) a (some true) := by
  obtain ⟨j,hj,hr⟩ := FrameWriteMachine.run bytes body
  have hh : (FrameWriteMachine.tick^[j] (FrameWriteMachine.start bytes body)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run entryLayout FrameWriteMachine.program (write .entry) (writeDone .entry) (fun _ => rfl)
    j (FrameWriteMachine.start bytes body) (writerFrame q [] a count) hh
  change tick^[u] _ = TM2ReturnLink.embed (write .entry) (writeDone .entry)
    (TM2StackFrame.embed entryLayout (FrameWriteMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed (write .entry) (writeDone .entry)
      (TM2StackFrame.embed entryLayout (FrameWriteMachine.start bytes body) (writerFrame q [] a count)) =
      state (some (write .entry default)) q [] [] [] bytes count [] body a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu.trans hj,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

private theorem final_run (n : Nat) (q a body : List Bool) :
    ∃ fuel ≤ 3*n.size+3,
      tick^[fuel] (state (some (write .final .digits)) q [] [] [] [] n.bits [] body a none) =
        state (some (writeDone .final)) q [] [] [] [] [] [] (uniformNatEncode n++body) a (some true) := by
  have hr := FrameWriteMachine.prefix_run n body none
  have hh : (FrameWriteMachine.tick^[3*n.size+3] (FrameWriteMachine.state (some .digits) [] [] [] body n.bits none)).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run finalLayout FrameWriteMachine.program (write .final) (writeDone .final) (fun _ => rfl)
    (3*n.size+3) (FrameWriteMachine.state (some .digits) [] [] [] body n.bits none) (writerFrame q [] a []) hh
  change tick^[u] _ = TM2ReturnLink.embed (write .final) (writeDone .final)
    (TM2StackFrame.embed finalLayout (FrameWriteMachine.tick^[3*n.size+3] _) _) at he
  rw [hr] at he
  have hs : TM2ReturnLink.embed (write .final) (writeDone .final)
      (TM2StackFrame.embed finalLayout (FrameWriteMachine.state (some .digits) [] [] [] body n.bits none) (writerFrame q [] a [])) =
      state (some (write .final .digits)) q [] [] [] [] n.bits [] body a none := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hs] at he
  refine ⟨u,hu,he.trans ?_⟩
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> rfl
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

def builderCost (K A E n : Nat) : Nat :=
  5*n.size+3*(n+1).size+2*A+2*K+
    FrameWriteMachine.cost A+FrameWriteMachine.cost K+FrameWriteMachine.cost E+21

private theorem pair_step (q a body count : List Bool) :
    tick (state (some pair) q [] [] [] (uniformNatEncode q.length++(q++(uniformNatEncode a.length++a)))
      count [] body a (some true)) =
      state (some (write .entry default)) q [] [] [] (bitFieldsEncode [q,a]) count [] body a none := by
  simp [tick,state,CacheLookupMachine.state,PreservingCompareMachine.parserState,
    RecordFieldStepMachine.state,program,stepAux]
  funext k
  rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
  · cases k <;> simp [bitFieldsEncode,bitFramesEncode,List.append_assoc,
      show uniformNatEncode 2 = [true,true,false,false,true] from rfl]
  · cases b <;> simp
  · simp
  · simp
  · simp

/-- Complete construction after the guarded lookup has supplied a fresh cache.
The count and all three nested field frames are produced by actual programs. -/
private theorem builder_run (n : Nat) (q a body : List Bool) :
    ∃ fuel ≤ builderCost q.length a.length (bitFieldsEncode [q,a]).length n,
      tick^[fuel] (state (some (parse default)) q [] [] [] [] [] [] (uniformNatEncode n++body) a none) =
        state none q [] [] [] [] [] [] (uniformNatEncode (n+1)++
          (uniformNatEncode (bitFieldsEncode [q,a]).length++(bitFieldsEncode [q,a]++body))) a (some true) := by
  obtain ⟨i,hi,hp⟩ := parse_run n q a body
  obtain ⟨j,hj,hn⟩ := increment_run n q a body
  obtain ⟨k,hk,hca⟩ := copy_run true q a [] (n+1).bits body
  obtain ⟨l,hl,hwa⟩ := operand_run true q a a [] (n+1).bits body
  simp only [List.append_nil] at hwa
  obtain ⟨m,hm,hck⟩ := copy_run false q a (uniformNatEncode a.length++a) (n+1).bits body
  obtain ⟨r,hr,hwk⟩ := operand_run false q a q (uniformNatEncode a.length++a) (n+1).bits body
  obtain ⟨s,hs,hwe⟩ := entry_run q a (bitFieldsEncode [q,a]) (n+1).bits body
  obtain ⟨t,ht,hwf⟩ := final_run (n+1) q a
    (uniformNatEncode (bitFieldsEncode [q,a]).length++(bitFieldsEncode [q,a]++body))
  simp only [operandStage,ite_true,Bool.false_eq_true,ite_false] at hwa hwk
  have hp' : tick^[i+1] (state (some (parse default)) q [] [] [] [] [] [] (uniformNatEncode n++body) a none) =
      state (some (increment false)) q [] [] [] [] n.bits [] body a none := by
    rw [Function.iterate_succ_apply',hp]; rfl
  have hn' : tick^[j+1] (state (some (increment false)) q [] [] [] [] n.bits [] body a none) =
      state (some (copy true false)) q [] [] [] [] (n+1).bits [] body a none := by
    rw [Function.iterate_succ_apply',hn]; rfl
  have hca' : tick^[k+1] (state (some (copy true false)) q [] [] [] [] (n+1).bits [] body a none) =
      state (some (write .scalar default)) q a [] [] [] (n+1).bits [] body a none := by
    rw [Function.iterate_succ_apply',hca]; rfl
  have hwa' : tick^[l+1] (state (some (write .scalar default)) q a [] [] [] (n+1).bits [] body a none) =
      state (some (copy false false)) q [] [] [] (uniformNatEncode a.length++a) (n+1).bits [] body a none := by
    rw [Function.iterate_succ_apply',hwa]; rfl
  have hck' : tick^[m+1] (state (some (copy false false)) q [] [] [] (uniformNatEncode a.length++a) (n+1).bits [] body a none) =
      state (some (write .key default)) q q [] [] (uniformNatEncode a.length++a) (n+1).bits [] body a none := by
    rw [Function.iterate_succ_apply',hck]; rfl
  have hwk' : tick^[r+2] (state (some (write .key default)) q q [] [] (uniformNatEncode a.length++a) (n+1).bits [] body a none) =
      state (some (write .entry default)) q [] [] [] (bitFieldsEncode [q,a]) (n+1).bits [] body a none := by
    rw [show r+2 = (r+1)+1 by omega,Function.iterate_succ_apply' tick (r+1),Function.iterate_succ_apply' tick r,hwk]
    exact pair_step q a body (n+1).bits
  have hwe' : tick^[s+1] (state (some (write .entry default)) q [] [] [] (bitFieldsEncode [q,a]) (n+1).bits [] body a none) =
      state (some (write .final .digits)) q [] [] [] [] (n+1).bits []
        (uniformNatEncode (bitFieldsEncode [q,a]).length++(bitFieldsEncode [q,a]++body)) a none := by
    rw [Function.iterate_succ_apply',hwe]; rfl
  have hwf' : tick^[t+1] (state (some (write .final .digits)) q [] [] [] [] (n+1).bits []
      (uniformNatEncode (bitFieldsEncode [q,a]).length++(bitFieldsEncode [q,a]++body)) a none) =
      state none q [] [] [] [] [] [] (uniformNatEncode (n+1)++
        (uniformNatEncode (bitFieldsEncode [q,a]).length++(bitFieldsEncode [q,a]++body))) a (some true) := by
    rw [Function.iterate_succ_apply',hwf]; rfl
  refine ⟨(t+1)+((s+1)+((r+2)+((m+1)+((l+1)+((k+1)+((j+1)+(i+1))))))),?_,?_⟩
  · unfold builderCost
    simp only [ite_true,ite_false,Bool.false_eq_true] at hk hm
    omega
  · rw [Function.iterate_add_apply tick (t+1),Function.iterate_add_apply tick (s+1),
      Function.iterate_add_apply tick (r+2),Function.iterate_add_apply tick (m+1),
      Function.iterate_add_apply tick (l+1),Function.iterate_add_apply tick (k+1),
      Function.iterate_add_apply tick (j+1),hp',hn',hca',hwa',hck',hwk',hwe',hwf']

private theorem builderCost_mono {K A E n K' A' E' n' : Nat}
    (hk : K ≤ K') (ha : A ≤ A') (he : E ≤ E') (hn : n ≤ n') :
    builderCost K A E n ≤ builderCost K' A' E' n' := by
  have hns := Nat.size_le_size hn
  have hsucc := Nat.size_le_size (Nat.add_le_add_right hn 1)
  have hkc := FrameWriteMachine.cost_mono hk
  have hac := FrameWriteMachine.cost_mono ha
  have hec := FrameWriteMachine.cost_mono he
  unfold builderCost
  omega

def cost (p q N W : Nat) : Nat :=
  2*W+3*N.size+N*CacheLookupMachine.iterationCost p q N+9+
    builderCost (keyRecordBitBound p) (groupRecordBitBound q) (cacheEntryBitBound p q) N

/-- Complete fresh-insertion post-state for the enclosing caller: all work is
cleared and key, answer and new cache are retained. -/
theorem fresh_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) (h : cache.lookup key = none) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode cache)) =
      state none ((ballotKeyBitCodec p q).encode key) [] [] [] [] [] []
        ((ballotCacheBitCodec p q).encode (cache.insert key value)) ((primeScalarBitCodec q).encode value) (some true) := by
  obtain ⟨j,hj,hr⟩ := CacheLookupMachine.miss_run cache key h
  have hh : (CacheLookupMachine.tick^[j] (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key)
      ((ballotCacheBitCodec p q).encode cache))).l = none := by rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := call_run (Equiv.refl _) CacheLookupMachine.program lookup lookupDone (fun _ => rfl)
    j (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))
    (fun _ => (primeScalarBitCodec q).encode value) hh
  change tick^[u] (start _ _ _) = TM2ReturnLink.embed lookup lookupDone
    (TM2StackFrame.embed (Equiv.refl _) (CacheLookupMachine.tick^[j] _) _) at he
  rw [hr] at he
  have hmstate : TM2ReturnLink.embed lookup lookupDone (TM2StackFrame.embed (Equiv.refl _)
      (CacheLookupMachine.state none ((ballotKeyBitCodec p q).encode key) [] [] [] [] [] []
        ((ballotCacheBitCodec p q).encode cache) (some false)) (fun _ => (primeScalarBitCodec q).encode value)) =
      state (some lookupDone) ((ballotKeyBitCodec p q).encode key) [] [] [] [] [] []
        ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value) (some false) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k
    rcases k with ((((k|b)|⟨⟩)|⟨⟩)|⟨⟩)
    · cases k <;> rfl
    · cases b <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hmstate] at he
  have he' : tick^[u+1] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
      ((ballotCacheBitCodec p q).encode cache)) =
      state (some (parse default)) ((ballotKeyBitCodec p q).encode key) [] [] [] [] [] []
        ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value) none := by
    rw [Function.iterate_succ_apply',he]; rfl
  obtain ⟨v,hv,hb⟩ := builder_run cache.entries.length ((ballotKeyBitCodec p q).encode key)
    ((primeScalarBitCodec q).encode value) (bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode))
  have hw : (ballotCacheBitCodec p q).encode cache = uniformNatEncode cache.entries.length++
      bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) := by
    change bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode) = _
    simp only [bitFieldsEncode,List.length_map]
  have hi : (cache.insert key value).entries = ⟨key,value⟩::cache.entries :=
    AList.entries_insert_of_notMem (AList.lookup_eq_none.mp h)
  have hentry : (ballotCacheEntryBitCodec p q).encode ⟨key,value⟩ =
      bitFieldsEncode [(ballotKeyBitCodec p q).encode key,(primeScalarBitCodec q).encode value] := rfl
  have hnew : (ballotCacheBitCodec p q).encode (cache.insert key value) =
      uniformNatEncode (cache.entries.length+1)++
        (uniformNatEncode (bitFieldsEncode [(ballotKeyBitCodec p q).encode key,(primeScalarBitCodec q).encode value]).length++
          (bitFieldsEncode [(ballotKeyBitCodec p q).encode key,(primeScalarBitCodec q).encode value]++
            bitFramesEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode))) := by
    change uniformNatEncode (((cache.insert key value).entries.map (ballotCacheEntryBitCodec p q).encode).length)++
      bitFramesEncode ((cache.insert key value).entries.map (ballotCacheEntryBitCodec p q).encode) = _
    rw [hi,List.map_cons]
    simp only [List.length_cons,List.length_map,bitFramesEncode,hentry,List.append_assoc]
  rw [←hw,←hnew] at hb
  have hk := ballotKeyBits_length_le key
  have ha : ((primeScalarBitCodec q).encode value).length ≤ groupRecordBitBound q := scalarEncode_length_le value
  have hen := ballotCacheEntryBits_length_le (⟨key,value⟩ : PrimeCacheEntry p q)
  rw [hentry] at hen
  have hcost := builderCost_mono hk ha hen (le_refl cache.entries.length)
  refine ⟨v+(u+1),by unfold cost; omega,?_⟩
  rw [Function.iterate_add_apply,he',hb]

private theorem occupied_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value old : ZMod q) (h : cache.lookup key = some old) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode cache))
      c.l = none ∧ readout c = some (false,(ballotCacheBitCodec p q).encode cache) ∧
        c.stk query = (ballotKeyBitCodec p q).encode key ∧ c.stk answer = (primeScalarBitCodec q).encode value := by
  obtain ⟨j,hj,hh,ho,hq,hc⟩ := CacheLookupMachine.run cache key
  let d := CacheLookupMachine.tick^[j] (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key)
    ((ballotCacheBitCodec p q).encode cache))
  change d.l = none at hh
  change CacheLookupMachine.readout d = _ at ho
  change d.stk CacheLookupMachine.query = _ at hq
  change d.stk CacheLookupMachine.saved = _ at hc
  rw [h,Option.map_some] at ho
  have hd : d.var = some true := by
    unfold CacheLookupMachine.readout at ho
    rw [if_pos hh] at ho
    cases hv : d.var with
    | none => simp [hv] at ho
    | some b => cases b <;> simp_all
  obtain ⟨u,hu,he⟩ := call_run (Equiv.refl _) CacheLookupMachine.program lookup lookupDone (fun _ => rfl)
    j (CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))
    (fun _ => (primeScalarBitCodec q).encode value) hh
  change tick^[u] (start _ _ _) = TM2ReturnLink.embed lookup lookupDone
    (TM2StackFrame.embed (Equiv.refl _) d _) at he
  have hf : tick (TM2ReturnLink.embed lookup lookupDone (TM2StackFrame.embed (Equiv.refl _) d
      (fun _ => (primeScalarBitCodec q).encode value))) =
      ⟨none,some false,(TM2StackFrame.embed (Equiv.refl _) d (fun _ => (primeScalarBitCodec q).encode value)).stk⟩ := by
    simp [tick,TM2ReturnLink.embed,TM2StackFrame.embed,hh,hd,program,stepAux]
  refine ⟨u+1,by unfold cost; omega,?_⟩
  dsimp only
  rw [Function.iterate_succ_apply',he,hf]
  refine ⟨rfl,?_,hq,rfl⟩
  change some (false,d.stk CacheLookupMachine.saved) = some (false,(ballotCacheBitCodec p q).encode cache)
  rw [hc]

/-- Complete guarded insertion. Absence is decided by executed lookup, never
supplied by the caller; occupied keys keep the complete original cache. -/
theorem run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode cache))
      c.l = none ∧ readout c = some (if cache.lookup key = none
          then (true,(ballotCacheBitCodec p q).encode (cache.insert key value))
          else (false,(ballotCacheBitCodec p q).encode cache)) ∧
        c.stk query = (ballotKeyBitCodec p q).encode key ∧ c.stk answer = (primeScalarBitCodec q).encode value := by
  cases h : cache.lookup key with
  | none =>
    obtain ⟨fuel,hf,hr⟩ := fresh_run cache key value h
    refine ⟨fuel,hf,?_⟩
    dsimp only
    rw [hr]
    simp only [ite_true]
    exact ⟨rfl,rfl,rfl,rfl⟩
  | some old =>
    obtain ⟨fuel,hf,hr⟩ := occupied_run cache key value old h
    refine ⟨fuel,hf,?_⟩
    simpa only [h,Option.some_ne_none,ite_false] using hr

/-- Increase the count and loaded-word bounds of the same insertion routine. -/
theorem cost_mono {p q N N' W W' : Nat} (hn : N ≤ N') (hw : W ≤ W') :
    cost p q N W ≤ cost p q N' W' := by
  have hs := Nat.size_le_size hn
  have hi : CacheLookupMachine.iterationCost p q N ≤ CacheLookupMachine.iterationCost p q N' := by
    unfold CacheLookupMachine.iterationCost
    omega
  have hm := Nat.mul_le_mul hn hi
  have hb := builderCost_mono (le_refl (keyRecordBitBound p)) (le_refl (groupRecordBitBound q))
    (le_refl (cacheEntryBitBound p q)) hn
  unfold cost
  omega

open OracleComp OracleSpec

/-- Actual supported repaired-source caches supply the entry and bit bounds for
this same guarded insertion program. No freshness/size/frame certificate. -/
theorem source_cache_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (result : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (hs : result ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[])))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) :
    ∃ fuel ≤ cost p q (n+15) (cacheRecordBitBound p q (n+15)),
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode result.2.1))
      c.l = none ∧ readout c = some (if result.2.1.lookup key = none
          then (true,(ballotCacheBitCodec p q).encode (result.2.1.insert key value))
          else (false,(ballotCacheBitCodec p q).encode result.2.1)) ∧
        c.stk query = (ballotKeyBitCodec p q).encode key ∧ c.stk answer = (primeScalarBitCodec q).encode value := by
  obtain ⟨fuel,hf,hr⟩ := run result.2.1 key value
  have hw := repairedSubmissionPrime_cache_bits_le g pk vote attacker n hb result hs
  have hn := runBallotFiniteLogged_cache_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) result hs
  simp only [AList.empty_entries,List.length_nil,Nat.zero_add] at hn
  exact ⟨fuel,hf.trans (cost_mono hn hw),hr⟩

/-- The actual programmed source keeps occupied caches and raises its sticky
flag, even when challenges agree. This proves its cache/flag projection only;
transcript sampling/construction and the programmed-statement list are separate. -/
theorem programmed_cache_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) (stmt : BallotStatement (PrimeGroup p q))
    (t : BallotCommitment (PrimeGroup p q) × ZMod q × BallotResponse (ZMod q)) :
    ∃ fuel ≤ cost p q s.cache.entries.length ((ballotCacheBitCodec p q).encode s.cache).length,
      let c := tick^[fuel] (start ((ballotKeyBitCodec p q).encode (stmt,t.1)) ((primeScalarBitCodec q).encode t.2.1)
        ((ballotCacheBitCodec p q).encode s.cache))
      c.l = none ∧ (readout c).map Prod.snd = some ((ballotCacheBitCodec p q).encode (s.program stmt t).2.cache) ∧
        (readout c).map (fun r => s.bad || !r.1) = some (s.program stmt t).2.bad ∧
        c.stk query = (ballotKeyBitCodec p q).encode (stmt,t.1) ∧ c.stk answer = (primeScalarBitCodec q).encode t.2.1 := by
  obtain ⟨fuel,hf,hh,ho,hq,ha⟩ := run s.cache (stmt,t.1) t.2.1
  refine ⟨fuel,hf,hh,?_,?_,hq,ha⟩
  · rw [ho]
    cases h : s.cache.lookup (stmt,t.1) <;> simp [BallotFiniteProgrammedState.program,h]
  · rw [ho]
    cases h : s.cache.lookup (stmt,t.1) <;> simp [BallotFiniteProgrammedState.program,h]

private def newKey : BallotForkPoint (PrimeGroup 23 11) :=
  ({BallotCacheCodecControls.key.1 with generator := BallotCacheCodecControls.key.1.ciphertext.1},
    BallotCacheCodecControls.key.2)
private def expectedCache : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  ⟨[⟨newKey,7⟩,⟨BallotCacheCodecControls.otherKey,5⟩,⟨BallotCacheCodecControls.key,3⟩],by decide⟩
private def fixtureBound : Nat := cost 23 11 BallotCacheCodecControls.cache.entries.length
  ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache).length

/-- The literal expected order is new key, prior head, prior second entry. -/
theorem prepend_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode newKey) ((primeScalarBitCodec 11).encode 7)
        ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some (true,(ballotCacheBitCodec 23 11).encode expectedCache) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode newKey ∧ c.stk answer = (primeScalarBitCodec 11).encode 7 := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,ha⟩ := run BallotCacheCodecControls.cache newKey 7
  have hn : BallotCacheCodecControls.cache.lookup newKey = none := by decide
  have hi : BallotCacheCodecControls.cache.insert newKey 7 = expectedCache := by
    apply AList.ext; decide
  rw [hn,if_pos rfl,hi] at ho
  refine ⟨fuel,?_,hh,ho,hq,ha⟩
  with_reducible exact hf

theorem head_collision_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey)
        ((primeScalarBitCodec 11).encode 7) ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some (false,(ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.otherKey ∧
        c.stk answer = (primeScalarBitCodec 11).encode 7 := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,ha⟩ := occupied_run BallotCacheCodecControls.cache BallotCacheCodecControls.otherKey 7 5 (by decide)
  refine ⟨fuel,?_,hh,ho,hq,ha⟩
  with_reducible exact hf

/-- A late collision refuses insertion even when old and supplied answers agree. -/
theorem agreeing_collision_control :
    ∃ fuel ≤ fixtureBound,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((primeScalarBitCodec 11).encode 3) ((ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache))
      c.l = none ∧ readout c = some (false,(ballotCacheBitCodec 23 11).encode BallotCacheCodecControls.cache) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧
        c.stk answer = (primeScalarBitCodec 11).encode 3 := by
  unfold fixtureBound
  obtain ⟨fuel,hf,hh,ho,hq,ha⟩ := occupied_run BallotCacheCodecControls.cache BallotCacheCodecControls.key 3 3 (by decide)
  refine ⟨fuel,?_,hh,ho,hq,ha⟩
  with_reducible exact hf

theorem empty_control :
    ∃ fuel ≤ cost 23 11 0 1,
      let c := tick^[fuel] (start ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((primeScalarBitCodec 11).encode 7) [false])
      c.l = none ∧ readout c = some (true,(ballotCacheBitCodec 23 11).encode
          (AList.singleton BallotCacheCodecControls.key 7)) ∧
        c.stk query = (ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key ∧
        c.stk answer = (primeScalarBitCodec 11).encode 7 := by
  obtain ⟨fuel,hf,hr⟩ := fresh_run (∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)) BallotCacheCodecControls.key 7 rfl
  rw [show (ballotCacheBitCodec 23 11).encode (∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)) = [false] from rfl] at hr
  refine ⟨fuel,hf,?_⟩
  dsimp only
  rw [hr]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem malformed_controls :
    ∀ word ∈ [[false,true], [true,false,true], [true,false,true,true,false,true,false],
      [true,false,true,true,true,true,false,false,true,true,true,true,false,false,true,false]],
      let c := tick^[300] (start [true] [false,true] word)
      c.l = none ∧ readout c = none ∧ c.stk query = [true] ∧ c.stk saved = word ∧ c.stk answer = [false,true] := by
  decide +kernel

#print axioms supports
#print axioms run
#print axioms source_cache_run
#print axioms programmed_cache_run
#print axioms prepend_control
#print axioms head_collision_control
#print axioms agreeing_collision_control
#print axioms empty_control
#print axioms malformed_controls
end ExplainableCrypto.Helios.Computational.CacheInsertMachine
