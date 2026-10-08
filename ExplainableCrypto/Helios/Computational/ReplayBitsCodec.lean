import ExplainableCrypto.Helios.Computational.ScalarCodec
import ExplainableCrypto.Helios.Computational.BallotReplayTape

/-! Complete canonical bit records for the actual lowered entropy tape.
Uniform events and scalar challenges retain distinct tags. Event lengths and the
number of events are checked; malformed input is never reduced modulo q. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

abbrev ReplayEvent (q : Nat) := Σ t : (FiatShamir.Fork.wrappedSpec (ZMod q)).Domain,
  (FiatShamir.Fork.wrappedSpec (ZMod q)).Range t
abbrev ReplayTape (q : Nat) := List (ReplayEvent q)

def replayEventEncode {q : Nat} : ReplayEvent q → List Bool
  | ⟨.inl n,a⟩ => false :: uniformEventEncode ⟨n,a⟩
  | ⟨.inr _,a⟩ => true :: scalarEncode a

def replayEventDecode (q : Nat) : List Bool → Option (ReplayEvent q)
  | [] => none
  | false :: word => (uniformEventDecode word).map (fun e => ⟨.inl e.1,e.2⟩)
  | true :: word => (scalarDecode q word).map (fun a => ⟨.inr (),a⟩)

variable {q : Nat}

theorem replayEventDecode_encode [NeZero q] (e : ReplayEvent q) :
    replayEventDecode q (replayEventEncode e) = some e := by
  rcases e with ⟨t,a⟩
  cases t with
  | inl n => simp [replayEventDecode,replayEventEncode,uniformEventDecode_encode]
  | inr u => cases u; simp [replayEventDecode,replayEventEncode,scalarDecode_encode]

theorem replayEventDecode_exact (word : List Bool) (e : ReplayEvent q)
    (h : replayEventDecode q word = some e) : word = replayEventEncode e := by
  cases word with
  | nil => cases h
  | cons tag word =>
    cases tag with
    | false =>
      obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp h
      subst e
      change false :: word = false :: uniformEventEncode u
      rw [uniformEventDecode_exact word u hu]
    | true =>
      obtain ⟨a,ha,he⟩ := Option.map_eq_some_iff.mp h
      subst e
      change true :: word = true :: scalarEncode a
      rw [scalarDecode_exact word a ha]

/-- Frame a single typed event by the length of its encoded word. -/
def replayEventFrame (e : ReplayEvent q) : List Bool :=
  uniformNatEncode (replayEventEncode e).length ++ replayEventEncode e

def replayFramesEncode : ReplayTape q → List Bool
  | [] => []
  | e :: es => replayEventFrame e ++ replayFramesEncode es

/-- Read exactly the supplied number of frames, returning the untouched suffix. -/
def replayFramesRead (q : Nat) : Nat → List Bool → Option (ReplayTape q × List Bool)
  | 0,word => some ([],word)
  | n+1,word => do
    let (size,payload) ← uniformNatRead word
    if size ≤ payload.length then
      let e ← replayEventDecode q (payload.take size)
      let (es,suffix) ← replayFramesRead q n (payload.drop size)
      some (e::es,suffix)
    else none

theorem replayFramesRead_encode [NeZero q] (es : ReplayTape q) (suffix : List Bool) :
    replayFramesRead q es.length (replayFramesEncode es ++ suffix) = some (es,suffix) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp [replayFramesEncode,replayFramesRead,replayEventFrame,List.append_assoc,
      uniformNatRead_encode,replayEventDecode_encode,ih]

/-- Accepted frames account for exactly n events and all consumed bits. -/
theorem replayFramesRead_exact (n : Nat) (word : List Bool) (es : ReplayTape q)
    (suffix : List Bool) (h : replayFramesRead q n word = some (es,suffix)) :
    es.length = n ∧ word = replayFramesEncode es ++ suffix := by
  induction n generalizing word es suffix with
  | zero =>
    cases Option.some.inj h
    exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [replayFramesRead] at h
    cases hn : uniformNatRead word with
    | none => simp [hn] at h
    | some p =>
      rcases p with ⟨size,payload⟩
      simp only [hn] at h
      dsimp only [Bind.bind,Option.bind] at h
      split at h
      · rename_i hs
        cases he : replayEventDecode q (payload.take size) with
        | none => simp [he] at h
        | some e =>
          simp only [he] at h
          cases hr : replayFramesRead q n (payload.drop size) with
          | none => simp [hr] at h
          | some p =>
            rcases p with ⟨rest,tail⟩
            simp only [hr] at h
            cases Option.some.inj h
            obtain ⟨hlen,hrest⟩ := ih _ _ _ hr
            have hword := uniformNatRead_exact word size payload hn
            have hframe := replayEventDecode_exact (payload.take size) e he
            have hsize : size = (replayEventEncode e).length := by
              rw [← hframe,List.length_take_of_le hs]
            constructor
            · simp [hlen]
            · rw [hword]
              rw [← List.take_append_drop size payload,hframe,hrest,hsize]
              simp [replayFramesEncode,replayEventFrame,List.append_assoc]
      · cases h

def replayTapeEncode (es : ReplayTape q) : List Bool :=
  uniformNatEncode es.length ++ replayFramesEncode es

def replayTapeDecode (q : Nat) (word : List Bool) : Option (ReplayTape q) := do
  let (n,rest) ← uniformNatRead word
  let (es,suffix) ← replayFramesRead q n rest
  if suffix = [] then some es else none

theorem replayTapeDecode_encode [NeZero q] (es : ReplayTape q) :
    replayTapeDecode q (replayTapeEncode es) = some es := by
  have hf := replayFramesRead_encode es []
  simp only [List.append_nil] at hf
  simp [replayTapeEncode,replayTapeDecode,uniformNatRead_encode,hf]

theorem replayTapeDecode_exact (word : List Bool) (es : ReplayTape q)
    (h : replayTapeDecode q word = some es) : word = replayTapeEncode es := by
  unfold replayTapeDecode at h
  cases hn : uniformNatRead word with
  | none => simp [hn] at h
  | some p =>
    rcases p with ⟨n,rest⟩
    simp only [hn] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases hr : replayFramesRead q n rest with
    | none => simp [hr] at h
    | some p =>
      rcases p with ⟨events,suffix⟩
      simp only [hr] at h
      split at h
      · rename_i hs
        subst suffix
        cases Option.some.inj h
        obtain ⟨hlen,hrest⟩ := replayFramesRead_exact n rest _ [] hr
        have hw := uniformNatRead_exact word n rest hn
        simpa only [replayTapeEncode,hlen,List.append_nil,hrest] using hw
      · cases h

/-- Exact bit cost of the encoded record, retaining each operand's actual width. -/
theorem replayTapeEncode_length (es : ReplayTape q) :
    (replayTapeEncode es).length = 2*es.length.size+1+
      (List.map (fun e => 2*(replayEventEncode e).length.size+1+
        (replayEventEncode e).length) es).sum := by
  have hf : (replayFramesEncode es).length =
      (List.map (fun e => 2*(replayEventEncode e).length.size+1+
        (replayEventEncode e).length) es).sum := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp [replayFramesEncode,replayEventFrame,uniformNatEncode_length,ih,Nat.add_assoc]
  simp only [replayTapeEncode,List.length_append,uniformNatEncode_length,hf]

#print axioms replayEventDecode_encode
#print axioms replayEventDecode_exact
#print axioms replayFramesRead_encode
#print axioms replayFramesRead_exact
#print axioms replayTapeDecode_encode
#print axioms replayTapeDecode_exact
#print axioms replayTapeEncode_length
end ExplainableCrypto.Helios.Computational
