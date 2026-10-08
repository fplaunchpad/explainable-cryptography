import VCVio.OracleComp.OracleSpec
import Mathlib.Data.Nat.Size

/-! Canonical binary records for the actual uniform-range/answer event.
The unary prefix encodes binary width, not the natural value. These are codecs,
not machine-time certificates or a replacement for source execution. -/
namespace ExplainableCrypto.Helios.Computational
open OracleSpec

/-- Width ones, a zero delimiter, then little-endian binary digits. -/
def uniformNatEncode (n : Nat) : List Bool :=
  List.replicate n.bits.length true ++ false :: n.bits

def bitsValue (bits : List Bool) : Nat := bits.foldr Nat.bit 0

theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    change Nat.bit b (bitsValue n.bits) = Nat.bit b n
    rw [ih]

private def readWidth : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => (readWidth rest).map (fun p => (p.1+1,p.2))

private theorem readWidth_frame (n : Nat) (rest : List Bool) :
    readWidth (List.replicate n true ++ false :: rest) = some (n,rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,readWidth,ih]

private theorem readWidth_exact (word : List Bool) (n : Nat) (rest : List Bool)
    (h : readWidth word = some (n,rest)) :
    word = List.replicate n true ++ false :: rest := by
  induction word generalizing n rest with
  | nil => simp [readWidth] at h
  | cons bit word ih =>
    cases bit with
    | false => cases Option.some.inj h; rfl
    | true =>
      obtain ⟨⟨k,suffix⟩,hk,he⟩ := Option.map_eq_some_iff.mp h
      cases he
      simp [List.replicate_succ,ih k suffix hk]

/-- Decode one canonical natural record and preserve the unconsumed suffix. -/
def uniformNatRead (word : List Bool) : Option (Nat × List Bool) := do
  let (width,payload) ← readWidth word
  if width ≤ payload.length then
    let bits := payload.take width
    let n := bitsValue bits
    if n.bits = bits then some (n,payload.drop width) else none
  else none

/-- Exact prefix round trip for every trailing word. -/
theorem uniformNatRead_encode (n : Nat) (suffix : List Bool) :
    uniformNatRead (uniformNatEncode n ++ suffix) = some (n,suffix) := by
  simp [uniformNatRead,uniformNatEncode,List.append_assoc,readWidth_frame,bitsValue_bits]

/-- Successful decoding admits only the canonical record, with no ignored bits. -/
theorem uniformNatRead_exact (word : List Bool) (n : Nat) (suffix : List Bool)
    (h : uniformNatRead word = some (n,suffix)) : word = uniformNatEncode n ++ suffix := by
  unfold uniformNatRead at h
  cases hw : readWidth word with
  | none => simp [hw] at h
  | some p =>
    rcases p with ⟨width,payload⟩
    simp only [hw] at h
    dsimp only [Bind.bind,Option.bind] at h
    split at h
    · rename_i hwidth
      split at h
      · rename_i hc
        cases Option.some.inj h
        rw [readWidth_exact word width payload hw]
        simp only [uniformNatEncode,hc,List.length_take_of_le hwidth,List.append_assoc,
          List.cons_append,List.take_append_drop]
      · cases h
    · cases h

theorem uniformNatEncode_length (n : Nat) :
    (uniformNatEncode n).length = 2*n.size+1 := by
  simp only [uniformNatEncode,List.length_append,List.length_replicate,List.length_cons,
    Nat.size_eq_bits_len]
  omega

abbrev UniformEvent := Σ n : unifSpec.Domain, unifSpec.Range n

def uniformEventEncode (event : UniformEvent) : List Bool :=
  uniformNatEncode event.1 ++ uniformNatEncode event.2.val

/-- The event decoder checks both canonical naturals, the answer's declared
range, and complete consumption of the supplied word. -/
def uniformEventDecode (word : List Bool) : Option UniformEvent := do
  let (n,rest) ← uniformNatRead word
  let (answer,suffix) ← uniformNatRead rest
  if suffix = [] then
    if h : answer < n+1 then some ⟨n,⟨answer,h⟩⟩ else none
  else none

theorem uniformEventDecode_encode (event : UniformEvent) :
    uniformEventDecode (uniformEventEncode event) = some event := by
  rcases event with ⟨n,answer⟩
  simp [uniformEventDecode,uniformEventEncode,uniformNatRead_encode,
    show uniformNatRead (uniformNatEncode answer.val) = some (answer.val,[]) from
      by simpa using uniformNatRead_encode answer.val []]

/-- Decoding cannot silently ignore a malformed prefix or trailing suffix. -/
theorem uniformEventDecode_exact (word : List Bool) (event : UniformEvent)
    (h : uniformEventDecode word = some event) : word = uniformEventEncode event := by
  unfold uniformEventDecode at h
  cases hn : uniformNatRead word with
  | none => simp [hn] at h
  | some p =>
    rcases p with ⟨n,rest⟩
    simp only [hn] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases ha : uniformNatRead rest with
    | none => simp [ha] at h
    | some p =>
      rcases p with ⟨a,suffix⟩
      simp only [ha] at h
      split at h
      · rename_i hs
        subst suffix
        split at h
        · cases Option.some.inj h
          rw [uniformNatRead_exact word n rest hn]
          have he := uniformNatRead_exact rest a [] ha
          simpa only [uniformEventEncode,List.append_nil] using congrArg (uniformNatEncode n ++ ·) he
        · cases h
      · cases h

theorem uniformEventEncode_length (event : UniformEvent) :
    (uniformEventEncode event).length = 2*event.1.size+2*event.2.val.size+2 := by
  simp only [uniformEventEncode,List.length_append,uniformNatEncode_length]
  omega

#print axioms bitsValue_bits
#print axioms uniformNatRead_encode
#print axioms uniformNatRead_exact
#print axioms uniformNatEncode_length
#print axioms uniformEventDecode_encode
#print axioms uniformEventDecode_exact
#print axioms uniformEventEncode_length
end ExplainableCrypto.Helios.Computational
