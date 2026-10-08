import ExplainableCrypto.Helios.Computational.UniformOperandCodec

/-! Canonical framing for the heterogeneous fields in concrete keys, cache
entries and boards. These laws concern bit records, not execution costs. -/
namespace ExplainableCrypto.Helios.Computational

def bitFramesEncode : List (List Bool) → List Bool
  | [] => []
  | w::ws => uniformNatEncode w.length ++ w ++ bitFramesEncode ws

def bitFramesRead : Nat → List Bool → Option (List (List Bool) × List Bool)
  | 0,word => some ([],word)
  | n+1,word => do
    let (size,payload) ← uniformNatRead word
    if size ≤ payload.length then
      let (ws,suffix) ← bitFramesRead n (payload.drop size)
      some (payload.take size::ws,suffix)
    else none

theorem bitFramesRead_encode (ws : List (List Bool)) (suffix : List Bool) :
    bitFramesRead ws.length (bitFramesEncode ws ++ suffix) = some (ws,suffix) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [bitFramesEncode,bitFramesRead,List.append_assoc,uniformNatRead_encode,ih]

theorem bitFramesRead_exact (n : Nat) (word : List Bool)
    (ws : List (List Bool)) (suffix : List Bool)
    (h : bitFramesRead n word = some (ws,suffix)) :
    ws.length = n ∧ word = bitFramesEncode ws ++ suffix := by
  induction n generalizing word ws suffix with
  | zero => cases Option.some.inj h; exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [bitFramesRead] at h
    cases hn : uniformNatRead word with
    | none => simp [hn] at h
    | some pair =>
      rcases pair with ⟨size,payload⟩
      simp only [hn] at h
      dsimp only [Bind.bind,Option.bind] at h
      split at h
      · rename_i hs
        cases hr : bitFramesRead n (payload.drop size) with
        | none => simp [hr] at h
        | some pair =>
          rcases pair with ⟨rest,tail⟩
          simp only [hr] at h
          cases Option.some.inj h
          obtain ⟨hlen,hrest⟩ := ih _ _ _ hr
          constructor
          · simp [hlen]
          · rw [uniformNatRead_exact word size payload hn]
            simp only [bitFramesEncode,List.length_take_of_le hs,List.append_assoc]
            rw [← hrest,List.take_append_drop]
      · cases h

/-- Count and length prefixes use binary widths; field payloads remain literal. -/
def bitFieldsEncode (ws : List (List Bool)) : List Bool :=
  uniformNatEncode ws.length ++ bitFramesEncode ws

def bitFieldsDecode (word : List Bool) : Option (List (List Bool)) := do
  let (n,rest) ← uniformNatRead word
  let (ws,suffix) ← bitFramesRead n rest
  if suffix = [] then some ws else none

theorem bitFieldsDecode_encode (ws : List (List Bool)) :
    bitFieldsDecode (bitFieldsEncode ws) = some ws := by
  have hf := bitFramesRead_encode ws []
  simp only [List.append_nil] at hf
  simp [bitFieldsDecode,bitFieldsEncode,uniformNatRead_encode,hf]

theorem bitFieldsDecode_exact (word : List Bool) (ws : List (List Bool))
    (h : bitFieldsDecode word = some ws) : word = bitFieldsEncode ws := by
  unfold bitFieldsDecode at h
  cases hn : uniformNatRead word with
  | none => simp [hn] at h
  | some pair =>
    rcases pair with ⟨n,rest⟩
    simp only [hn] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases hr : bitFramesRead n rest with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨fields,suffix⟩
      simp only [hr] at h
      split at h
      · rename_i hs
        subst suffix
        cases Option.some.inj h
        obtain ⟨hlen,hrest⟩ := bitFramesRead_exact n rest _ [] hr
        simpa only [bitFieldsEncode,hlen,List.append_nil,hrest] using
          uniformNatRead_exact word n rest hn
      · cases h

theorem bitFieldsEncode_length (ws : List (List Bool)) :
    (bitFieldsEncode ws).length = 2*ws.length.size+1+
      (ws.map (fun w => 2*w.length.size+1+w.length)).sum := by
  have hf : (bitFramesEncode ws).length =
      (ws.map (fun w => 2*w.length.size+1+w.length)).sum := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [bitFramesEncode,uniformNatEncode_length,ih,Nat.add_assoc]
  simp only [bitFieldsEncode,List.length_append,uniformNatEncode_length,hf]

theorem bitFieldsEncode_length_le (ws : List (List Bool)) (L : Nat)
    (h : ∀ w ∈ ws, w.length ≤ L) :
    (bitFieldsEncode ws).length ≤ 2*ws.length.size+1+ws.length*(2*L.size+1+L) := by
  rw [bitFieldsEncode_length]
  suffices hs : (ws.map (fun w => 2*w.length.size+1+w.length)).sum ≤
      ws.length*(2*L.size+1+L) by omega
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := h w (by simp)
    have hb := Nat.size_le_size hw
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.add_mul,one_mul]
    omega

/-- An executable codec with independently discharged canonicality laws. -/
structure BitRecordCodec (A : Type) where
  encode : A → List Bool
  decode : List Bool → Option A
  roundTrip : ∀ x, decode (encode x) = some x
  exact : ∀ word x, decode word = some x → word = encode x

namespace BitRecordCodec
variable {A B : Type}

theorem injective (c : BitRecordCodec A) : Function.Injective c.encode := by
  intro x y h
  have he := congrArg c.decode h
  rw [c.roundTrip,c.roundTrip] at he
  exact Option.some.inj he

private theorem mapM_roundTrip (c : BitRecordCodec A) (xs : List A) :
    (xs.map c.encode).mapM c.decode = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons,c.roundTrip,ih]

private theorem mapM_exact (c : BitRecordCodec A) (ws : List (List Bool)) (xs : List A)
    (h : ws.mapM c.decode = some xs) : ws = xs.map c.encode := by
  induction ws generalizing xs with
  | nil => cases Option.some.inj h; rfl
  | cons w ws ih =>
    simp only [List.mapM_cons] at h
    cases hd : c.decode w with
    | none => simp [hd] at h
    | some x =>
      simp only [hd] at h
      cases ht : ws.mapM c.decode with
      | none => simp [ht] at h
      | some tail =>
        simp only [ht] at h
        cases Option.some.inj h
        simp only [List.map_cons,c.exact w x hd,ih tail ht]

/-- Ordered lists retain every field and require full input consumption. -/
def list (c : BitRecordCodec A) : BitRecordCodec (List A) where
  encode xs := bitFieldsEncode (xs.map c.encode)
  decode word := do
    let ws ← bitFieldsDecode word
    ws.mapM c.decode
  roundTrip xs := by
    rw [bitFieldsDecode_encode]
    exact mapM_roundTrip c xs
  exact word xs h := by
    cases hf : bitFieldsDecode word with
    | none => simp [hf] at h
    | some ws =>
      simp only [hf] at h
      have hm := mapM_exact c ws xs h
      rw [bitFieldsDecode_exact word ws hf,hm]

/-- A pair has exactly two framed fields. -/
def pair (c : BitRecordCodec A) (d : BitRecordCodec B) : BitRecordCodec (A × B) where
  encode x := bitFieldsEncode [c.encode x.1,d.encode x.2]
  decode word := match bitFieldsDecode word with
    | some [wa,wb] => do
      let a ← c.decode wa
      let b ← d.decode wb
      some (a,b)
    | _ => none
  roundTrip x := by simp [bitFieldsDecode_encode,c.roundTrip,d.roundTrip]
  exact word x h := by
    split at h
    · rename_i wa wb hf
      cases ha : c.decode wa with
      | none => simp [ha] at h
      | some a =>
        simp only [ha] at h
        cases hb : d.decode wb with
        | none => simp [hb] at h
        | some b =>
          simp only [hb] at h
          cases Option.some.inj h
          rw [bitFieldsDecode_exact word [wa,wb] hf,c.exact wa a ha,d.exact wb b hb]
    · cases h

/-- Transport only across an explicit computable equivalence. -/
def equiv (c : BitRecordCodec A) (e : A ≃ B) : BitRecordCodec B where
  encode x := c.encode (e.symm x)
  decode word := (c.decode word).map e
  roundTrip x := by simp [c.roundTrip]
  exact word x h := by
    obtain ⟨a,ha,hx⟩ := Option.map_eq_some_iff.mp h
    subst x
    simpa using c.exact word a ha

/-- Restrict an existing canonical representation by an executable invariant.
Used for exact key arity and unique cache keys; no entries are discarded. -/
def subtype (c : BitRecordCodec A) (P : A → Prop) [DecidablePred P] :
    BitRecordCodec {x : A // P x} where
  encode x := c.encode x.val
  decode word := do
    let x ← c.decode word
    if h : P x then some ⟨x,h⟩ else none
  roundTrip x := by simp [c.roundTrip,x.property]
  exact word x h := by
    cases hd : c.decode word with
    | none => simp [hd] at h
    | some y =>
      simp only [hd] at h
      dsimp only [Bind.bind,Option.bind] at h
      split at h
      · cases Option.some.inj h
        exact c.exact word y hd
      · cases h

#print axioms injective
end BitRecordCodec
#print axioms bitFieldsDecode_encode
#print axioms bitFieldsDecode_exact
#print axioms bitFieldsEncode_length
#print axioms bitFieldsEncode_length_le
end ExplainableCrypto.Helios.Computational
