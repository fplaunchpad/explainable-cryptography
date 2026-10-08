import ExplainableCrypto.Helios.Computational.BallotFiniteLogged

/-! Fixed field layout for full hash keys. This packs group elements, not bits;
it does not provide a primitive group codec or a machine-cost certificate. -/
namespace ExplainableCrypto.Helios.Computational
variable {F G : Type}

/-- Generator, public key, ciphertext pair, then the two commitment pairs. -/
def ballotKeyRecord (key : BallotForkPoint G) : List G :=
  [key.1.generator,key.1.publicKey,key.1.ciphertext.1,key.1.ciphertext.2,
    key.2.1.1,key.2.1.2,key.2.2.1,key.2.2.2]

def ballotKeyOfRecord : List G → Option (BallotForkPoint G)
  | [g,pk,c0,c1,a0,b0,a1,b1] => some (⟨g,pk,(c0,c1)⟩,((a0,b0),(a1,b1)))
  | _ => none

theorem ballotKeyRecord_length (key : BallotForkPoint G) : (ballotKeyRecord key).length = 8 := rfl

theorem ballotKeyOfRecord_roundTrip (key : BallotForkPoint G) :
    ballotKeyOfRecord (ballotKeyRecord key) = some key := by
  rcases key with ⟨⟨g,pk,c0,c1⟩,⟨a0,b0⟩,⟨a1,b1⟩⟩
  rfl

/-- A successfully decoded record is exactly the full record of that key. -/
theorem ballotKeyOfRecord_exact (record : List G) (key : BallotForkPoint G)
    (h : ballotKeyOfRecord record = some key) : record = ballotKeyRecord key := by
  unfold ballotKeyOfRecord at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

theorem ballotKeyRecord_injective : Function.Injective (ballotKeyRecord (G := G)) := by
  intro x y h
  have hd := congrArg ballotKeyOfRecord h
  rw [ballotKeyOfRecord_roundTrip,ballotKeyOfRecord_roundTrip] at hd
  exact Option.some.inj hd

theorem ballotKeyOfRecord_wrong_length (record : List G) (h : record.length ≠ 8) :
    ballotKeyOfRecord record = none := by
  cases hd : ballotKeyOfRecord record with
  | none => rfl
  | some key =>
    have he := ballotKeyOfRecord_exact record key hd
    subst record
    exact (h (ballotKeyRecord_length key)).elim

/-- Group-element projection of the actual finite cache keys and chronological
log keys. Cache values are retained in the separate scalar projection below. -/
def ballotLoggedGroupRecord (s : BallotFiniteLoggedState F G) : List G :=
  s.1.entries.flatMap (fun entry => ballotKeyRecord entry.1) ++
    s.2.flatMap (fun entry => ballotKeyRecord entry.2)

def ballotLoggedScalarRecord (s : BallotFiniteLoggedState F G) : List F :=
  s.1.entries.map (fun entry => entry.2)

private theorem packed_length {X : Type} (xs : List X) (key : X → BallotForkPoint G) :
    (xs.flatMap (fun x => ballotKeyRecord (key x))).length = 8*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,ballotKeyRecord_length,ih,List.length_cons]
    omega

/-- Exact number of group-element cells in the concrete key-record projection. -/
theorem ballotLoggedGroupRecord_length (s : BallotFiniteLoggedState F G) :
    (ballotLoggedGroupRecord s).length = 8*(s.1.entries.length+s.2.length) := by
  simp only [ballotLoggedGroupRecord,List.length_append,packed_length,Nat.mul_add]

theorem ballotLoggedScalarRecord_length (s : BallotFiniteLoggedState F G) :
    (ballotLoggedScalarRecord s).length = s.1.entries.length := by
  simp only [ballotLoggedScalarRecord,List.length_map]

#print axioms ballotKeyRecord_length
#print axioms ballotKeyOfRecord_roundTrip
#print axioms ballotKeyOfRecord_exact
#print axioms ballotKeyRecord_injective
#print axioms ballotKeyOfRecord_wrong_length
#print axioms ballotLoggedGroupRecord_length
#print axioms ballotLoggedScalarRecord_length
end ExplainableCrypto.Helios.Computational
