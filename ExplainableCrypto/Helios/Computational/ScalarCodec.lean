import ExplainableCrypto.Helios.Computational.UniformOperandCodec
import Mathlib.Data.ZMod.Basic

/-! Canonical historical scalar records. Values at or above the modulus reject;
the decoder does not silently reduce malformed input modulo q. -/
namespace ExplainableCrypto.Helios.Computational
variable {q : Nat} [NeZero q]

def scalarEncode (a : ZMod q) : List Bool := uniformNatEncode a.val

def scalarDecode (q : Nat) (word : List Bool) : Option (ZMod q) := do
  let (n,suffix) ← uniformNatRead word
  if suffix = [] ∧ n < q then some (n : ZMod q) else none

theorem scalarDecode_encode (a : ZMod q) : scalarDecode q (scalarEncode a) = some a := by
  have hr := uniformNatRead_encode a.val []
  simp only [List.append_nil] at hr
  simp [scalarDecode,scalarEncode,hr,a.val_lt]

omit [NeZero q] in
/-- Accepted scalar input is exactly its canonical record; out-of-range
naturals cannot masquerade as a smaller residue. -/
theorem scalarDecode_exact (word : List Bool) (a : ZMod q)
    (h : scalarDecode q word = some a) : word = scalarEncode a := by
  unfold scalarDecode at h
  cases hr : uniformNatRead word with
  | none => simp [hr] at h
  | some p =>
    rcases p with ⟨n,suffix⟩
    simp only [hr] at h
    dsimp only [Bind.bind,Option.bind] at h
    split at h
    · rename_i hc
      rcases hc with ⟨rfl,hn⟩
      cases Option.some.inj h
      have he := uniformNatRead_exact word n [] hr
      simpa only [scalarEncode,ZMod.val_natCast_of_lt hn,List.append_nil] using he
    · cases h

omit [NeZero q] in
theorem scalarEncode_length (a : ZMod q) : (scalarEncode a).length = 2*a.val.size+1 :=
  uniformNatEncode_length _

/-- Concrete encoded scalar size is bounded by the modulus width. -/
theorem scalarEncode_length_le (a : ZMod q) :
    (scalarEncode a).length ≤ 2*(q-1).size+1 := by
  rw [scalarEncode_length]
  have h := Nat.size_le_size (show a.val ≤ q-1 by have := a.val_lt; omega)
  omega

#print axioms scalarDecode_encode
#print axioms scalarDecode_exact
#print axioms scalarEncode_length
#print axioms scalarEncode_length_le
end ExplainableCrypto.Helios.Computational
