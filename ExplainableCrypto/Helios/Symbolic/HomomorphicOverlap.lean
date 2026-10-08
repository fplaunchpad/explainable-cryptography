import ExplainableCrypto.Helios.Symbolic.Confluence
import ExplainableCrypto.Helios.Symbolic.RewriteSPOT

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

abbrev cipher (k r m : Term V) := Term.ternary .penc k r m

def tripleSource (k r s t m n p : Term V) : Term V :=
  .binary .mul (.binary .mul (cipher k r m) (cipher k s n)) (cipher k t p)

def tripleLeft (k r s t m n p : Term V) : Term V :=
  .binary .mul (cipher k (.binary .compose r s) (.binary .add m n)) (cipher k t p)

def tripleRight (k r s t m n p : Term V) : Term V :=
  .binary .mul (cipher k r m) (cipher k (.binary .compose s t) (.binary .add n p))

def tripleFinalLeft (k r s t m n p : Term V) : Term V :=
  cipher k (.binary .compose (.binary .compose r s) t) (.binary .add (.binary .add m n) p)

def tripleFinal (k r s t m n p : Term V) : Term V :=
  cipher k (.binary .compose r (.binary .compose s t)) (.binary .add m (.binary .add n p))

theorem triple_left_step (k r s t m n p : Term V) :
    ModuloStep (tripleSource k r s t m n p) (tripleLeft k r s t m n p) :=
  (RootStep.homomorphic k r s m n).to_modulo.context
    (.binaryLeft .mul .hole (cipher k t p))

theorem triple_right_step (k r s t m n p : Term V) :
    ModuloStep (tripleSource k r s t m n p) (tripleRight k r s t m n p) :=
  ((RootStep.homomorphic k s t n p).to_modulo.context
    (.binaryRight .mul (cipher k r m) .hole)).pre_base
      (.equation (.assoc .mul trivial (cipher k r m) (cipher k s n) (cipher k t p)))

theorem triple_endpoints_base (k r s t m n p : Term V) :
    BaseEq (tripleFinalLeft k r s t m n p) (tripleFinal k r s t m n p) :=
  .ternary .penc (.refl _) (.equation (.assoc .compose trivial r s t))
    (.equation (.assoc .add trivial m n p))

/-- An unconditional join for the homomorphic three-ciphertext overlap. -/
theorem triple_join (k r s t m n p : Term V) :
    JoinModulo (tripleLeft k r s t m n p) (tripleRight k r s t m n p) := by
  refine ⟨tripleFinal k r s t m n p, ?_, ?_⟩
  · exact .single ((RootStep.homomorphic k (.binary .compose r s) t
      (.binary .add m n) p).to_modulo.post_base (triple_endpoints_base k r s t m n p))
  · exact .single (RootStep.homomorphic k r (.binary .compose s t)
      m (.binary .add n p)).to_modulo

/-- Both branches are reachable from the same term, not merely equal in E. -/
theorem triple_peak_joined (k r s t m n p : Term V) :
    ModuloStep (tripleSource k r s t m n p) (tripleLeft k r s t m n p) ∧
    ModuloStep (tripleSource k r s t m n p) (tripleRight k r s t m n p) ∧
    JoinModulo (tripleLeft k r s t m n p) (tripleRight k r s t m n p) :=
  ⟨triple_left_step k r s t m n p, triple_right_step k r s t m n p,
    triple_join k r s t m n p⟩

/-- Counterexample retained from the raw-endpoint equality campaign. -/
theorem triple_raw_endpoints_differ :
    tripleFinalLeft (.name 0) (.name 1) (.name 2) (.name 3)
      (.const .zero) (.const .one) (.const .zero) ≠
    tripleFinal (V := Nat) (.name 0) (.name 1) (.name 2) (.name 3)
      (.const .zero) (.const .one) (.const .zero) := by decide

theorem Irreducible.reduces_eq {a b : Term V} (ha : Irreducible a) (h : Reduces a b) : a = b := by
  rcases h.cases_head with he | ⟨c, hs, _⟩
  · exact he
  · exact False.elim (ha c hs)

/-- Raw syntactic confluence is actually false for our modulo-step presentation:
terminal E0 representatives need not be identical. This does not refute confluence modulo E0. -/
theorem raw_confluence_false :
    ∃ s a b : Term Nat, ModuloStep s a ∧ ModuloStep s b ∧
      ¬ (∃ c, Reduces a c ∧ Reduces b c) := by
  let z : Term Nat := .const .zero
  let zz : Term Nat := .binary .add z z
  let start : Term Nat := .unary .fst (.binary .pair z (.const .one))
  have hs : ModuloStep start z := (RootStep.fst z (.const .one)).to_modulo
  refine ⟨start, z, zz, hs, hs.post_base (BaseEq.equation BaseEquation.zero_zero).symm, ?_⟩
  rintro ⟨c, hz, hzz⟩
  have he := (constant_irreducible .zero).reduces_eq hz
  have he' := (zero_weight_irreducible zz rfl).reduces_eq hzz
  have hn : z ≠ zz := by decide
  exact hn (he.trans he'.symm)

end ExplainableCrypto.Helios.Symbolic
