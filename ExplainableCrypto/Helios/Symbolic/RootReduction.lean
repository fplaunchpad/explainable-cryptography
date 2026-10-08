import ExplainableCrypto.Helios.Symbolic.Rewriting

/-! Executable, proof-producing root matching. It matches raw syntax and does not
search modulo E0 or descend through contexts, so `none` is not irreducibility. -/
namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} [DecidableEq V]

/-- Every returned reduction carries a kernel-checkable instance of a source rule. -/
def rootReduce (t : Term V) : Option {u : Term V // RootStep t u} :=
  match t with
  | .unary .fst (.binary .pair a b) => some ⟨a, .fst a b⟩
  | .unary .snd (.binary .pair a b) => some ⟨b, .snd a b⟩
  | .binary .dec k (.ternary .penc (.unary .pk sk) r m) =>
    if h : k = sk then
      some ⟨m, by subst k; exact .decrypt sk r m⟩
    else
      match k with
      | .binary .partialDecrypt sk' c =>
        if hs : sk' = sk then
          if hc : c = .ternary .penc (.unary .pk sk) r m then
            some ⟨m, by subst sk'; subst c; exact .partial_decrypt sk r m⟩
          else none
        else none
      | _ => none
  | .binary .mul (.ternary .penc k r m) (.ternary .penc k' s n) =>
    if h : k' = k then
      some ⟨.ternary .penc k (.binary .compose r s) (.binary .add m n),
        by subst k'; exact .homomorphic k r s m n⟩
    else none
  | .ternary .checkspk k (.ternary .penc k' r m) (.spk k'' r' m' c) =>
    if hk : k' = k then
      if hk' : k'' = k then
        if hr : r' = r then
          if hm : m' = m then
            if hc : c = .ternary .penc k r m then
              match m with
              | .const .zero => some ⟨.const .ok, by
                  subst k'; subst k''; subst r'; subst m'; subst c
                  exact .check_zero k r⟩
              | .const .one => some ⟨.const .ok, by
                  subst k'; subst k''; subst r'; subst m'; subst c
                  exact .check_one k r⟩
              | _ => none
            else none
          else none
        else none
      else none
    else none
  | _ => none

/-- Connect the executable output to a rule instance independently of its proof field. -/
theorem rootReduce_sound (t r : Term V)
    (h : (rootReduce t).map Subtype.val = some r) : RootStep t r := by
  cases hc : rootReduce t with
  | none => simp [hc] at h
  | some u =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    exact h ▸ u.property

/-- Every raw root-rule instance is recognised; no matching modulo E0 is claimed. -/
theorem rootReduce_complete {t r : Term V} (h : RootStep t r) :
    (rootReduce t).map Subtype.val = some r := by
  cases h <;> simp [rootReduce]
  split <;> simp_all

/-- Both equational soundness and progress hold for every successful output. -/
theorem rootReduce_correct (t r : Term V)
    (h : (rootReduce t).map Subtype.val = some r) :
    EqE t r ∧ r.cryptoWeight < t.cryptoWeight :=
  ⟨(rootReduce_sound t r h).sound, (rootReduce_sound t r h).weight_lt⟩

end ExplainableCrypto.Helios.Symbolic
