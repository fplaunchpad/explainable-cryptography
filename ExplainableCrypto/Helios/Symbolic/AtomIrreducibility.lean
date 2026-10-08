import ExplainableCrypto.Helios.Symbolic.UnaryLocalConfluence
import ExplainableCrypto.Helios.Symbolic.RewriteSPOT

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem BaseEq.name_shape {n : Nat} {t : Term V} (h : BaseEq (.name n) t) : t = .name n := by
  have hh := h.head_eq
  cases t with
  | name m => exact congrArg Term.name (HeadTag.name.inj hh).symm
  | var => cases hh
  | const c => cases c <;> cases hh
  | unary => cases hh
  | binary f => cases f <;> cases hh
  | ternary => cases hh
  | spk => cases hh

theorem BaseEq.var_shape {v : V} {t : Term V} (h : BaseEq (.var v) t) : t = .var v := by
  have hh := h.head_eq
  cases t with
  | name => cases hh
  | var w => exact congrArg Term.var (HeadTag.var.inj hh).symm
  | const c => cases c <;> cases hh
  | unary => cases hh
  | binary f => cases f <;> cases hh
  | ternary => cases hh
  | spk => cases hh

theorem RewriteStep.not_name {n : Nat} {t : Term V} : ¬ RewriteStep (.name n) t := by
  rintro ⟨c, l, r, hr, hs, _⟩
  cases c with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    cases hr
  | _ => cases hs

theorem RewriteStep.not_var {v : V} {t : Term V} : ¬ RewriteStep (.var v) t := by
  rintro ⟨c, l, r, hr, hs, _⟩
  cases c with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    cases hr
  | _ => cases hs

theorem name_irreducible (n : Nat) : Irreducible (Term.name (V := V) n) := by
  rintro t ⟨a, b, ha, hab, _⟩
  have he := ha.name_shape
  subst a
  exact RewriteStep.not_name hab

theorem var_irreducible (v : V) : Irreducible (Term.var v) := by
  rintro t ⟨a, b, ha, hab, _⟩
  have he := ha.var_shape
  subst a
  exact RewriteStep.not_var hab

/-- Atomic base cases have no peaks. Nontrivial projection controls separately
exercise the constructor implications on sources with competing reductions. -/
theorem Irreducible.locally_confluent_at {a : Term V} (h : Irreducible a) : LocallyConfluentAt a :=
  fun b _ hab _ => False.elim (h b hab)

end ExplainableCrypto.Helios.Symbolic
