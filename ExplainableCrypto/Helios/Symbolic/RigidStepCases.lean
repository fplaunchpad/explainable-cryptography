import ExplainableCrypto.Helios.Symbolic.CiphertextLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- One rule at the root, allowing E0 representatives before and after the rule.
Contextual steps are still represented by the broader `ModuloStep`. -/
def RootModuloStep (a b : Term V) : Prop :=
  ∃ l r, BaseEq a l ∧ RootStep l r ∧ BaseEq r b

theorem RootModuloStep.to_modulo {a b : Term V} (h : RootModuloStep a b) : ModuloStep a b := by
  obtain ⟨l, r, hl, hr, hb⟩ := h
  exact (hr.to_modulo.pre_base hl).post_base hb

theorem RootModuloStep.outputs_base {a b c : Term V}
    (hb : RootModuloStep a b) (hc : RootModuloStep a c) : BaseEq b c := by
  obtain ⟨l, r, hal, hlr, hrb⟩ := hb
  obtain ⟨l', r', hal', hlr', hrc⟩ := hc
  exact hrb.symm.trans ((root_outputs_base hlr hlr' (hal.symm.trans hal')).trans hrc)

theorem BaseEq.unary_shape {f : Unary} {a t : Term V} (h : BaseEq (.unary f a) t) :
    ∃ a', t = .unary f a' ∧ BaseEq a a' := by
  have hh := h.head_eq
  cases t with
  | name => cases hh
  | var => cases hh
  | const c => cases c <;> cases hh
  | unary g a' =>
    obtain ⟨rfl, ha⟩ := (BaseEq.unary_iff f g a a').mp h
    exact ⟨a', rfl, ha⟩
  | binary g => cases g <;> cases hh
  | ternary => cases hh
  | spk => cases hh

/-- Fixed binary arguments retain order; this excludes all three AC symbols. -/
theorem BaseEq.rigid_binary_shape {f : Binary} (hf : ¬ AC f) {a b t : Term V}
    (h : BaseEq (.binary f a b) t) :
    ∃ a' b', t = .binary f a' b' ∧ BaseEq a a' ∧ BaseEq b b' := by
  have hh := h.head_eq
  cases t with
  | binary g a' b' =>
    have hfg : f = g := by cases f <;> cases g <;> simp_all [AC, Term.headTag]
    subst g
    obtain ⟨_, ha, hb⟩ := (BaseEq.binary_iff f f hf hf a b a' b').mp h
    exact ⟨a', b', rfl, ha, hb⟩
  | const c => cases c <;> cases f <;> simp_all [AC, Term.headTag]
  | _ => cases f <;> simp_all [AC, Term.headTag]

/-- Raw unary contexts expose either the root rule or one argument step. -/
theorem RewriteStep.unary_cases {f : Unary} {a t : Term V}
    (h : RewriteStep (.unary f a) t) :
    RootStep (.unary f a) t ∨ ∃ a', RewriteStep a a' ∧ t = .unary f a' := by
  obtain ⟨c, l, r, hr, hs, rfl⟩ := h
  cases c with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    exact Or.inl hr
  | unary g c =>
    simp only [Context.fill, Term.unary.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inr ⟨c.fill r, ⟨c, l, r, hr, rfl, rfl⟩, rfl⟩
  | _ => cases hs

/-- Raw binary contexts expose the root or one of the two ordered arguments. -/
theorem RewriteStep.binary_cases {f : Binary} {a b t : Term V}
    (h : RewriteStep (.binary f a b) t) :
    RootStep (.binary f a b) t ∨
    (∃ a', RewriteStep a a' ∧ t = .binary f a' b) ∨
    (∃ b', RewriteStep b b' ∧ t = .binary f a b') := by
  obtain ⟨c, l, r, hr, hs, rfl⟩ := h
  cases c with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    exact Or.inl hr
  | binaryLeft g c d =>
    simp only [Context.fill, Term.binary.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inl ⟨c.fill r, ⟨c, l, r, hr, rfl, rfl⟩, rfl⟩)
  | binaryRight g d c =>
    simp only [Context.fill, Term.binary.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr ⟨c.fill r, ⟨c, l, r, hr, rfl, rfl⟩, rfl⟩)
  | _ => cases hs

/-- Unary inversion covers arbitrary E0 representatives, including the target. -/
theorem ModuloStep.unary_cases {f : Unary} {a t : Term V}
    (h : ModuloStep (.unary f a) t) :
    RootModuloStep (.unary f a) t ∨
      ∃ a', ModuloStep a a' ∧ BaseEq t (.unary f a') := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  obtain ⟨a₀, rfl, ha⟩ := hx.unary_shape
  rcases hxy.unary_cases with hr | ⟨a', hs, rfl⟩
  · exact Or.inl ⟨_, _, hx, hr, hy⟩
  · exact Or.inr ⟨a', ⟨a₀, a', ha, hs, .refl _⟩, hy.symm⟩

/-- Non-AC binary inversion, including active decryption roots. -/
theorem ModuloStep.rigid_binary_cases {f : Binary} (hf : ¬ AC f) {a b t : Term V}
    (h : ModuloStep (.binary f a b) t) :
    RootModuloStep (.binary f a b) t ∨
    (∃ a', ModuloStep a a' ∧ BaseEq t (.binary f a' b)) ∨
    (∃ b', ModuloStep b b' ∧ BaseEq t (.binary f a b') ) := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  obtain ⟨a₀, b₀, rfl, ha, hb⟩ := hx.rigid_binary_shape hf
  rcases hxy.binary_cases with hr | ⟨a', hs, rfl⟩ | ⟨b', hs, rfl⟩
  · exact Or.inl ⟨_, _, hx, hr, hy⟩
  · exact Or.inr (Or.inl ⟨a', ⟨a₀, a', ha, hs, .refl _⟩,
      hy.symm.trans (.binary f (.refl _) hb.symm)⟩)
  · exact Or.inr (Or.inr ⟨b', ⟨b₀, b', hb, hs, .refl _⟩,
      hy.symm.trans (.binary f ha.symm (.refl _))⟩)

/-- Pairing and partial-decryption construction do not themselves reduce at the root. -/
theorem RootModuloStep.not_passive_binary {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {a b t : Term V} : ¬ RootModuloStep (.binary f a b) t := by
  rintro ⟨l, r, he, hr, _⟩
  have hh := he.head_eq
  rcases hf with rfl | rfl <;> cases hr <;> cases hh

theorem ModuloStep.passive_binary_cases {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {a b t : Term V} (h : ModuloStep (.binary f a b) t) :
    (∃ a', ModuloStep a a' ∧ BaseEq t (.binary f a' b)) ∨
    (∃ b', ModuloStep b b' ∧ BaseEq t (.binary f a b')) := by
  have hn : ¬ AC f := by rcases hf with rfl | rfl <;> simp [AC]
  rcases h.rigid_binary_cases hn with hroot | hinner
  · exact False.elim (RootModuloStep.not_passive_binary hf hroot)
  · exact hinner

end ExplainableCrypto.Helios.Symbolic
