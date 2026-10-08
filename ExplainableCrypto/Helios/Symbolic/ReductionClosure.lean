import ExplainableCrypto.Helios.Symbolic.Rewriting

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

namespace Context

def compose (outer inner : Context V) : Context V :=
  match outer with
  | .hole => inner
  | .unary f c => .unary f (c.compose inner)
  | .binaryLeft f c b => .binaryLeft f (c.compose inner) b
  | .binaryRight f a c => .binaryRight f a (c.compose inner)
  | .ternaryFirst f c b d => .ternaryFirst f (c.compose inner) b d
  | .ternarySecond f a c d => .ternarySecond f a (c.compose inner) d
  | .ternaryThird f a b c => .ternaryThird f a b (c.compose inner)
  | .spkFirst c b d e => .spkFirst (c.compose inner) b d e
  | .spkSecond a c d e => .spkSecond a (c.compose inner) d e
  | .spkThird a b c e => .spkThird a b (c.compose inner) e
  | .spkFourth a b d c => .spkFourth a b d (c.compose inner)

@[simp] theorem fill_compose (outer inner : Context V) (t : Term V) :
    (outer.compose inner).fill t = outer.fill (inner.fill t) := by
  induction outer <;> simp_all [compose, fill]

theorem base_congr (c : Context V) {a b : Term V} (h : BaseEq a b) :
    BaseEq (c.fill a) (c.fill b) := by
  induction c with
  | hole => exact h
  | unary f c ih => exact .unary f ih
  | binaryLeft f c b ih => exact .binary f ih (.refl _)
  | binaryRight f a c ih => exact .binary f (.refl _) ih
  | ternaryFirst f c b d ih => exact .ternary f ih (.refl _) (.refl _)
  | ternarySecond f a c d ih => exact .ternary f (.refl _) ih (.refl _)
  | ternaryThird f a b c ih => exact .ternary f (.refl _) (.refl _) ih
  | spkFirst c b d e ih => exact .spk ih (.refl _) (.refl _) (.refl _)
  | spkSecond a c d e ih => exact .spk (.refl _) ih (.refl _) (.refl _)
  | spkThird a b c e ih => exact .spk (.refl _) (.refl _) ih (.refl _)
  | spkFourth a b d c ih => exact .spk (.refl _) (.refl _) (.refl _) ih

end Context

theorem RewriteStep.context {a b : Term V} (h : RewriteStep a b) (c : Context V) :
    RewriteStep (c.fill a) (c.fill b) := by
  obtain ⟨d, l, r, hr, rfl, rfl⟩ := h
  exact ⟨c.compose d, l, r, hr, (c.fill_compose d l).symm, (c.fill_compose d r).symm⟩

theorem ModuloStep.context {a b : Term V} (h : ModuloStep a b) (c : Context V) :
    ModuloStep (c.fill a) (c.fill b) := by
  obtain ⟨a', b', ha, hr, hb⟩ := h
  exact ⟨c.fill a', c.fill b', c.base_congr ha, hr.context c, c.base_congr hb⟩

theorem ModuloStep.pre_base {a a' b : Term V} (h : ModuloStep a b) (he : BaseEq a' a) :
    ModuloStep a' b := by
  obtain ⟨x, y, hx, hr, hy⟩ := h
  exact ⟨x, y, he.trans hx, hr, hy⟩

theorem ModuloStep.post_base {a b b' : Term V} (h : ModuloStep a b) (he : BaseEq b b') :
    ModuloStep a b' := by
  obtain ⟨x, y, hx, hr, hy⟩ := h
  exact ⟨x, y, hx, hr, hy.trans he⟩

theorem RootStep.to_modulo {a b : Term V} (h : RootStep a b) : ModuloStep a b :=
  ⟨a, b, .refl _, ⟨.hole, a, b, h, rfl, rfl⟩, .refl _⟩

/-- Zero or more oriented reductions with an E0 equality at the endpoint.
Unlike `Reduces`, the zero-step case can change the E0 representative. -/
inductive ReducesModulo : Term V → Term V → Prop where
  | base {a b} : BaseEq a b → ReducesModulo a b
  | head {a b c} : ModuloStep a b → ReducesModulo b c → ReducesModulo a c

namespace ReducesModulo

theorem refl (a : Term V) : ReducesModulo a a := .base (.refl a)

theorem single {a b : Term V} (h : ModuloStep a b) : ReducesModulo a b := .head h (.refl b)

theorem pre_base {a a' b : Term V} (h : ReducesModulo a b) (he : BaseEq a' a) :
    ReducesModulo a' b := by
  cases h with
  | base h => exact .base (he.trans h)
  | head h hr => exact .head (h.pre_base he) hr

theorem trans {a b c : Term V} (h : ReducesModulo a b) (h' : ReducesModulo b c) :
    ReducesModulo a c := by
  induction h with
  | base he => exact h'.pre_base he
  | head hs _ ih => exact .head hs (ih h')

theorem post_base {a b b' : Term V} (h : ReducesModulo a b) (he : BaseEq b b') :
    ReducesModulo a b' := h.trans (.base he)

theorem context {a b : Term V} (h : ReducesModulo a b) (c : Context V) :
    ReducesModulo (c.fill a) (c.fill b) := by
  induction h with
  | base he => exact .base (c.base_congr he)
  | head hs _ ih => exact .head (hs.context c) ih

theorem sound {a b : Term V} (h : ReducesModulo a b) : EqE a b := by
  induction h with
  | base he => exact he.sound
  | head hs _ ih => exact hs.sound.trans ih

theorem weight_le {a b : Term V} (h : ReducesModulo a b) : b.cryptoWeight ≤ a.cryptoWeight := by
  induction h with
  | base he => exact Nat.le_of_eq he.weight_eq.symm
  | head hs _ ih => exact Nat.le_trans ih (Nat.le_of_lt hs.weight_lt)

end ReducesModulo

theorem Reduces.to_modulo {a b : Term V} (h : Reduces a b) : ReducesModulo a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans (.single hs)

theorem Irreducible.base {a b : Term V} (h : Irreducible a) (he : BaseEq a b) :
    Irreducible b := by
  intro c hc
  exact h c (hc.pre_base he)

theorem Irreducible.reducesModulo {a b : Term V} (h : Irreducible a)
    (hr : ReducesModulo a b) : BaseEq a b := by
  cases hr with
  | base he => exact he
  | head hs _ => exact False.elim (h _ hs)

end ExplainableCrypto.Helios.Symbolic
