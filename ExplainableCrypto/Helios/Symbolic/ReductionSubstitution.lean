import ExplainableCrypto.Helios.Symbolic.ReductionClosure

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

namespace ReducesModulo

theorem unary (f) {a a' : Term V} (ha : ReducesModulo a a') :
    ReducesModulo (.unary f a) (.unary f a') := ha.context (.unary f .hole)

theorem binary (f) {a a' b b' : Term V}
    (ha : ReducesModulo a a') (hb : ReducesModulo b b') :
    ReducesModulo (.binary f a b) (.binary f a' b') :=
  (ha.context (.binaryLeft f .hole b)).trans (hb.context (.binaryRight f a' .hole))

theorem ternary (f) {a a' b b' c c' : Term V}
    (ha : ReducesModulo a a') (hb : ReducesModulo b b') (hc : ReducesModulo c c') :
    ReducesModulo (.ternary f a b c) (.ternary f a' b' c') :=
  ((ha.context (.ternaryFirst f .hole b c)).trans
    (hb.context (.ternarySecond f a' .hole c))).trans
      (hc.context (.ternaryThird f a' b' .hole))

theorem spk {a a' b b' c c' d d' : Term V}
    (ha : ReducesModulo a a') (hb : ReducesModulo b b')
    (hc : ReducesModulo c c') (hd : ReducesModulo d d') :
    ReducesModulo (.spk a b c d) (.spk a' b' c' d') :=
  (((ha.context (.spkFirst .hole b c d)).trans
    (hb.context (.spkSecond a' .hole c d))).trans
      (hc.context (.spkThird a' b' .hole d))).trans
        (hd.context (.spkFourth a' b' c' .hole))

/-- Each occurrence follows the supplied reduction, including repeated variables. -/
theorem subst_congr {σ τ : V → Term W} (h : ∀ v, ReducesModulo (σ v) (τ v))
    (t : Term V) : ReducesModulo (t.subst σ) (t.subst τ) := by
  induction t with
  | name => exact .refl _
  | var v => exact h v
  | const => exact .refl _
  | unary f _ ih => exact .unary f ih
  | binary f _ _ ih₁ ih₂ => exact .binary f ih₁ ih₂
  | ternary f _ _ _ ih₁ ih₂ ih₃ => exact .ternary f ih₁ ih₂ ih₃
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ => exact .spk ih₁ ih₂ ih₃ ih₄

end ReducesModulo

theorem RootStep.subst {l r : Term V} (h : RootStep l r) (σ : V → Term W) :
    RootStep (l.subst σ) (r.subst σ) := by
  cases h <;> simp only [Term.subst] <;> constructor

namespace Context

def subst (σ : V → Term W) : Context V → Context W
  | .hole => .hole
  | .unary f c => .unary f (c.subst σ)
  | .binaryLeft f c b => .binaryLeft f (c.subst σ) (b.subst σ)
  | .binaryRight f a c => .binaryRight f (a.subst σ) (c.subst σ)
  | .ternaryFirst f c b d => .ternaryFirst f (c.subst σ) (b.subst σ) (d.subst σ)
  | .ternarySecond f a c d => .ternarySecond f (a.subst σ) (c.subst σ) (d.subst σ)
  | .ternaryThird f a b c => .ternaryThird f (a.subst σ) (b.subst σ) (c.subst σ)
  | .spkFirst c b d e => .spkFirst (c.subst σ) (b.subst σ) (d.subst σ) (e.subst σ)
  | .spkSecond a c d e => .spkSecond (a.subst σ) (c.subst σ) (d.subst σ) (e.subst σ)
  | .spkThird a b c e => .spkThird (a.subst σ) (b.subst σ) (c.subst σ) (e.subst σ)
  | .spkFourth a b d c => .spkFourth (a.subst σ) (b.subst σ) (d.subst σ) (c.subst σ)

@[simp] theorem subst_fill (σ : V → Term W) (c : Context V) (t : Term V) :
    (c.fill t).subst σ = (c.subst σ).fill (t.subst σ) := by
  induction c <;> simp_all [subst, fill, Term.subst]

/-- Synchronise the other variable occurrences while preserving the chosen hole. -/
theorem subst_fill_reduces {σ τ : V → Term W}
    (h : ∀ v, ReducesModulo (σ v) (τ v)) (c : Context V) (a : Term W) :
    ReducesModulo ((c.subst σ).fill a) ((c.subst τ).fill a) := by
  induction c with
  | hole => exact .refl _
  | unary f _ ih => exact .unary f ih
  | binaryLeft f _ b ih => exact .binary f ih (.subst_congr h b)
  | binaryRight f b _ ih => exact .binary f (.subst_congr h b) ih
  | ternaryFirst f _ b d ih => exact .ternary f ih (.subst_congr h b) (.subst_congr h d)
  | ternarySecond f b _ d ih => exact .ternary f (.subst_congr h b) ih (.subst_congr h d)
  | ternaryThird f b d _ ih => exact .ternary f (.subst_congr h b) (.subst_congr h d) ih
  | spkFirst _ b d e ih => exact .spk ih (.subst_congr h b) (.subst_congr h d) (.subst_congr h e)
  | spkSecond b _ d e ih => exact .spk (.subst_congr h b) ih (.subst_congr h d) (.subst_congr h e)
  | spkThird b d _ e ih => exact .spk (.subst_congr h b) (.subst_congr h d) ih (.subst_congr h e)
  | spkFourth b d e _ ih => exact .spk (.subst_congr h b) (.subst_congr h d) (.subst_congr h e) ih

end Context
end ExplainableCrypto.Helios.Symbolic
