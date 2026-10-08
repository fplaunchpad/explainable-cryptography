import ExplainableCrypto.Helios.Symbolic.RootReduction
import ExplainableCrypto.Helios.Symbolic.ReductionSubstitution
import ExplainableCrypto.Helios.Symbolic.Confluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Apply at most one raw root rule. Failure means only that no raw root rule matches. -/
def contractRoot [DecidableEq V] (t : Term V) : Term V :=
  ((rootReduce t).map Subtype.val).getD t

/-- Bottom-up raw normalization. Background AC/E3/E4 matching is absent. -/
def normalizeRaw [DecidableEq V] : Term V → Term V
  | .name n => .name n
  | .var v => .var v
  | .const c => .const c
  | .unary f a => contractRoot (.unary f (normalizeRaw a))
  | .binary f a b => contractRoot (.binary f (normalizeRaw a) (normalizeRaw b))
  | .ternary f a b c => contractRoot (.ternary f (normalizeRaw a) (normalizeRaw b) (normalizeRaw c))
  | .spk a b c d => .spk (normalizeRaw a) (normalizeRaw b) (normalizeRaw c) (normalizeRaw d)

/-- Ordinary rewriting only: unlike `Reduces`, these steps do not change E0 representatives. -/
abbrev RawReduces (a b : Term V) := Relation.ReflTransGen RewriteStep a b

theorem RootStep.to_rewrite {a b : Term V} (h : RootStep a b) : RewriteStep a b :=
  ⟨.hole, a, b, h, rfl, rfl⟩

theorem RewriteStep.to_modulo {a b : Term V} (h : RewriteStep a b) : ModuloStep a b :=
  ⟨a, b, .refl _, h, .refl _⟩

namespace RawReduces

theorem context {a b : Term V} (h : RawReduces a b) (c : Context V) :
    RawReduces (c.fill a) (c.fill b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact .tail ih (hs.context c)

theorem to_modulo {a b : Term V} (h : RawReduces a b) : ReducesModulo a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans (.single hs.to_modulo)

theorem weight_le {a b : Term V} (h : RawReduces a b) : b.cryptoWeight ≤ a.cryptoWeight :=
  h.to_modulo.weight_le

theorem unary (f) {a a' : Term V} (ha : RawReduces a a') :
    RawReduces (.unary f a) (.unary f a') := ha.context (.unary f .hole)

theorem binary (f) {a a' b b' : Term V} (ha : RawReduces a a') (hb : RawReduces b b') :
    RawReduces (.binary f a b) (.binary f a' b') :=
  (ha.context (.binaryLeft f .hole b)).trans (hb.context (.binaryRight f a' .hole))

theorem ternary (f) {a a' b b' c c' : Term V}
    (ha : RawReduces a a') (hb : RawReduces b b') (hc : RawReduces c c') :
    RawReduces (.ternary f a b c) (.ternary f a' b' c') :=
  ((ha.context (.ternaryFirst f .hole b c)).trans
    (hb.context (.ternarySecond f a' .hole c))).trans (hc.context (.ternaryThird f a' b' .hole))

theorem spk {a a' b b' c c' d d' : Term V}
    (ha : RawReduces a a') (hb : RawReduces b b') (hc : RawReduces c c') (hd : RawReduces d d') :
    RawReduces (.spk a b c d) (.spk a' b' c' d') :=
  (((ha.context (.spkFirst .hole b c d)).trans
    (hb.context (.spkSecond a' .hole c d))).trans
      (hc.context (.spkThird a' b' .hole d))).trans (hd.context (.spkFourth a' b' c' .hole))

end RawReduces

variable [DecidableEq V]

theorem contractRoot_reachable (t : Term V) : RawReduces t (contractRoot t) := by
  cases he : rootReduce t with
  | none => simp only [contractRoot, he, Option.map_none, Option.getD_none]; exact .refl
  | some u =>
    simp only [contractRoot, he, Option.map_some, Option.getD_some]
    exact .single u.property.to_rewrite

/-- The algorithm produces an actual finite ordinary-reduction trace. -/
theorem normalizeRaw_reachable (t : Term V) : RawReduces t (normalizeRaw t) := by
  induction t with
  | name => exact .refl
  | var => exact .refl
  | const => exact .refl
  | unary f _ ih => exact (RawReduces.unary f ih).trans (contractRoot_reachable _)
  | binary f _ _ ih₁ ih₂ => exact (RawReduces.binary f ih₁ ih₂).trans (contractRoot_reachable _)
  | ternary f _ _ _ ih₁ ih₂ ih₃ =>
    exact (RawReduces.ternary f ih₁ ih₂ ih₃).trans (contractRoot_reachable _)
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ => exact RawReduces.spk ih₁ ih₂ ih₃ ih₄

/-- Every source rule preserves the raw normalizer, including repeated parameters. -/
theorem RootStep.normalize_eq {a b : Term V} (h : RootStep a b) :
    normalizeRaw a = normalizeRaw b := by
  cases h <;> simp [normalizeRaw, contractRoot, rootReduce]
  split <;> simp_all

theorem Context.normalize_congr (c : Context V) {a b : Term V}
    (h : normalizeRaw a = normalizeRaw b) :
    normalizeRaw (c.fill a) = normalizeRaw (c.fill b) := by
  induction c <;> simp_all [Context.fill, normalizeRaw]

/-- All ordinary context positions are covered, not only the directed test contexts. -/
theorem RewriteStep.normalize_eq {a b : Term V} (h : RewriteStep a b) :
    normalizeRaw a = normalizeRaw b := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  exact c.normalize_congr hr.normalize_eq

theorem RawReduces.normalize_eq {a b : Term V} (h : RawReduces a b) :
    normalizeRaw a = normalizeRaw b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans hs.normalize_eq

theorem normalizeRaw_idempotent (t : Term V) : normalizeRaw (normalizeRaw t) = normalizeRaw t :=
  (normalizeRaw_reachable t).normalize_eq.symm

/-- Raw irreducibility is weaker than the project's modulo-E0 `Irreducible`. -/
def RawIrreducible (t : Term V) : Prop := ∀ u, ¬ RewriteStep t u

theorem normalizeRaw_irreducible (t : Term V) : RawIrreducible (normalizeRaw t) := by
  intro b hb
  have hw := (normalizeRaw_reachable b).weight_le
  have he : normalizeRaw b = normalizeRaw t := hb.normalize_eq.symm.trans (normalizeRaw_idempotent t)
  rw [he] at hw
  have hlt := hb.weight_lt
  omega

omit [DecidableEq V] in
/-- Confluence of ordinary rewriting, with literal equality of the common descendant.
This is not confluence of `ModuloStep` or the `Reduces` closure. -/
theorem ordinary_rewriting_confluent {a b c : Term V}
    (hb : RawReduces a b) (hc : RawReduces a c) :
    ∃ d, RawReduces b d ∧ RawReduces c d := by
  classical
  have he : normalizeRaw c = normalizeRaw b := hc.normalize_eq.symm.trans hb.normalize_eq
  exact ⟨normalizeRaw b, normalizeRaw_reachable b, he ▸ normalizeRaw_reachable c⟩

omit [DecidableEq V] in
theorem raw_contextual_peak_joined {a b c : Term V}
    (hb : RewriteStep a b) (hc : RewriteStep a c) : JoinModulo b c := by
  obtain ⟨d, hbd, hcd⟩ := ordinary_rewriting_confluent (.single hb) (.single hc)
  exact ⟨d, hbd.to_modulo, hcd.to_modulo⟩

end ExplainableCrypto.Helios.Symbolic
