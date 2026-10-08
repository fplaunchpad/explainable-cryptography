import ExplainableCrypto.Helios.Symbolic.MinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- Only immediate children are required to be source-minimum; the root may reduce. -/
def MinimumChildren (φ : Frame restricted n) : Recipe n → Prop
  | .name _ | .var _ | .const _ => True
  | .unary _ a => MinimalRecipe restricted φ.value a
  | .binary _ a b => MinimalRecipe restricted φ.value a ∧ MinimalRecipe restricted φ.value b
  | .ternary _ a b c => MinimalRecipe restricted φ.value a ∧
      MinimalRecipe restricted φ.value b ∧ MinimalRecipe restricted φ.value c
  | .spk a b c d => MinimalRecipe restricted φ.value a ∧
      MinimalRecipe restricted φ.value b ∧ MinimalRecipe restricted φ.value c ∧
      MinimalRecipe restricted φ.value d

def LocalMinimumTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r → SharedMinimum φ ψ r

/-- A shared equivalent can reuse an already established shared minimum. -/
theorem SharedMinimum.of_shared_equivalent {r s : Recipe n}
    (h : SharedMinimum φ ψ s) (he : EqE (φ.eval r) (φ.eval s))
    (he' : EqE (ψ.eval r) (ψ.eval s)) : SharedMinimum φ ψ r := by
  obtain ⟨m, hm, hs, hs'⟩ := h
  exact ⟨m, hm, he.trans hs, he'.trans hs'⟩

/-- Structural induction minimizes children in both worlds before invoking the
local root obligation. This requires no smaller-observation premise. -/
theorem common_minima_of_local (h : LocalMinimumTransport φ ψ) : CommonMinima φ ψ := by
  intro r
  induction r with
  | name a => exact fun hp => h (.name a) hp trivial
  | var a => exact fun hp => h (.var a) hp trivial
  | const a => exact fun hp => h (.const a) hp trivial
  | unary f a ia =>
    intro hp
    obtain ⟨a', ha, he, he'⟩ := ia hp
    exact (h (.unary f a') ha.isPublic ha).of_shared_equivalent
      (.unary f he) (.unary f he')
  | binary f a b ia ib =>
    intro hp
    obtain ⟨a', ha, he, he'⟩ := ia hp.1
    obtain ⟨b', hb, hf, hf'⟩ := ib hp.2
    exact (h (.binary f a' b') ⟨ha.isPublic, hb.isPublic⟩ ⟨ha, hb⟩).of_shared_equivalent
      (.binary f he hf) (.binary f he' hf')
  | ternary f a b c ia ib ic =>
    intro hp
    obtain ⟨a', ha, he, he'⟩ := ia hp.1
    obtain ⟨b', hb, hf, hf'⟩ := ib hp.2.1
    obtain ⟨c', hc, hg, hg'⟩ := ic hp.2.2
    exact (h (.ternary f a' b' c') ⟨ha.isPublic, hb.isPublic, hc.isPublic⟩
      ⟨ha, hb, hc⟩).of_shared_equivalent
      (.ternary f he hf hg) (.ternary f he' hf' hg')
  | spk a b c d ia ib ic id =>
    intro hp
    obtain ⟨a', ha, he, he'⟩ := ia hp.1
    obtain ⟨b', hb, hf, hf'⟩ := ib hp.2.1
    obtain ⟨c', hc, hg, hg'⟩ := ic hp.2.2.1
    obtain ⟨d', hd, hh, hh'⟩ := id hp.2.2.2
    exact (h (.spk a' b' c' d') ⟨ha.isPublic, hb.isPublic, hc.isPublic, hd.isPublic⟩
      ⟨ha, hb, hc, hd⟩).of_shared_equivalent
      (.spk he hf hg hh) (.spk he' hf' hg' hh')

/-- The actionable remaining premises are local root minimization and assembly
of the minimum observation branches. Neither is asserted for swapped Helios frames. -/
theorem staticEq_of_local_minimum_transport (hlocal : LocalMinimumTransport φ ψ)
    (hstep : MinimumObservationStep φ ψ) : StaticEq φ ψ :=
  staticEq_of_common_minima (common_minima_of_local hlocal) hstep

end ExplainableCrypto.Helios.Symbolic.Frame
