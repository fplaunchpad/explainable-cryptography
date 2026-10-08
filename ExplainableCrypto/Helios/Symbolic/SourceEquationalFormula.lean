import ExplainableCrypto.Helios.Symbolic.SourceProcessBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Formula

/-- Componentwise full-E congruence, retaining guard polarity and conjunction. -/
inductive EquivE : Formula V → Formula V → Prop where
  | equal {a a' b b'} : EqE a a' → EqE b b' → EquivE (.equal a b) (.equal a' b')
  | unequal {a a' b b'} : EqE a a' → EqE b b' → EquivE (.unequal a b) (.unequal a' b')
  | both {f f' g g'} : EquivE f f' → EquivE g g' → EquivE (.both f g) (.both f' g')

variable {V W : Type}

theorem EquivE.refl (f : Formula V) : EquivE f f := by
  induction f with
  | equal => exact .equal (.refl _) (.refl _)
  | unequal => exact .unequal (.refl _) (.refl _)
  | both f g hf hg => exact .both hf hg

theorem EquivE.symm {f g : Formula V} (h : EquivE f g) : EquivE g f := by
  induction h with
  | equal h h' => exact .equal h.symm h'.symm
  | unequal h h' => exact .unequal h.symm h'.symm
  | both h h' ih ih' => exact .both ih ih'

theorem EquivE.trans {f g k : Formula V} (h : EquivE f g) (h' : EquivE g k) :
    EquivE f k := by
  induction h generalizing k with
  | equal h h' => cases ‹EquivE _ k› with | equal j j' => exact .equal (h.trans j) (h'.trans j')
  | unequal h h' => cases ‹EquivE _ k› with | unequal j j' => exact .unequal (h.trans j) (h'.trans j')
  | both h h' ih ih' => cases ‹EquivE _ k› with | both j j' => exact .both (ih j) (ih' j')

theorem EquivE.subst {f g : Formula V} (h : EquivE f g) (σ : V → Term W) :
    EquivE (f.subst σ) (g.subst σ) := by
  induction h with
  | equal h h' => exact .equal (h.subst σ) (h'.subst σ)
  | unequal h h' => exact .unequal (h.subst σ) (h'.subst σ)
  | both h h' ih ih' => exact .both ih ih'

theorem subst_equivE (f : Formula V) (σ τ : V → Term W)
    (h : ∀ v, EqE (σ v) (τ v)) : EquivE (f.subst σ) (f.subst τ) := by
  induction f with
  | equal a b => exact .equal (a.subst_congr σ τ h) (b.subst_congr σ τ h)
  | unequal a b => exact .unequal (a.subst_congr σ τ h) (b.subst_congr σ τ h)
  | both f g hf hg => exact .both hf hg

theorem EquivE.holds {f g : Formula V} (h : EquivE f g) (env : V → Ground) :
    f.Holds env ↔ g.Holds env := by
  have obs {a a' b b' : Term V} (ha : EqE a a') (hb : EqE b b') :
      EqE (a.subst env) (b.subst env) ↔ EqE (a'.subst env) (b'.subst env) :=
    ⟨fun j => (ha.subst env).symm.trans (j.trans (hb.subst env)),
     fun j => (ha.subst env).trans (j.trans (hb.subst env).symm)⟩
  induction h with
  | equal ha hb => exact obs ha hb
  | unequal ha hb => exact not_congr (obs ha hb)
  | both h h' ih ih' => exact and_congr ih ih'

theorem holds_equivE_env (f : Formula V) (σ τ : V → Ground)
    (h : ∀ v, EqE (σ v) (τ v)) : f.Holds σ ↔ f.Holds τ := by
  have obs (a b : Term V) : EqE (a.subst σ) (b.subst σ) ↔ EqE (a.subst τ) (b.subst τ) :=
    ⟨fun j => (a.subst_congr σ τ h).symm.trans (j.trans (b.subst_congr σ τ h)),
     fun j => (a.subst_congr σ τ h).trans (j.trans (b.subst_congr σ τ h).symm)⟩
  induction f with
  | equal a b => exact obs a b
  | unequal a b => exact not_congr (obs a b)
  | both f g hf hg => exact and_congr hf hg

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Formula
