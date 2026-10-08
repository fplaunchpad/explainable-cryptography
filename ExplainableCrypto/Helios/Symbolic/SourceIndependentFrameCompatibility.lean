import ExplainableCrypto.Helios.Symbolic.SourceCanonicalFrameSolutions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}
variable {a b c : Named (Fin handles)}

/-- A genuine ground presentation supplies a solution, excluding vacuous
universal observations from inconsistent raw constraints. -/
theorem RepresentsFrame.models {φ : Frame restricted handles} (ha : a.RepresentsFrame hidden φ) :
    a.Models id φ.value :=
  (models_frameOf a id φ.value).mp ((Structural.models ha id φ.value).mpr (canonicalFrame_models φ))

theorem RepresentsFrame.validEquation_iff {φ : Frame restricted handles}
    (ha : a.RepresentsFrame hidden φ) (r s : Recipe handles)
    (hr : r.Public restricted) (hs : s.Public restricted) :
    a.ValidEquation r s ↔ EqE (φ.eval r) (φ.eval s) :=
  (validEquation_frameOf_iff a r s).symm.trans
    ((validEquation_structural_iff ha r s).trans (canonicalFrame_validEquation_iff φ r s hr hs))

/-- Independently chosen presentations of the same actual source frame agree
on every full-E public equality test. Their private values need not be literally
or pointwise E-equal: alpha conversion is included in each structural path. -/
theorem RepresentsFrame.compatible {hidden' : Finset Nat} {φ ψ : Frame restricted handles}
    (ha : a.RepresentsFrame hidden φ) (hb : a.RepresentsFrame hidden' ψ) : φ.StaticEq ψ := by
  intro r s hr hs
  exact (ha.validEquation_iff r s hr hs).symm.trans (hb.validEquation_iff r s hr hs)

theorem canonicalFrame_structural_staticEq {hidden' : Finset Nat} (φ ψ : Frame restricted handles)
    (h : Structural (canonicalFrame hidden φ) (canonicalFrame hidden' ψ)) : φ.StaticEq ψ :=
  (canonicalFrame_represents φ).compatible ((canonicalFrame_represents ψ).structural h.symm)

/-- Composition uses the existing common-policy construction and now discharges
the independent middle-frame compatibility obligation. -/
theorem StaticEq.trans (hab : StaticEq a b) (hbc : StaticEq b c) : StaticEq a c := by
  obtain ⟨policy,φ,ψ,χ,δ,ha,hb,hb',hc,he,hf⟩ := hab.common_policy hbc
  exact .of_presentations ha hc (he.trans ((hb.compatible hb').trans hf))

/-- Arbitrary literal tests are meaningful after freshening the actual frame
presentations away from those same unchanged tests. -/
theorem StaticEq.validEquation (hab : StaticEq a b) (r s : Recipe handles) :
    a.ValidEquation r s ↔ b.ValidEquation r s := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,hr,hs,_,he⟩ := hab.test_witness r s
  exact (ha.validEquation_iff r s hr hs).trans (he.trans (hb.validEquation_iff r s hr hs).symm)

/-- Observation agreement is also sufficient when actual common-policy
presentation witnesses are supplied. No arbitrary raw frame is assumed solvable. -/
theorem staticEq_iff_validEquations {φ ψ : Frame restricted handles}
    (ha : a.RepresentsFrame hidden φ) (hb : b.RepresentsFrame hidden ψ) :
    StaticEq a b ↔ ∀ r s : Recipe handles, a.ValidEquation r s ↔ b.ValidEquation r s := by
  constructor
  · exact fun h => h.validEquation
  · intro h
    apply StaticEq.of_presentations ha hb
    intro r s hr hs
    exact (ha.validEquation_iff r s hr hs).symm.trans
      ((h r s).trans (hb.validEquation_iff r s hr hs))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
