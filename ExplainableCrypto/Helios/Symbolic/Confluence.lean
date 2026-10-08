import ExplainableCrypto.Helios.Symbolic.ReductionClosure

/-! A termination-to-confluence argument for this relation. All global results
retain `LocalConfluentModulo` as an explicit hypothesis. `GlobalConfluence.lean`
supplies its Helios-specific proof by simultaneous structural induction. -/
namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

def JoinModulo (a b : Term V) : Prop :=
  ∃ c, ReducesModulo a c ∧ ReducesModulo b c

def LocalConfluentModulo (V : Type) : Prop :=
  ∀ a b c : Term V, ModuloStep a b → ModuloStep a c → JoinModulo b c

def ConfluentModulo (V : Type) : Prop :=
  ∀ a b c : Term V, ReducesModulo a b → ReducesModulo a c → JoinModulo b c

theorem normal_forms_unique_of_local_confluence (hlc : LocalConfluentModulo V) :
    ∀ a b c : Term V, ReducesModulo a b → Irreducible b →
      ReducesModulo a c → Irreducible c → BaseEq b c := by
  intro a
  induction a using rewrite_wellFounded.induction with
  | h a ih =>
    intro b c hab hb hac hc
    cases hab with
    | base he =>
      exact he.symm.trans ((hb.base he.symm).reducesModulo hac)
    | head hab₁ hab₂ =>
      cases hac with
      | base he => exact False.elim ((hc.base he.symm) _ hab₁)
      | head hac₁ hac₂ =>
        obtain ⟨d, hbd, hcd⟩ := hlc _ _ _ hab₁ hac₁
        obtain ⟨e, hde, he⟩ := exists_normal_form d
        have hbe := ih _ hab₁ b e hab₂ hb (hbd.trans hde.to_modulo) he
        have hce := ih _ hac₁ c e hac₂ hc (hcd.trans hde.to_modulo) he
        exact hbe.trans hce.symm

/-- Newman-style consequence of the already checked termination theorem. -/
theorem confluence_of_local_confluence (hlc : LocalConfluentModulo V) :
    ConfluentModulo V := by
  intro a b c hab hac
  obtain ⟨b', hbb, hb⟩ := exists_normal_form b
  obtain ⟨c', hcc, hc⟩ := exists_normal_form c
  have he := normal_forms_unique_of_local_confluence hlc a b' c'
    (hab.trans hbb.to_modulo) hb (hac.trans hcc.to_modulo) hc
  exact ⟨c', hbb.to_modulo.post_base he, hcc.to_modulo⟩

namespace JoinModulo

theorem refl (a : Term V) : JoinModulo a a := ⟨a, .refl a, .refl a⟩

theorem symm {a b : Term V} (h : JoinModulo a b) : JoinModulo b a := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨c, hb, ha⟩

theorem trans (hc : ConfluentModulo V) {a b c : Term V}
    (h : JoinModulo a b) (h' : JoinModulo b c) : JoinModulo a c := by
  obtain ⟨d, had, hbd⟩ := h
  obtain ⟨e, hbe, hce⟩ := h'
  obtain ⟨f, hdf, hef⟩ := hc b d e hbd hbe
  exact ⟨f, had.trans hdf, hce.trans hef⟩

theorem context {a b : Term V} (h : JoinModulo a b) (c : Context V) :
    JoinModulo (c.fill a) (c.fill b) := by
  obtain ⟨d, ha, hb⟩ := h
  exact ⟨c.fill d, ha.context c, hb.context c⟩

theorem sound {a b : Term V} (h : JoinModulo a b) : EqE a b := by
  obtain ⟨c, ha, hb⟩ := h
  exact ha.sound.trans hb.sound.symm

end JoinModulo

/-- The original E is precisely joinability if the remaining local-confluence
obligation holds; no new equality relation replaces E in the security target. -/
theorem EqE.join_of_confluence (hc : ConfluentModulo V) {a b : Term V} (h : EqE a b) :
    JoinModulo a b := by
  induction h with
  | equation he =>
    cases he.classify with
    | inl hb => exact ⟨_, .base (.equation hb), .refl _⟩
    | inr hr => exact ⟨_, .single hr.to_modulo, .refl _⟩
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans hc ih₂
  | unary f _ ih => exact ih.context (.unary f .hole)
  | binary f _ _ ih₁ ih₂ =>
    exact (ih₁.context (.binaryLeft f .hole _)).trans hc
      (ih₂.context (.binaryRight f _ .hole))
  | ternary f _ _ _ ih₁ ih₂ ih₃ =>
    exact ((ih₁.context (.ternaryFirst f .hole _ _)).trans hc
      (ih₂.context (.ternarySecond f _ .hole _))).trans hc
        (ih₃.context (.ternaryThird f _ _ .hole))
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ =>
    exact (((ih₁.context (.spkFirst .hole _ _ _)).trans hc
      (ih₂.context (.spkSecond _ .hole _ _))).trans hc
        (ih₃.context (.spkThird _ _ .hole _))).trans hc
          (ih₄.context (.spkFourth _ _ _ .hole))

theorem eqE_iff_join_of_local_confluence (hlc : LocalConfluentModulo V) (a b : Term V) :
    EqE a b ↔ JoinModulo a b :=
  ⟨EqE.join_of_confluence (confluence_of_local_confluence hlc), JoinModulo.sound⟩

theorem irreducible_eqE_iff_base_of_local_confluence
    (hlc : LocalConfluentModulo V) {a b : Term V} (ha : Irreducible a) (hb : Irreducible b) :
    EqE a b ↔ BaseEq a b := by
  constructor
  · intro h
    obtain ⟨c, hac, hbc⟩ := h.join_of_confluence (confluence_of_local_confluence hlc)
    exact (ha.reducesModulo hac).trans (hb.reducesModulo hbc).symm
  · exact BaseEq.sound

end ExplainableCrypto.Helios.Symbolic
