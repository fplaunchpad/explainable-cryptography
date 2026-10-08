import ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningReconstruction
import ExplainableCrypto.Helios.Symbolic.SourcePresentationRigidity
import ExplainableCrypto.Helios.Symbolic.SourceJointOpening

namespace ExplainableCrypto.Helios.Symbolic
namespace Historical.General.Source.Extended
variable {V : Type} {handles : Nat}

/-- Plain code always has an interpretation once the actual provider equations
have a solution. This does not supply a structural presentation. -/
theorem satisfies_iff_exists_realizes (a : Extended V) (env : V → Ground) :
    a.Satisfies env ↔ ∃ p, a.Realizes env p := by
  induction a with
  | plain p => exact ⟨fun _ => ⟨_,.refl _⟩,fun _ => True.intro⟩
  | active x m => exact ⟨fun h => ⟨.nil,h,.refl _⟩,fun ⟨_,h,_⟩ => h⟩
  | newVar a ih =>
    simp only [Satisfies,Realizes,ih]
    exact exists_comm
  | par a b ha hb =>
    constructor
    · rintro ⟨h,j⟩
      obtain ⟨p,hp⟩ := (ha env).mp h
      obtain ⟨q,hq⟩ := (hb env).mp j
      exact ⟨.par p q,p,q,hp,hq,.refl _⟩
    · rintro ⟨_,p,q,hp,hq,_⟩
      exact ⟨(ha env).mpr ⟨p,hp⟩,(hb env).mpr ⟨q,hq⟩⟩

theorem SameRealizations.satisfies {a b : Extended V} (h : a.SameRealizations b)
    (env : V → Ground) : a.Satisfies env ↔ b.Satisfies env := by
  rw [satisfies_iff_exists_realizes,satisfies_iff_exists_realizes]
  exact exists_congr (h env)

/-- Pointwise full-E equality rewrites every retained public provider. -/
theorem frameEntries_structural_of_values (h : Nat) (vars : Fin h → V)
    (values values' : Fin h → Ground) (he : ∀ i, EqE (values i) (values' i)) :
    Structural (frameEntries h vars values) (frameEntries h vars values') := by
  induction h with
  | zero => exact .refl _
  | succ h ih =>
    exact (Structural.parLeft _ (.rewrite _ ((he (Fin.last h)).subst Empty.elim))).trans
      (Structural.parRight _ (ih _ _ _ (fun i => he i.castSucc)))

/-- Actual presentations are the necessary structural premise; semantic
comparison only identifies the ground equations after both are extracted. -/
theorem SameRealizations.frame_structural_of_presentations
    {a b : Extended (Fin handles)} (h : a.SameRealizations b)
    {r s : Finset Nat} {φ : Frame r handles} {ψ : Frame s handles}
    (ha : a.frameOf.BinderStructural (activeFrame φ))
    (hb : b.frameOf.BinderStructural (activeFrame ψ)) :
    a.frameOf.BinderStructural b.frameOf := by
  have hv : ∀ i, EqE (φ.value i) (ψ.value i) := by
    apply (activeFrame_satisfies_iff ψ φ.value).mp
    apply (hb.satisfies φ.value).mp
    apply (satisfies_frameOf b φ.value).mpr
    apply (h.satisfies φ.value).mp
    apply (satisfies_frameOf a φ.value).mp
    apply (ha.satisfies φ.value).mpr
    exact (activeFrame_satisfies_iff φ φ.value).mpr (fun _ => .refl _)
  exact ha.trans ((frameEntries_structural_of_values handles id _ _ hv).binderStructural.trans hb.symm)
end Historical.General.Source.Extended

namespace Historical.General.Source.Named
variable {handles : Nat}

/-- Any chosen opening of an actually presented process has an actual ground
frame presentation. The extracted assignment need not be injective or fresh. -/
theorem RepresentsFrame.opening_presentation {r hidden : Finset Nat}
    {a : Named (Fin handles)} {φ : Frame r handles} (h : a.RepresentsFrame hidden φ)
    {ρ : NameAssignment} {ns : List SourceName} {b : Extended (Fin handles)}
    (ho : Opens a ρ ns b) :
    ∃ f : Nat → Nat, b.frameOf.BinderStructural (Extended.activeFrame (φ.mapNames f)) := by
  obtain ⟨ms,c,hc,_,he⟩ := h.transport_binder_opening ρ ns b.frameOf ∅ ho.frameOf (by simp)
  obtain ⟨τ,hc',_,_⟩ := hc.prefix_pair_assignment _ (Extended.activeFrame φ)
    (Extended.activeFrame φ) ρ
  refine ⟨τ.base,?_⟩
  simpa only [hc',Extended.activeFrame_mapNames] using he

/-- Joint semantic coordinates align two independently supplied actual frame
presentations, even when their original private policies differ. -/
theorem JointOpening.frame_structural_of_presentations
    {a d : Named (Fin handles)} (h : JointOpening a d)
    {r s hidden hidden' : Finset Nat} {φ : Frame r handles} {ψ : Frame s handles}
    (ha : a.RepresentsFrame hidden φ) (hd : d.RepresentsFrame hidden' ψ) :
    Structural a.frameOf d.frameOf := by
  obtain ⟨ns,b,ms,c,hb,hc,hf,hg,he,_⟩ := h.fresh (a.frameOf.allNames ∪ d.frameOf.allNames)
  obtain ⟨f,hp⟩ := ha.opening_presentation hb
  obtain ⟨g,hq⟩ := hd.opening_presentation hc
  exact hb.frameOf.structural_of_binder hc.frameOf
    (fun n hn hh => hf n hn (Finset.mem_union_left _ hh))
    (fun n hn hh => hg n hn (Finset.mem_union_left _ hh))
    (he.frame_structural_of_presentations hp hq)

/-- Once constructive extraction supplies some actual presentation, the full
phase joint witness determines its prescribed policy and complete frame. -/
theorem JointOpening.align_presentation {r s hidden hidden' : Finset Nat}
    {a : Named (Fin handles)} {p : ScopedState r handles} {φ : Frame s handles}
    (h : JointOpening a (restrictedState hidden p)) (ha : a.RepresentsFrame hidden' φ) :
    a.RepresentsFrame hidden p.frame :=
  (h.frame_structural_of_presentations ha (restrictedState_represents p)).trans
    (restrictedState_frameOf hidden p)

end Historical.General.Source.Named
end ExplainableCrypto.Helios.Symbolic
