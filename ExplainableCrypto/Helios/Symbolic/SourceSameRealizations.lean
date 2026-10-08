import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpening

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

/-- Equality of complete interpretations, including every active equation and
the whole process body. It adds no source action or structural rule. -/
def SameRealizations (a b : Extended V) : Prop :=
  ∀ env p, a.Realizes env p ↔ b.Realizes env p

variable {V W : Type}

theorem SameRealizations.refl (a : Extended V) : SameRealizations a a := fun _ _ => Iff.rfl

theorem SameRealizations.symm {a b : Extended V} (h : SameRealizations a b) :
    SameRealizations b a := fun env p => (h env p).symm

theorem SameRealizations.trans {a b c : Extended V}
    (h : SameRealizations a b) (j : SameRealizations b c) : SameRealizations a c :=
  fun env p => (h env p).trans (j env p)

theorem Structural.sameRealizations {a b : Extended V} (h : Structural a b) :
    SameRealizations a b := h.realizes

theorem SameRealizations.par {a a' b b' : Extended V}
    (ha : SameRealizations a a') (hb : SameRealizations b b') :
    SameRealizations (.par a b) (.par a' b') := by
  intro env p
  exact exists_congr (fun q => exists_congr (fun r => and_congr (ha env q) (and_congr (hb env r) Iff.rfl)))

theorem SameRealizations.newVar {a b : Extended (Option V)} (h : SameRealizations a b) :
    SameRealizations (.newVar a) (.newVar b) := by
  intro env p
  exact exists_congr (fun m => h (extendEnv env m) p)

theorem SameRealizations.rename {a b : Extended V} (h : SameRealizations a b) (σ : V → W) :
    SameRealizations (a.rename σ) (b.rename σ) := by
  intro env p
  rw [realizes_rename,realizes_rename]
  exact h _ _

theorem sameRealizations_varComm (a : Extended (Option (Option V))) :
    SameRealizations (.newVar (.newVar a)) (.newVar (.newVar (a.rename swapBinders))) := by
  intro env p
  simp only [Realizes,realizes_rename,extendEnv_swapBinders]
  exact exists_comm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
