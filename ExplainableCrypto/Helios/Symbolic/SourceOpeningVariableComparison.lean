import ExplainableCrypto.Helios.Symbolic.SourceOpeningNameComparison

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem openingEquivalent_varPar (a : Named V) (b : Named (Option V)) :
    OpeningEquivalent (.par a (.newVar b)) (.newVar (.par (a.rename some) b)) := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp with
    | par ha hb hd => cases hb with
      | newVar hb =>
        exact ⟨_,_,.newVar (.par (ha.rename some) hb hd),hf,
          (Extended.Structural.newPar _ _).binderStructural⟩
  · intro ρ ns p avoid hp hf
    cases hp with
    | newVar hp => cases hp with
      | par ha hb hd =>
        obtain ⟨a',ha',he⟩ := (opens_rename_iff a some _ _ _).mp ha
        subst he
        exact ⟨_,_,.par ha' (.newVar hb) hd,hf,
          (Extended.Structural.newPar _ _).symm.binderStructural⟩

theorem openingEquivalent_varComm (a : Named (Option (Option V))) :
    OpeningEquivalent (.newVar (.newVar a))
      (.newVar (.newVar (a.rename Extended.swapBinders))) := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp with
    | newVar hp => cases hp with
      | newVar hp =>
        exact ⟨_,_,.newVar (.newVar (hp.rename Extended.swapBinders)),hf,
          Extended.BinderStructural.varComm _⟩
  · intro ρ ns p avoid hp hf
    cases hp with
    | newVar hp => cases hp with
      | newVar hp =>
        obtain ⟨a',ha',he⟩ := (opens_rename_iff a Extended.swapBinders _ _ _).mp hp
        subst he
        exact ⟨_,_,.newVar (.newVar ha'),hf,(Extended.BinderStructural.varComm _).symm⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
