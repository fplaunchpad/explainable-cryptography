import ExplainableCrypto.Helios.Symbolic.SourceOpeningTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem OpeningEquivalent.of_opens_iff {a b : Named V}
    (h : ∀ ρ ns p, Opens a ρ ns p ↔ Opens b ρ ns p) : OpeningEquivalent a b := by
  constructor
  · intro ρ ns p avoid hp hf; exact ⟨ns,p,(h _ _ _).mp hp,hf,.refl _⟩
  · intro ρ ns p avoid hp hf; exact ⟨ns,p,(h _ _ _).mpr hp,hf,.refl _⟩

theorem openingEquivalent_embed {a b : Extended V} (h : Extended.Structural a b) :
    OpeningEquivalent (.embed a) (.embed b) := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp
    exact ⟨[],_,.embed b ρ,by simp,(h.mapNames ρ.base ρ.channel).binderStructural⟩
  · intro ρ ns p avoid hp hf
    cases hp
    exact ⟨[],_,.embed a ρ,by simp,(h.symm.mapNames ρ.base ρ.channel).binderStructural⟩

theorem openingTransport_comm (a b : Named V) : OpeningTransport (.par a b) (.par b a) := by
  intro ρ ns p avoid hp hf
  cases hp with
  | @par _ _ _ _ ns ms a' b' ha hb hd =>
    refine ⟨ms++ns,.par b' a',.par hb ha (fun n hn hm => hd n hm hn),?_,(Extended.Structural.comm _ _).binderStructural⟩
    intro n hn hm
    rcases List.mem_append.mp hn with hn | hn
    · exact hf n (List.mem_append_right _ hn) hm
    · exact hf n (List.mem_append_left _ hn) hm

theorem openingEquivalent_comm (a b : Named V) : OpeningEquivalent (.par a b) (.par b a) :=
  ⟨openingTransport_comm a b,openingTransport_comm b a⟩

theorem openingEquivalent_zero (a : Named V) :
    OpeningEquivalent (.par a (.embed (.plain .nil))) a := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp with
    | par ha hb hd =>
      cases hb
      exact ⟨_,_,ha,by simpa only [List.append_nil] using hf,(Extended.Structural.zero _).binderStructural⟩
  · intro ρ ns p avoid hp hf
    exact ⟨ns++[],.par p (.plain .nil),.par hp (.embed _ _) (by simp),
      by simpa only [List.append_nil] using hf,(Extended.Structural.zero _).symm.binderStructural⟩

theorem openingEquivalent_assoc (a b c : Named V) :
    OpeningEquivalent (.par (.par a b) c) (.par a (.par b c)) := by
  constructor
  · intro ρ ns p avoid hp hf
    cases hp with
    | @par _ _ _ _ _ ks _ c' hab hc hd =>
      cases hab with
      | @par _ _ _ _ ns ms a' b' ha hb hj =>
        refine ⟨ns++(ms++ks),.par a' (.par b' c'),.par ha
          (.par hb hc (fun n hn hm => hd n (List.mem_append_right _ hn) hm)) ?_,?_,
          (Extended.Structural.assoc _ _ _).binderStructural⟩
        · intro n hn hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hj n hn hm
          · exact hd n (List.mem_append_left _ hn) hm
        · simpa only [List.append_assoc] using hf
  · intro ρ ns p avoid hp hf
    cases hp with
    | @par _ _ _ _ ns _ a' _ ha hbc hd =>
      cases hbc with
      | @par _ _ _ _ ms ks b' c' hb hc hj =>
        refine ⟨(ns++ms)++ks,.par (.par a' b') c',.par
          (.par ha hb (fun n hn hm => hd n hn (List.mem_append_left _ hm))) hc ?_,?_,
          (Extended.Structural.assoc _ _ _).symm.binderStructural⟩
        · intro n hn hm
          rcases List.mem_append.mp hn with hn | hn
          · exact hd n hn (List.mem_append_right _ hm)
          · exact hj n hn hm
        · simpa only [List.append_assoc] using hf

theorem openingEquivalent_embedPar (a b : Extended V) :
    OpeningEquivalent (.embed (.par a b)) (.par (.embed a) (.embed b)) := by
  apply OpeningEquivalent.of_opens_iff
  intro ρ ns p
  constructor
  · intro h; cases h
    exact .par (.embed _ _) (.embed _ _) (by simp)
  · intro h; cases h with
    | par ha hb hd => cases ha; cases hb; exact .embed _ _

theorem openingEquivalent_embedVar (a : Extended (Option V)) :
    OpeningEquivalent (.embed (.newVar a)) (.newVar (.embed a)) := by
  apply OpeningEquivalent.of_opens_iff
  intro ρ ns p
  constructor
  · intro h; cases h; exact .newVar (.embed _ _)
  · intro h; cases h with
    | newVar ha => cases ha; exact .embed _ _

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
