import ExplainableCrypto.Helios.Symbolic.SourceOpeningInversion
import ExplainableCrypto.Helios.Symbolic.SourceBinderStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Transport a chosen allocation with an actual binder-structural body
comparison. Fresh unused allocations may be added or removed while the supplied
avoidance set remains avoided. This is a proof property, not a source action. -/
def OpeningTransport (a b : Named V) : Prop :=
  ∀ (ρ : NameAssignment) (ns : List SourceName) (a' : Extended V) (avoid : Finset SourceName),
    Opens a ρ ns a' → (∀ n ∈ ns, n ∉ avoid) →
    ∃ ms b', Opens b ρ ms b' ∧ (∀ m ∈ ms, m ∉ avoid) ∧ a'.BinderStructural b'

def OpeningEquivalent (a b : Named V) : Prop := OpeningTransport a b ∧ OpeningTransport b a

theorem OpeningTransport.refl (a : Named V) : OpeningTransport a a :=
  fun _ ns a' _ ha hf => ⟨ns,a',ha,hf,.refl _⟩

theorem OpeningTransport.trans {a b c : Named V}
    (h : OpeningTransport a b) (j : OpeningTransport b c) : OpeningTransport a c := by
  intro ρ ns a' avoid ha hf
  obtain ⟨ms,b',hb,hg,he⟩ := h ρ ns a' avoid ha hf
  obtain ⟨ks,c',hc,hh,hj⟩ := j ρ ms b' avoid hb hg
  exact ⟨ks,c',hc,hh,he.trans hj⟩

theorem OpeningEquivalent.refl (a : Named V) : OpeningEquivalent a a := ⟨.refl a,.refl a⟩

theorem OpeningEquivalent.symm {a b : Named V} (h : OpeningEquivalent a b) :
    OpeningEquivalent b a := ⟨h.2,h.1⟩

theorem OpeningEquivalent.trans {a b c : Named V}
    (h : OpeningEquivalent a b) (j : OpeningEquivalent b c) : OpeningEquivalent a c :=
  ⟨h.1.trans j.1,j.2.trans h.2⟩

theorem OpeningTransport.parLeft {a b : Named V} (h : OpeningTransport a b) (c : Named V) :
    OpeningTransport (.par a c) (.par b c) := by
  intro ρ ns a' avoid ha hf
  cases ha with
  | @par _ _ _ _ ns ms p q hp hq hd =>
    have hfp : ∀ n ∈ ns, n ∉ avoid ∪ ms.toFinset := by
      intro n hn hm
      rcases Finset.mem_union.mp hm with hm | hm
      · exact hf n (List.mem_append_left _ hn) hm
      · exact hd n hn (List.mem_toFinset.mp hm)
    obtain ⟨ks,p',hp',hfk,he⟩ := h ρ ns p (avoid ∪ ms.toFinset) hp hfp
    refine ⟨ks++ms,.par p' q,.par hp' hq ?_,?_,he.par (.refl _)⟩
    · intro n hn hm
      exact hfk n hn (Finset.mem_union_right _ (List.mem_toFinset.mpr hm))
    · intro n hn hm
      rcases List.mem_append.mp hn with hn | hn
      · exact hfk n hn (Finset.mem_union_left _ hm)
      · exact hf n (List.mem_append_right _ hn) hm

theorem OpeningTransport.parRight {a b : Named V} (h : OpeningTransport a b) (c : Named V) :
    OpeningTransport (.par c a) (.par c b) := by
  intro ρ ns a' avoid ha hf
  cases ha with
  | @par _ _ _ _ ns ms p q hp hq hd =>
    have hfq : ∀ n ∈ ms, n ∉ avoid ∪ ns.toFinset := by
      intro n hn hm
      rcases Finset.mem_union.mp hm with hm | hm
      · exact hf n (List.mem_append_right _ hn) hm
      · exact hd n (List.mem_toFinset.mp hm) hn
    obtain ⟨ks,q',hq',hfk,he⟩ := h ρ ms q (avoid ∪ ns.toFinset) hq hfq
    refine ⟨ns++ks,.par p q',.par hp hq' ?_,?_,(Extended.BinderStructural.refl p).par he⟩
    · intro n hn hm
      exact hfk n hm (Finset.mem_union_right _ (List.mem_toFinset.mpr hn))
    · intro n hn hm
      rcases List.mem_append.mp hn with hn | hn
      · exact hf n (List.mem_append_left _ hn) hm
      · exact hfk n hn (Finset.mem_union_left _ hm)

theorem OpeningTransport.newName {a b : Named V} (h : OpeningTransport a b) (n : SourceName) :
    OpeningTransport (.newName n a) (.newName n b) := by
  intro ρ ns a' avoid ha hf
  cases ha with
  | newName _ v ha hn =>
    obtain ⟨ms,b',hb,hg,he⟩ := h (Function.update ρ n v) _ _ (insert (n.withValue v) avoid) ha
      (by intro m hm hmem; rcases Finset.mem_insert.mp hmem with he | hh
          · exact hn (he ▸ hm)
          · exact hf m (List.mem_cons_of_mem _ hm) hh)
    refine ⟨n.withValue v :: ms,b',.newName n v hb ?_,?_,he⟩
    · intro hm; exact hg _ hm (Finset.mem_insert_self _ _)
    · intro m hm hmem
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hf _ List.mem_cons_self hmem
      · exact hg m hm (Finset.mem_insert_of_mem hmem)

theorem OpeningTransport.newVar {a b : Named (Option V)} (h : OpeningTransport a b) :
    OpeningTransport (.newVar a) (.newVar b) := by
  intro ρ ns a' avoid ha hf
  cases ha with
  | newVar ha =>
    obtain ⟨ms,b',hb,hg,he⟩ := h ρ ns _ avoid ha hf
    exact ⟨ms,.newVar b',.newVar hb,hg,he.newVar⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
