import ExplainableCrypto.Helios.Symbolic.SourceFiniteFaithfulAssignments

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- The primitive used by an internal derivation. This classification does not
claim that different derivations between the same endpoints have the same kind. -/
inductive InternalKind where
  | communication
  | conditional (taken : Bool)
  deriving DecidableEq

namespace Extended

/-- The existing internal rules with their primitive kind retained. Structural
and evaluation contexts are unchanged. Erasure is exactly Reduction below. -/
inductive InternalStep : InternalKind → {V : Type} → Extended V → Extended V → Prop where
  | atomComm (c : Nat) (x : V) (p : Agent V) (q : Agent (Option V)) :
      InternalStep .communication (.plain (.par (.output c (.var x) p) (.input c q)))
        (.plain (.par p (q.bind (.var x))))
  | thenBranch (f : Formula Empty) (p q : Agent V) (hf : f.Holds Empty.elim) :
      InternalStep (.conditional true) (.plain (.branch (f.subst Empty.elim) p q)) (.plain p)
  | elseBranch (f : Formula Empty) (p q : Agent V) (hf : ¬ f.Holds Empty.elim) :
      InternalStep (.conditional false) (.plain (.branch (f.subst Empty.elim) p q)) (.plain q)
  | parLeft {a b : Extended V} (c : Extended V) :
      InternalStep kind a b → InternalStep kind (.par a c) (.par b c)
  | parRight (a : Extended V) {b c : Extended V} :
      InternalStep kind b c → InternalStep kind (.par a b) (.par a c)
  | newVar {a b : Extended (Option V)} :
      InternalStep kind a b → InternalStep kind (.newVar a) (.newVar b)
  | congr {a a' b b' : Extended V} :
      Structural a a' → InternalStep kind a' b' → Structural b' b → InternalStep kind a b

theorem InternalStep.reduction {kind : InternalKind} {a b : Extended V}
    (h : InternalStep kind a b) : Reduction a b := by
  induction h with
  | atomComm => exact .atomComm _ _ _ _
  | thenBranch f p q hf => exact .thenBranch f p q hf
  | elseBranch f p q hf => exact .elseBranch f p q hf
  | parLeft c h ih => exact .parLeft c ih
  | parRight a h ih => exact .parRight a ih
  | newVar h ih => exact .newVar ih
  | congr hs h ht ih => exact .congr hs ih ht

theorem Reduction.classify {a b : Extended V} (h : Reduction a b) :
    ∃ kind, InternalStep kind a b := by
  induction h with
  | atomComm => exact ⟨.communication,.atomComm _ _ _ _⟩
  | thenBranch f p q hf => exact ⟨.conditional true,.thenBranch f p q hf⟩
  | elseBranch f p q hf => exact ⟨.conditional false,.elseBranch f p q hf⟩
  | parLeft c h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.parLeft c hk⟩
  | parRight a h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.parRight a hk⟩
  | newVar h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.newVar hk⟩
  | congr hs h ht ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.congr hs hk ht⟩

theorem reduction_iff_classified (a b : Extended V) :
    Reduction a b ↔ ∃ kind, InternalStep kind a b :=
  ⟨Reduction.classify,fun ⟨_,h⟩ => h.reduction⟩

end Extended

namespace Named

inductive InternalStep : InternalKind → {V : Type} → Named V → Named V → Prop where
  | embed {a b : Extended V} : Extended.InternalStep kind a b → InternalStep kind (.embed a) (.embed b)
  | parLeft {a b : Named V} (c : Named V) :
      InternalStep kind a b → InternalStep kind (.par a c) (.par b c)
  | parRight (a : Named V) {b c : Named V} :
      InternalStep kind b c → InternalStep kind (.par a b) (.par a c)
  | newName (n : SourceName) {a b : Named V} :
      InternalStep kind a b → InternalStep kind (.newName n a) (.newName n b)
  | newVar {a b : Named (Option V)} :
      InternalStep kind a b → InternalStep kind (.newVar a) (.newVar b)
  | congr {a a' b b' : Named V} :
      Structural a a' → InternalStep kind a' b' → Structural b' b → InternalStep kind a b

theorem InternalStep.reduction {kind : InternalKind} {a b : Named V}
    (h : InternalStep kind a b) : Reduction a b := by
  induction h with
  | embed h => exact .embed h.reduction
  | parLeft c h ih => exact .parLeft c ih
  | parRight a h ih => exact .parRight a ih
  | newName n h ih => exact .newName n ih
  | newVar h ih => exact .newVar ih
  | congr hs h ht ih => exact .congr hs ih ht

theorem Reduction.classify {a b : Named V} (h : Reduction a b) :
    ∃ kind, InternalStep kind a b := by
  induction h with
  | embed h => obtain ⟨kind,hk⟩ := h.classify; exact ⟨kind,.embed hk⟩
  | parLeft c h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.parLeft c hk⟩
  | parRight a h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.parRight a hk⟩
  | newName n h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.newName n hk⟩
  | newVar h ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.newVar hk⟩
  | congr hs h ht ih => obtain ⟨kind,hk⟩ := ih; exact ⟨kind,.congr hs hk ht⟩

theorem reduction_iff_classified (a b : Named V) :
    Reduction a b ↔ ∃ kind, InternalStep kind a b :=
  ⟨Reduction.classify,fun ⟨_,h⟩ => h.reduction⟩

theorem InternalStep.restrictNames {kind : InternalKind} {a b : Named V}
    (h : InternalStep kind a b) (ns : List SourceName) :
    InternalStep kind (Named.restrictNames ns a) (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact .newName n ih

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
