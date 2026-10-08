import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

inductive Reduction : {V : Type} → Named V → Named V → Prop where
  | embed {a b : Extended V} : Extended.Reduction a b → Reduction (.embed a) (.embed b)
  | parLeft {a b : Named V} (c : Named V) : Reduction a b → Reduction (.par a c) (.par b c)
  | parRight (a : Named V) {b c : Named V} : Reduction b c → Reduction (.par a b) (.par a c)
  | newName (n : SourceName) {a b : Named V} : Reduction a b → Reduction (.newName n a) (.newName n b)
  | newVar {a b : Named (Option V)} : Reduction a b → Reduction (.newVar a) (.newVar b)
  | congr {a a' b b' : Named V} : Structural a a' → Reduction a' b' → Structural b' b → Reduction a b

/-- Name Scope checks the complete free label. Variable Scope uses the existing
typed shift; no name freshness condition is replaced by variable freshness. -/
inductive FreeStep : {V : Type} → Named V → Extended.FreeLabel V → Named V → Prop where
  | embed {a b : Extended V} {l : Extended.FreeLabel V} : Extended.FreeStep a l b → FreeStep (.embed a) l (.embed b)
  | scopeName (n : SourceName) {a b : Named V} {l : Extended.FreeLabel V}
      (hf : n ∉ l.nameSupport) : FreeStep a l b → FreeStep (.newName n a) l (.newName n b)
  | scopeInput {a b : Named (Option V)} {c : Nat} {m : Term V} :
      FreeStep a (.input c (shiftTerm m)) b → FreeStep (.newVar a) (.input c m) (.newVar b)
  | scopeOutput {a b : Named (Option V)} {c : Nat} {x : V} :
      FreeStep a (.output c (some x)) b → FreeStep (.newVar a) (.output c x) (.newVar b)
  | parLeft {a b : Named V} {l : Extended.FreeLabel V} (c : Named V) :
      FreeStep a l b → FreeStep (.par a c) l (.par b c)
  | parRight (a : Named V) {b c : Named V} {l : Extended.FreeLabel V} :
      FreeStep b l c → FreeStep (.par a b) l (.par a c)
  | congr {a a' b b' : Named V} {l : Extended.FreeLabel V} :
      Structural a a' → FreeStep a' l b' → Structural b' b → FreeStep a l b

/-- Open-Atom exports a base variable. Name restrictions remain in the target;
only the channel occurs as a name in this bound-variable label. Channel-valued
output/extrusion is outside the finite static-channel historical syntax. -/
inductive BoundOutput : {V : Type} → Named V → Nat → Named (Option V) → Prop where
  | embed {a : Extended V} {b : Extended (Option V)} {c : Nat} :
      Extended.BoundOutput a c b → BoundOutput (.embed a) c (.embed b)
  | openAtom {a b : Named (Option V)} {c : Nat} :
      FreeStep a (.output c none) b → BoundOutput (.newVar a) c b
  | scopeName (n : SourceName) {a : Named V} {b : Named (Option V)} {c : Nat}
      (hf : n ≠ .channel c) : BoundOutput a c b → BoundOutput (.newName n a) c (.newName n b)
  | scopeVar {a : Named (Option V)} {b : Named (Option (Option V))} {c : Nat} :
      BoundOutput a c b → BoundOutput (.newVar a) c (.newVar (b.rename Extended.swapBinders))
  | parLeft {a : Named V} {b : Named (Option V)} {c : Nat} (d : Named V) :
      BoundOutput a c b → BoundOutput (.par a d) c (.par b (d.rename some))
  | parRight (a : Named V) {b : Named V} {d : Named (Option V)} {c : Nat} :
      BoundOutput b c d → BoundOutput (.par a b) c (.par (a.rename some) d)
  | congr {a a' : Named V} {b b' : Named (Option V)} {c : Nat} :
      Structural a a' → BoundOutput a' c b' → Structural b' b → BoundOutput a c b

theorem Reduction.restrictNames {a b : Named V} (h : Reduction a b) (ns : List SourceName) :
    Reduction (Named.restrictNames ns a) (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact .newName n ih

theorem FreeStep.restrictNames {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (ns : List SourceName) (hf : ∀ n ∈ ns, n ∉ l.nameSupport) :
    FreeStep (Named.restrictNames ns a) l (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih =>
    exact .scopeName n (hf n (by simp)) (ih (fun m hm => hf m (by simp [hm])))

theorem BoundOutput.restrictNames {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (ns : List SourceName) (hf : ∀ n ∈ ns, n ≠ .channel c) :
    BoundOutput (Named.restrictNames ns a) c (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih =>
    exact .scopeName n (hf n (by simp)) (ih (fun m hm => hf m (by simp [hm])))
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
