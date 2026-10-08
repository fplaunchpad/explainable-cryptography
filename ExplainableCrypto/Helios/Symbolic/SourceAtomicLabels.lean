import ExplainableCrypto.Helios.Symbolic.SourceExtendedInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

/-- Free source labels in the finite static-channel/base-variable fragment. -/
inductive FreeLabel (V : Type) where
  | input : Nat → Term V → FreeLabel V
  | output : Nat → V → FreeLabel V

/-- Source In/Out-Atom, variable Scope, Par and Struct. Input scope requires a
shifted term, and output scope an old variable, so neither mentions the binder. -/
inductive FreeStep : {V : Type} → Extended V → FreeLabel V → Extended V → Prop where
  | input (c : Nat) (m : Term V) (p : Agent (Option V)) :
      FreeStep (.plain (.input c p)) (.input c m) (.plain (p.bind m))
  | output (c : Nat) (x : V) (p : Agent V) :
      FreeStep (.plain (.output c (.var x) p)) (.output c x) (.plain p)
  | scopeInput {a b : Extended (Option V)} {c : Nat} {m : Term V} :
      FreeStep a (.input c (shiftTerm m)) b → FreeStep (.newVar a) (.input c m) (.newVar b)
  | scopeOutput {a b : Extended (Option V)} {c : Nat} {x : V} :
      FreeStep a (.output c (some x)) b → FreeStep (.newVar a) (.output c x) (.newVar b)
  | parLeft {a b : Extended V} {l : FreeLabel V} (c : Extended V) :
      FreeStep a l b → FreeStep (.par a c) l (.par b c)
  | parRight (a : Extended V) {b c : Extended V} {l : FreeLabel V} :
      FreeStep b l c → FreeStep (.par a b) l (.par a c)
  | congr {a a' b b' : Extended V} {l : FreeLabel V} :
      Structural a a' → FreeStep a' l b' → Structural b' b → FreeStep a l b

/-- Exchange an enclosing restricted variable with a newly exported variable.
Both remain separate from every older variable. -/
def swapBinders : Option (Option V) → Option (Option V)
  | none => some none
  | some none => none
  | some (some v) => some (some v)

/-- Bound variable output νx.c<x>. Open-Atom removes its variable restriction.
Variables and static channel names have different sorts, so x≠c is automatic.
Par shifts the untouched context; Scope exchanges the two fresh binders. -/
inductive BoundOutput : {V : Type} → Extended V → Nat → Extended (Option V) → Prop where
  | openAtom {a b : Extended (Option V)} {c : Nat} :
      FreeStep a (.output c none) b → BoundOutput (.newVar a) c b
  | scope {a : Extended (Option V)} {b : Extended (Option (Option V))} {c : Nat} :
      BoundOutput a c b → BoundOutput (.newVar a) c (.newVar (b.rename swapBinders))
  | parLeft {a : Extended V} {b : Extended (Option V)} {c : Nat} (d : Extended V) :
      BoundOutput a c b → BoundOutput (.par a d) c (.par b (d.rename some))
  | parRight (a : Extended V) {b : Extended V} {d : Extended (Option V)} {c : Nat} :
      BoundOutput b c d → BoundOutput (.par a b) c (.par (a.rename some) d)
  | congr {a a' : Extended V} {b b' : Extended (Option V)} {c : Nat} :
      Structural a a' → BoundOutput a' c b' → Structural b' b → BoundOutput a c b
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
