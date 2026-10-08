import ExplainableCrypto.Helios.Symbolic.SourceNameExtended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

def FreeLabel.mapNames (f g : Nat → Nat) : FreeLabel V → FreeLabel V
  | .input c m => .input (g c) (m.mapNames f)
  | .output c x => .output (g c) x

theorem FreeLabel.mapNames_inverse (l : FreeLabel V) (e k : Nat ≃ Nat) :
    (l.mapNames e k).mapNames e.symm k.symm = l := by
  cases l <;> simp only [FreeLabel.mapNames,Term.mapNames_inverse,Equiv.symm_apply_apply]

theorem FreeStep.mapNames {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) (f g : Nat → Nat) :
    FreeStep (a.mapNames f g) (l.mapNames f g) (b.mapNames f g) := by
  induction h with
  | input c m p =>
    simpa only [Extended.mapNames,FreeLabel.mapNames,Agent.mapNames,Agent.mapNames_bind] using FreeStep.input (g c) (m.mapNames f) (p.mapNames f g)
  | output c x p => exact .output _ _ _
  | scopeInput h ih =>
    apply FreeStep.scopeInput
    simpa only [FreeLabel.mapNames,shiftTerm_mapNames] using ih
  | scopeOutput h ih => exact .scopeOutput ih
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | congr hp h hq ih => exact .congr (hp.mapNames f g) ih (hq.mapNames f g)

theorem FreeStep.mapNames_iff (a b : Extended V) (l : FreeLabel V) (e k : Nat ≃ Nat) :
    FreeStep (a.mapNames e k) (l.mapNames e k) (b.mapNames e k) ↔ FreeStep a l b := by
  constructor
  · intro h
    simpa only [Extended.mapNames_inverse,FreeLabel.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

/-- Exported variables retain their identity. Scope still exchanges the two
variable binders, independently of both name sorts. -/
theorem BoundOutput.mapNames {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (f g : Nat → Nat) :
    BoundOutput (a.mapNames f g) (g c) (b.mapNames f g) := by
  induction h with
  | openAtom h => exact .openAtom (h.mapNames f g)
  | scope h ih =>
    simpa only [Extended.mapNames,Extended.mapNames_rename] using BoundOutput.scope ih
  | parLeft d h ih =>
    simpa only [Extended.mapNames,Extended.mapNames_rename] using BoundOutput.parLeft (d.mapNames f g) ih
  | parRight a h ih =>
    simpa only [Extended.mapNames,Extended.mapNames_rename] using BoundOutput.parRight (a.mapNames f g) ih
  | congr hp h hq ih => exact .congr (hp.mapNames f g) ih (hq.mapNames f g)

theorem BoundOutput.mapNames_iff (a : Extended V) (b : Extended (Option V)) (c : Nat) (e k : Nat ≃ Nat) :
    BoundOutput (a.mapNames e k) (k c) (b.mapNames e k) ↔ BoundOutput a c b := by
  constructor
  · intro h
    simpa only [Extended.mapNames_inverse,Equiv.symm_apply_apply] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
