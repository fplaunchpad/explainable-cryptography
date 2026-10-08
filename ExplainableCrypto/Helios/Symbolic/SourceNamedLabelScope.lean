import ExplainableCrypto.Helios.Symbolic.SourceNamedVariableClosure

namespace ExplainableCrypto.Helios.Symbolic
namespace Term
variable {V W : Type}

theorem varsIn_rename_iff (m : Term V) (σ : V → W) (s : W → Prop) :
    (m.subst (fun v => .var (σ v))).VarsIn s ↔ m.VarsIn (fun v => s (σ v)) := by
  induction m <;> simp_all only [Term.subst,Term.VarsIn]
end Term

namespace Historical.General.Source
variable {V W : Type}

namespace Extended.FreeLabel

/-- The free-variable side of labelled-bisimulation admissibility. Full input
terms are checked, including every field of a proof payload. -/
def VarsIn (s : V → Prop) : Extended.FreeLabel V → Prop
  | .input _ m => m.VarsIn s
  | .output _ x => s x

def rename (σ : V → W) : Extended.FreeLabel V → Extended.FreeLabel W
  | .input c m => .input c (m.subst (fun v => .var (σ v)))
  | .output c x => .output c (σ x)

theorem varsIn_congr (l : Extended.FreeLabel V) {s t : V → Prop} (h : ∀ v, s v ↔ t v) :
    l.VarsIn s ↔ l.VarsIn t := by
  have he : s = t := funext (fun v => propext (h v))
  rw [he]

theorem varsIn_rename_iff (l : Extended.FreeLabel V) (σ : V → W) (s : W → Prop) :
    (l.rename σ).VarsIn s ↔ l.VarsIn (fun v => s (σ v)) := by
  cases l with
  | input c m => exact m.varsIn_rename_iff σ s
  | output => rfl

theorem varsIn_of_all (l : Extended.FreeLabel V) {s : V → Prop} (h : ∀ v, s v) : l.VarsIn s := by
  cases l with
  | input c m => exact m.varsIn_mono m.varsIn_all (fun v _ => h v)
  | output c x => exact h x

end Extended.FreeLabel
namespace Named

/-- Only fv(label) ⊆ dom(frame). Name freshness and equality observations
remain separate from this variable-domain condition. -/
def LabelScoped (a : Named V) (l : Extended.FreeLabel V) : Prop := l.VarsIn a.Exports

theorem labelScoped_of_all_exports (a : Named V) (l : Extended.FreeLabel V)
    (ha : ∀ v, a.Exports v) : a.LabelScoped l := l.varsIn_of_all ha

theorem Structural.labelScoped {a b : Named V} (h : Structural a b) (l : Extended.FreeLabel V) :
    a.LabelScoped l ↔ b.LabelScoped l := l.varsIn_congr h.exports

theorem Reduction.labelScoped {a b : Named V} (h : Reduction a b) (l : Extended.FreeLabel V) :
    a.LabelScoped l ↔ b.LabelScoped l := l.varsIn_congr h.exports

theorem FreeStep.labelScoped {a b : Named V} {k : Extended.FreeLabel V}
    (h : FreeStep a k b) (l : Extended.FreeLabel V) : a.LabelScoped l ↔ b.LabelScoped l :=
  l.varsIn_congr h.exports

/-- Old labels remain scoped exactly when their variables are shifted into
the output target. The fresh exported variable cannot replace an old handle. -/
theorem BoundOutput.shifted_labelScoped {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (l : Extended.FreeLabel V) :
    b.LabelScoped (l.rename some) ↔ a.LabelScoped l :=
  (l.varsIn_rename_iff some b.Exports).trans (l.varsIn_congr h.old_exports)

variable {restricted : Finset Nat} {handles : Nat}

theorem restrictedState_labelScoped (hidden : Finset Nat) (p : ScopedState restricted handles)
    (l : Extended.FreeLabel (Fin handles)) : (restrictedState hidden p).LabelScoped l :=
  labelScoped_of_all_exports _ l (restrictedState_all_exports hidden p)

/-- Every variable of the enlarged target type has a retained definition,
so future complete recipes over that type satisfy the variable-domain premise. -/
theorem restrictedState_bound_target_labelScoped (hidden : Finset Nat)
    (p : ScopedState restricted handles) {b : Named (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (restrictedState hidden p) c b) (l : Extended.FreeLabel (Option (Fin handles))) :
    b.LabelScoped l := labelScoped_of_all_exports _ l
      (h.all_exports (restrictedState_wellFormed hidden p).1 (restrictedState_all_exports hidden p))

end Named
end Historical.General.Source
end ExplainableCrypto.Helios.Symbolic
