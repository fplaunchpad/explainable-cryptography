import ExplainableCrypto.Helios.Symbolic.SourceGuardRetractions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V : Type}

/-- Recover only currently ready guards. Future guards under either prefix or
under a branch continuation are deliberately not premises for this one step. -/
def ReadyGuardsRetract (p : Agent V) (f g : Nat → Nat) : Prop :=
  match p with
  | .par p q => p.ReadyGuardsRetract f g ∧ q.ReadyGuardsRetract f g
  | .branch φ _ _ => φ.NameRetracts f g
  | _ => True

theorem ReadyGuardsRetract.of_inverse (p : Agent V) (e : Nat ≃ Nat) :
    p.ReadyGuardsRetract e e.symm := by
  induction p <;> simp_all only [ReadyGuardsRetract,Formula.NameRetracts.of_inverse,and_self]

theorem readyGuardsRetract_of_no_conditional (p : Agent V) (f g : Nat → Nat)
    (h : ¬ p.HasConditional) : p.ReadyGuardsRetract f g := by
  induction p with
  | nil => trivial
  | output => trivial
  | input => trivial
  | branch => exact (h trivial).elim
  | par p q hp hq => exact ⟨hp (fun h' => h (.inl h')),hq (fun h' => h (.inr h'))⟩

theorem ParEq.readyGuardsRetract {p q : Agent V} (h : ParEq p q) (f g : Nat → Nat) :
    p.ReadyGuardsRetract f g ↔ q.ReadyGuardsRetract f g := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | zero => simp [ReadyGuardsRetract]
  | assoc => exact and_assoc
  | comm => exact and_comm
  | par h j ih ij => exact and_congr ih ij

theorem EquivE.readyGuardsRetract {p q : Agent V} (h : EquivE p q) (f g : Nat → Nat) :
    p.ReadyGuardsRetract f g ↔ q.ReadyGuardsRetract f g := by
  induction h with
  | nil => rfl
  | input => rfl
  | output => rfl
  | par h j ih ij => exact and_congr ih ij
  | branch hf h j ih ij => exact ⟨fun h => h.congr hf,fun h => h.congr hf.symm⟩

theorem EvalEq.readyGuardsRetract {p q : Agent V} (h : EvalEq p q) (f g : Nat → Nat) :
    p.ReadyGuardsRetract f g ↔ q.ReadyGuardsRetract f g := by
  obtain ⟨r,hp,hq⟩ := h
  exact (hp.readyGuardsRetract f g).trans (hq.readyGuardsRetract f g)

theorem CoreStep.mapNames_of_guard_retractions {p q : Agent Empty} (h : CoreStep p q)
    (f g k : Nat → Nat) (hr : p.ReadyGuardsRetract f g) :
    CoreStep (p.mapNames f k) (q.mapNames f k) := by
  induction h with
  | comm c m p q =>
    simpa only [Agent.mapNames,Agent.mapNames_bind] using
      CoreStep.comm (k c) (m.mapNames f) (p.mapNames f k) (q.mapNames f k)
  | thenBranch φ p q hh =>
    exact .thenBranch _ _ _ (hr.holds_mapNames.mpr hh)
  | elseBranch φ p q hh =>
    exact .elseBranch _ _ _ (fun h' => hh (hr.holds_mapNames.mp h'))
  | parLeft c h ih => exact .parLeft _ (ih hr.1)
  | parRight c h ih => exact .parRight _ (ih hr.2)

/-- A full actual internal step, including arbitrary parallel representatives,
maps to the same branch and complete mapped target under this semantic condition.
The channel map is arbitrary; this is forward transport, not reflection. -/
theorem Tau.mapNames_of_guard_retractions {p q : Agent Empty} (h : Tau p q)
    (f g k : Nat → Nat) (hr : p.ReadyGuardsRetract f g) :
    Tau (p.mapNames f k) (q.mapNames f k) := by
  obtain ⟨p',q',hp,hstep,hq⟩ := h
  exact ⟨_,_,hp.mapNames f k,
    hstep.mapNames_of_guard_retractions f g k ((hp.readyGuardsRetract f g).mp hr),hq.mapNames f k⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
