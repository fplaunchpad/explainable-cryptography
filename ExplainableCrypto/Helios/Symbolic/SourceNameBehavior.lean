import ExplainableCrypto.Helios.Symbolic.SourceNameProcesses

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V : Type}

theorem ParEq.mapNames {p q : Agent V} (h : ParEq p q) (f g : Nat → Nat) :
    ParEq (p.mapNames f g) (q.mapNames f g) := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | zero => exact .zero _
  | assoc => exact .assoc _ _ _
  | comm => exact .comm _ _
  | par h h' ih ih' => exact .par ih ih'

/-- Both ground equality and disequality decisions survive a base-name
permutation. Channel permutations move every channel consistently. -/
theorem CoreStep.mapNames {p q : Agent Empty} (h : CoreStep p q) (e k : Nat ≃ Nat) :
    CoreStep (p.mapNames e k) (q.mapNames e k) := by
  induction h with
  | comm c m p q =>
    simpa only [Agent.mapNames,Agent.mapNames_bind] using CoreStep.comm (k c) (m.mapNames e) (p.mapNames e k) (q.mapNames e k)
  | thenBranch f p q hf => exact .thenBranch _ _ _ ((Formula.holds_mapNames_ground f e).mpr hf)
  | elseBranch f p q hf => exact .elseBranch _ _ _ (fun h => hf ((Formula.holds_mapNames_ground f e).mp h))
  | parLeft q h ih => exact .parLeft _ ih
  | parRight p h ih => exact .parRight _ ih

theorem CoreStep.mapNames_iff (p q : Agent Empty) (e k : Nat ≃ Nat) :
    CoreStep (p.mapNames e k) (q.mapNames e k) ↔ CoreStep p q := by
  constructor
  · intro h
    simpa only [Agent.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem Tau.mapNames {p q : Agent Empty} (h : Tau p q) (e k : Nat ≃ Nat) :
    Tau (p.mapNames e k) (q.mapNames e k) := by
  obtain ⟨p',q',hp,hc,hq⟩ := h
  exact ⟨_,_,hp.mapNames e k,hc.mapNames e k,hq.mapNames e k⟩

theorem Tau.mapNames_iff (p q : Agent Empty) (e k : Nat ≃ Nat) :
    Tau (p.mapNames e k) (q.mapNames e k) ↔ Tau p q := by
  constructor
  · intro h
    simpa only [Agent.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

def PayloadEvent.mapNames (f g : Nat → Nat) : PayloadEvent → PayloadEvent
  | .input c m => .input (g c) (m.mapNames f)
  | .output c m => .output (g c) (m.mapNames f)

theorem PayloadEvent.mapNames_inverse (a : PayloadEvent) (e k : Nat ≃ Nat) :
    (a.mapNames e k).mapNames e.symm k.symm = a := by
  cases a <;> simp only [PayloadEvent.mapNames,Term.mapNames_inverse,Equiv.symm_apply_apply]

theorem CoreVisible.mapNames {p q : Agent Empty} {a : PayloadEvent} (h : CoreVisible p a q) (f g : Nat → Nat) :
    CoreVisible (p.mapNames f g) (a.mapNames f g) (q.mapNames f g) := by
  induction h with
  | input c m p =>
    simpa only [Agent.mapNames,PayloadEvent.mapNames,Agent.mapNames_bind] using CoreVisible.input (g c) (m.mapNames f) (p.mapNames f g)
  | output c m p => exact .output _ _ _
  | parLeft r h ih => exact .parLeft _ ih
  | parRight r h ih => exact .parRight _ ih

theorem Visible.mapNames {p q : Agent Empty} {a : PayloadEvent} (h : Visible p a q) (f g : Nat → Nat) :
    Visible (p.mapNames f g) (a.mapNames f g) (q.mapNames f g) := by
  obtain ⟨p',q',hp,hv,hq⟩ := h
  exact ⟨_,_,hp.mapNames f g,hv.mapNames f g,hq.mapNames f g⟩

theorem Visible.mapNames_iff (p q : Agent Empty) (a : PayloadEvent) (e k : Nat ≃ Nat) :
    Visible (p.mapNames e k) (a.mapNames e k) (q.mapNames e k) ↔ Visible p a q := by
  constructor
  · intro h
    simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
