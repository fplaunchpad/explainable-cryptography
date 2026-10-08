import ExplainableCrypto.Helios.Symbolic.SourceInterpretationCapture
import ExplainableCrypto.Helios.Symbolic.SourceNameFrameEmbedding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

namespace Formula
variable {V : Type}

theorem EquivE.mapNames {p q : Formula V} (h : EquivE p q) (f : Nat → Nat) :
    EquivE (p.mapNames f) (q.mapNames f) := by
  induction h with
  | equal h h' => exact .equal (h.mapNames f) (h'.mapNames f)
  | unequal h h' => exact .unequal (h.mapNames f) (h'.mapNames f)
  | both h h' ih ih' => exact .both ih ih'

theorem equivE_mapNames_iff (p q : Formula V) (e : Nat ≃ Nat) :
    EquivE (p.mapNames e) (q.mapNames e) ↔ EquivE p q := by
  constructor
  · intro h
    have hi : (e.symm ∘ e : Nat → Nat) = id := by funext n; exact e.symm_apply_apply n
    simpa only [Formula.mapNames_comp,hi,Formula.mapNames_id] using h.mapNames e.symm
  · exact fun h => h.mapNames e
end Formula

namespace Agent
variable {V : Type}

theorem EquivE.mapNames {p q : Agent V} (h : EquivE p q) (f g : Nat → Nat) :
    EquivE (p.mapNames f g) (q.mapNames f g) := by
  induction h with
  | nil => exact .nil
  | par h h' ih ih' => exact .par ih ih'
  | output c hm h ih => exact .output (g c) (hm.mapNames f) ih
  | input c h ih => exact .input (g c) ih
  | branch hf h h' ih ih' => exact .branch (hf.mapNames f) ih ih'

theorem equivE_mapNames_iff (p q : Agent V) (e k : Nat ≃ Nat) :
    EquivE (p.mapNames e k) (q.mapNames e k) ↔ EquivE p q := by
  constructor
  · intro h
    simpa only [Agent.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem EvalEq.mapNames {p q : Agent V} (h : EvalEq p q) (f g : Nat → Nat) :
    EvalEq (p.mapNames f g) (q.mapNames f g) := by
  obtain ⟨r,hr,he⟩ := h
  exact ⟨r.mapNames f g,hr.mapNames f g,he.mapNames f g⟩

theorem evalEq_mapNames_iff (p q : Agent V) (e k : Nat ≃ Nat) :
    EvalEq (p.mapNames e k) (q.mapNames e k) ↔ EvalEq p q := by
  constructor
  · intro h
    simpa only [Agent.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k
end Agent

theorem extendEnv_mapNames (env : V → Ground) (m : Ground) (f : Nat → Nat) :
    (fun v => (extendEnv env m v).mapNames f) =
      extendEnv (fun v => (env v).mapNames f) (m.mapNames f) := by
  funext v
  cases v <;> rfl

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
