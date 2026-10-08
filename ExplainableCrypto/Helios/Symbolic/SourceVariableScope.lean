import ExplainableCrypto.Helios.Symbolic.SourceFrameInternal

namespace ExplainableCrypto.Helios.Symbolic.Term
variable {V W : Type}

/-- Every free variable occurs in the allowed scope; all term positions count. -/
def VarsIn (s : V → Prop) : Term V → Prop
  | .name _ | .const _ => True
  | .var v => s v
  | .unary _ t => t.VarsIn s
  | .binary _ a b => a.VarsIn s ∧ b.VarsIn s
  | .ternary _ a b c => a.VarsIn s ∧ b.VarsIn s ∧ c.VarsIn s
  | .spk a b c d => a.VarsIn s ∧ b.VarsIn s ∧ c.VarsIn s ∧ d.VarsIn s

theorem varsIn_all (t : Term V) : t.VarsIn (fun _ => True) := by
  induction t <;> simp_all [VarsIn]

theorem varsIn_mono (t : Term V) {s t' : V → Prop} (h : t.VarsIn s) (hs : ∀ v, s v → t' v) :
    t.VarsIn t' := by
  induction t <;> simp_all [VarsIn]

theorem varsIn_subst (t : Term V) {s : V → Prop} {s' : W → Prop} (σ : V → Term W)
    (h : t.VarsIn s) (hσ : ∀ v, s v → (σ v).VarsIn s') : (t.subst σ).VarsIn s' := by
  induction t <;> simp_all [VarsIn,subst]
end ExplainableCrypto.Helios.Symbolic.Term

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

def binderScope (s : V → Prop) : Option V → Prop
  | none => True
  | some v => s v

namespace Formula

def VarsIn (s : V → Prop) : Formula V → Prop
  | .equal a b | .unequal a b => a.VarsIn s ∧ b.VarsIn s
  | .both a b => a.VarsIn s ∧ b.VarsIn s

theorem varsIn_all (f : Formula V) : f.VarsIn (fun _ => True) := by
  induction f <;> simp_all [VarsIn,Term.varsIn_all]

theorem varsIn_mono (f : Formula V) {s t : V → Prop} (h : f.VarsIn s) (hs : ∀ v, s v → t v) :
    f.VarsIn t := by
  induction f with
  | equal a b | unequal a b => exact ⟨a.varsIn_mono h.1 hs,b.varsIn_mono h.2 hs⟩
  | both a b ha hb => exact ⟨ha h.1,hb h.2⟩

theorem varsIn_subst (f : Formula V) {s : V → Prop} {s' : W → Prop} (σ : V → Term W)
    (h : f.VarsIn s) (hσ : ∀ v, s v → (σ v).VarsIn s') : (f.subst σ).VarsIn s' := by
  induction f with
  | equal a b | unequal a b => exact ⟨a.varsIn_subst σ h.1 hσ,b.varsIn_subst σ h.2 hσ⟩
  | both a b ha hb => exact ⟨ha h.1,hb h.2⟩
end Formula

namespace Agent

def VarsIn : {V : Type} → (V → Prop) → Agent V → Prop
  | _, _, .nil => True
  | _, s, .par p q => p.VarsIn s ∧ q.VarsIn s
  | _, s, .output _ m p => m.VarsIn s ∧ p.VarsIn s
  | _, s, .input _ p => p.VarsIn (binderScope s)
  | _, s, .branch f p q => f.VarsIn s ∧ p.VarsIn s ∧ q.VarsIn s

theorem varsIn_all (p : Agent V) : p.VarsIn (fun _ => True) := by
  induction p with
  | nil => trivial
  | par p q hp hq => exact ⟨hp,hq⟩
  | output c m p hp => exact ⟨m.varsIn_all,hp⟩
  | branch f p q hp hq => exact ⟨f.varsIn_all,hp,hq⟩
  | input c p hp =>
    rename_i V'
    have he : binderScope (fun _ : V' => True) = (fun _ => True) := by funext v; cases v <;> rfl
    simpa only [VarsIn,he] using hp

theorem varsIn_mono (p : Agent V) {s t : V → Prop} (h : p.VarsIn s) (hs : ∀ v, s v → t v) :
    p.VarsIn t := by
  induction p with
  | nil => trivial
  | par p q hp hq => exact ⟨hp h.1 hs,hq h.2 hs⟩
  | output c m p hp => exact ⟨m.varsIn_mono h.1 hs,hp h.2 hs⟩
  | branch f p q hp hq => exact ⟨f.varsIn_mono h.1 hs,hp h.2.1 hs,hq h.2.2 hs⟩
  | input c p hp =>
    apply hp h
    intro v hv
    cases v with
    | none => trivial
    | some v => exact hs v hv

theorem varsIn_subst (p : Agent V) {s : V → Prop} {s' : W → Prop} (σ : V → Term W)
    (h : p.VarsIn s) (hσ : ∀ v, s v → (σ v).VarsIn s') : (p.subst σ).VarsIn s' := by
  induction p generalizing W with
  | nil => trivial
  | par p q hp hq => exact ⟨hp σ h.1 hσ,hq σ h.2 hσ⟩
  | output c m p hp => exact ⟨m.varsIn_subst σ h.1 hσ,hp σ h.2 hσ⟩
  | branch f p q hp hq => exact ⟨f.varsIn_subst σ h.1 hσ,hp σ h.2.1 hσ,hq σ h.2.2 hσ⟩
  | input c p hp =>
    apply hp (liftSubst σ) h
    intro v hv
    cases v with
    | none => trivial
    | some v =>
      apply Term.varsIn_subst (σ v) (fun w => .var (some w)) (hσ v hv)
      intro w hw
      exact hw
end Agent
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
