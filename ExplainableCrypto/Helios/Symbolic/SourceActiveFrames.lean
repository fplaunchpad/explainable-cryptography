import ExplainableCrypto.Helios.Symbolic.SourceExtendedRenaming
import Mathlib.Logic.Equiv.Fin.Basic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type} {restricted : Finset Nat} {handles : Nat}

/-- A finite source frame of full ground payloads. Its recursive order puts the
last handle first; parallel structure makes that presentation immaterial. -/
def frameEntries : (h : Nat) → (Fin h → V) → (Fin h → Ground) → Extended V
  | 0, _, _ => .plain .nil
  | h+1, vars, values => .par (.active (vars (Fin.last h)) (groundTerm (values (Fin.last h))))
      (frameEntries h (fun i => vars i.castSucc) (fun i => values i.castSucc))

def activeFrame (φ : Frame restricted handles) : Extended (Fin handles) :=
  frameEntries handles id φ.value

/-- Ground process attached to the actual public active substitutions. -/
def frameProcess (φ : Frame restricted handles) (p : Agent Empty) : Extended (Fin handles) :=
  .par (activeFrame φ) (.plain (groundAgent p))

theorem frameEntries_rename (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (f : V → W) :
    (frameEntries h vars values).rename f = frameEntries h (f ∘ vars) values := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [frameEntries,rename,groundTerm_rename,ih,Function.comp_def]

/-- The source frame of an extended public view adds precisely the new full
payload at the last handle and retains every previous active substitution. -/
theorem activeFrame_extend (φ : Frame restricted handles) (m : Ground) :
    activeFrame (φ.extend m) =
      .par (.active (Fin.last handles) (groundTerm m)) ((activeFrame φ).rename Fin.castSucc) := by
  simp only [activeFrame,frameEntries,Frame.extend_last,Frame.extend_old,frameEntries_rename,Function.comp_def,id]

/-- Explicit correspondence between a fresh source binder and the canonical
last handle. This is a bijection, so old handles cannot be captured. -/
def outputHandle : Option (Fin handles) ≃ Fin (handles+1) := finSuccEquivLast.symm

@[simp]
theorem outputHandle_none : outputHandle (none : Option (Fin handles)) = Fin.last handles :=
  finSuccEquivLast_symm_none

@[simp]
theorem outputHandle_some (i : Fin handles) : outputHandle (some i) = i.castSucc :=
  finSuccEquivLast_symm_some i

/-- Both fresh-source and canonical-last naming preserve every old handle. -/
theorem outputHandle_fresh (i : Fin handles) : outputHandle none ≠ outputHandle (some i) := by
  intro h
  have he := outputHandle.injective h
  cases he

/-- An output beside the existing frame produces a concrete active binding,
with its full old context shifted past the new exported variable. -/
theorem frame_output_derivable (φ : Frame restricted handles) (c : Nat) (m : Ground) (p : Agent Empty) :
    BoundOutput (frameProcess φ (.output c m p)) c
      (.par ((activeFrame φ).rename some) (capture (groundTerm m) (groundAgent p))) :=
  message_output_in_context (activeFrame φ) c (groundTerm m) (groundAgent p)

/-- Renaming the bound-output target to canonical handles yields the actual
extended public frame and continuation, modulo only source parallel laws. -/
theorem frame_output_capture (φ : Frame restricted handles) (m : Ground) (p : Agent Empty) :
    Structural
      ((Extended.par ((activeFrame φ).rename some) (capture (groundTerm m) (groundAgent p))).rename outputHandle)
      (frameProcess (φ.extend m) p) := by
  simp only [rename,capture,rename_comp,groundTerm_rename,groundAgent_rename,Agent.shift,shiftTerm,
    outputHandle_none,frameProcess,activeFrame_extend]
  have he : (outputHandle ∘ some : Fin handles → Fin (handles+1)) = Fin.castSucc := by
    funext i
    exact outputHandle_some i
  rw [he]
  exact (Structural.assoc _ _ _).symm.trans (Structural.parLeft _ (Structural.comm _ _))
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
