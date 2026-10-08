import ExplainableCrypto.Helios.Symbolic.SourceNameScoped

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

theorem groundTerm_mapNames (m : Ground) (f : Nat → Nat) :
    (groundTerm m : Term V).mapNames f = groundTerm (m.mapNames f) := by
  simp only [groundTerm,Term.mapNames_subst]
  congr 1
  funext v
  exact v.elim

theorem groundAgent_mapNames (p : Agent Empty) (f g : Nat → Nat) :
    (groundAgent p : Agent V).mapNames f g = groundAgent (p.mapNames f g) := by
  simp only [groundAgent,Agent.mapNames_subst]
  congr 1
  funext v
  exact v.elim

theorem frameEntries_mapNames (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (f g : Nat → Nat) :
    (frameEntries h vars values).mapNames f g = frameEntries h vars (fun i => (values i).mapNames f) := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [frameEntries,Extended.mapNames,groundTerm_mapNames,ih]

theorem activeFrame_mapNames (φ : Frame restricted handles) (f g : Nat → Nat) :
    (activeFrame φ).mapNames f g = activeFrame (φ.mapNames f) :=
  frameEntries_mapNames handles id φ.value f g

theorem frameProcess_mapNames (φ : Frame restricted handles) (p : Agent Empty) (f g : Nat → Nat) :
    (frameProcess φ p).mapNames f g = frameProcess (φ.mapNames f) (p.mapNames f g) := by
  simp only [frameProcess,Extended.mapNames,activeFrame_mapNames,groundAgent_mapNames]

theorem capture_mapNames (m : Term V) (p : Agent V) (f g : Nat → Nat) :
    (capture m p).mapNames f g = capture (m.mapNames f) (p.mapNames f g) := by
  simp only [capture,Extended.mapNames,shiftTerm_mapNames,Agent.shift,Agent.mapNames_subst,Term.mapNames]

theorem frameProcess_reduction_mapNames_iff (φ ψ : Frame restricted handles) (p q : Agent Empty) (e k : Nat ≃ Nat) :
    Reduction (frameProcess (φ.mapNames e) (p.mapNames e k)) (frameProcess (ψ.mapNames e) (q.mapNames e k)) ↔
      Reduction (frameProcess φ p) (frameProcess ψ q) := by
  simpa only [frameProcess_mapNames] using Reduction.mapNames_iff (frameProcess φ p) (frameProcess ψ q) e k

/-- Exact captured output commutes with name mapping before fresh-handle
canonicalization; all old active values and the complete new value are kept. -/
theorem frame_capture_mapNames (φ : Frame restricted handles) (m : Ground) (p : Agent Empty) (f g : Nat → Nat) :
    (Extended.par ((activeFrame φ).rename some) (capture (groundTerm m) (groundAgent p))).mapNames f g =
      .par ((activeFrame (φ.mapNames f)).rename some) (capture (groundTerm (m.mapNames f)) (groundAgent (p.mapNames f g))) := by
  simp only [Extended.mapNames,mapNames_rename,activeFrame_mapNames,capture_mapNames,groundTerm_mapNames,groundAgent_mapNames]
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
