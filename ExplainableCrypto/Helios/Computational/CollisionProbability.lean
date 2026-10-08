import ExplainableCrypto.Helios.Computational.HonestBallot

/-! Bounds for the nonce event needed by the concrete proof-reuse attack. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp

variable {F : Type} [Field F] [Fintype F]

noncomputable def noncePointBound (F : Type) [Fintype F] : ENNReal :=
  ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹

theorem sampleNonzero_point_le (r : F) :
    Pr[= r | sampleNonzero F] ≤ noncePointBound F := by
  classical
  let : DecidableEq F := Classical.decEq F
  by_cases hr : r = (0 : F)
  · subst r
    rw [probOutput_eq_zero_of_not_mem_support (fun h => sampleNonzero_ne_zero h rfl)]
    exact zero_le
  · exact le_of_eq (sampleNonzero_probability (Units.mk0 r hr))

theorem sampleNonzero_noFailure : Pr[⊥ | sampleNonzero F] = 0 := by
  simp [sampleNonzero]

def BlockedNonce (r0 r1 s : F) : Prop := s = r0 ∨ s = r1 ∨ s = r0 + r1

theorem blockedNonce_probability_le (r0 r1 : F) :
    Pr[BlockedNonce r0 r1 | sampleNonzero F] ≤ 3 * noncePointBound F := by
  have h0 := sampleNonzero_point_le r0
  have h1 := sampleNonzero_point_le r1
  have hs := sampleNonzero_point_le (r0 + r1)
  have houter := probEvent_or_le (sampleNonzero F) (fun s => s = r0)
    (fun s => s = r1 ∨ s = r0 + r1)
  have hinner := probEvent_or_le (sampleNonzero F) (fun s => s = r1)
    (fun s => s = r0 + r1)
  simp only [probEvent_eq_eq_probOutput] at houter hinner
  calc
    _ ≤ Pr[= r0 | sampleNonzero F] +
        (Pr[= r1 | sampleNonzero F] + Pr[= r0 + r1 | sampleNonzero F]) :=
      houter.trans (add_le_add_right hinner _)
    _ ≤ noncePointBound F + (noncePointBound F + noncePointBound F) :=
      add_le_add h0 (add_le_add h1 hs)
    _ = _ := by simp [show (3 : ENNReal) = 1 + (1 + 1) by norm_num, add_mul]

noncomputable def drawNoncePair (F : Type) [Field F] [Fintype F] : ProbComp (F × F) := do
  let r0 ← sampleNonzero F
  let r1 ← sampleNonzero F
  pure (r0, r1)

theorem drawNoncePair_second_event (p : F → Prop) :
    Pr[fun rs => p rs.2 | drawNoncePair F] = Pr[p | sampleNonzero F] := by
  unfold drawNoncePair
  rw [probEvent_bind_of_const (sampleNonzero F)
    (r := Pr[p | sampleNonzero F]) (by intro x hx; simp [Function.comp_def])]
  simp

theorem drawNoncePair_first_event (p : F → Prop) :
    Pr[fun rs => p rs.1 | drawNoncePair F] = Pr[p | sampleNonzero F] := by
  unfold drawNoncePair
  rw [probEvent_bind_bind_swap]
  rw [probEvent_bind_of_const (sampleNonzero F)
    (r := Pr[p | sampleNonzero F]) (by intro x hx; simp [Function.comp_def])]
  simp

theorem pairCollision_probability_le (r0 r1 : F) :
    Pr[fun rs => BlockedNonce r0 r1 rs.1 ∨ BlockedNonce r0 r1 rs.2 | drawNoncePair F] ≤
      6 * noncePointBound F := by
  calc
    _ ≤ Pr[fun rs => BlockedNonce r0 r1 rs.1 | drawNoncePair F] +
        Pr[fun rs => BlockedNonce r0 r1 rs.2 | drawNoncePair F] := probEvent_or_le _ _ _
    _ = Pr[BlockedNonce r0 r1 | sampleNonzero F] +
        Pr[BlockedNonce r0 r1 | sampleNonzero F] := by
      rw [drawNoncePair_first_event, drawNoncePair_second_event]
    _ ≤ 3 * noncePointBound F + 3 * noncePointBound F :=
      add_le_add (blockedNonce_probability_le _ _) (blockedNonce_probability_le _ _)
    _ = _ := by rw [← add_mul]; norm_num

#print axioms blockedNonce_probability_le
#print axioms pairCollision_probability_le

end ExplainableCrypto.Helios.Computational
