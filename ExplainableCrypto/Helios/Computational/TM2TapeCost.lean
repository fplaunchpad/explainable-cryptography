import ExplainableCrypto.Helios.Computational.TM2ReturnLink
import Mathlib.Tactic.Linarith

/-! Quantitative bounds for Mathlib's existing stack-to-tape translation.
The compiler, tape relation and stack-action correctness are reused unchanged.
Bounds count TM1 ticks; primitive finite-syntax and native-oracle costs remain
separate parts of the standard-machine connection. -/
namespace ExplainableCrypto.Helios.Computational.TM2TapeCost
open Turing Function TM2to1 TM2to1.Λ'
variable {K : Type*} {Γ : K → Type*} {Λ V : Type*} [DecidableEq K]

abbrev Config := TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ V) V

def tick (M : Λ → TM2.Stmt Γ Λ V) (cfg : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V)) :=
  (TM1.step (tr M) cfg).getD cfg

/-- Maximum number of stack accesses on a statement branch. Local finite
load/branch syntax is interpreted within the enclosing TM1 tick. -/
def accesses : TM2.Stmt Γ Λ V → Nat
  | .push _ _ q | .peek _ _ q | .pop _ _ q => 1 + accesses q
  | .load _ q => accesses q
  | .branch _ a b => max (accesses a) (accesses b)
  | .goto _ | .halt => 0

/-- The existing outward scan takes exactly n TM1 ticks before the stack end. -/
theorem scan_right (M : Λ → TM2.Stmt Γ Λ V) {k : K} (o : StAct K Γ V k)
    (q : TM2.Stmt Γ Λ V) (v : V) {S : List (Γ k)}
    {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : Nat) (hn : n ≤ S.length) :
    (tick M)^[n] ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ =
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [tick, TM1.step, Option.getD_some, TM1.stepAux, tr,
      Tape.mk'_nth_nat, Tape.move_right_n_head, addBottom_nth_snd]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem (by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn)]
    rw [Function.iterate_succ_apply']
    rfl

/-- The existing return scan takes exactly n ticks back to the bottom marker. -/
theorem scan_left (M : Λ → TM2.Stmt Γ Λ V) (q : TM2.Stmt Γ Λ V) (v : V)
    (L : ListBlank (∀ k, Option (Γ k))) (n : Nat) :
    (tick M)^[n] ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hs : tick M ⟨some (ret q), v,
        (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ =
        ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [tick, TM1.step, Option.getD_some, tr, TM1.stepAux,
        Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]
      rw [Function.iterate_succ_apply', Tape.move_right_left]
      rfl
    rw [hs, ih]

/-- Reuse the existing exact top-of-stack action, retaining all other columns. -/
theorem top_action (M : Λ → TM2.Stmt Γ Λ V) {k : K}
    (q : TM2.Stmt Γ Λ V) (v : V) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ V k) :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ j, L'.map (proj j) =
        ListBlank.mk (((Function.update S k (stWrite v (S k) o)) j).map some).reverse) ∧
      tick M ⟨some (go k o q), v,
        (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        ⟨some (ret q), stVar v (S k) o,
          (Tape.move Dir.right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
  obtain ⟨L', hL', he⟩ := tr_respects_aux₂
    (q := TM1.Stmt.goto (fun _ _ => ret q)) hL o
  refine ⟨L', hL', ?_⟩
  simp only [tick, TM1.step, Option.getD_some, tr, TM1.stepAux,
    Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd]
  rw [stk_nth_val _ (hL k), List.getElem?_eq_none (by simp)]
  simpa only [Option.isNone, cond, TM1.stepAux, Function.update_self] using he

/-- One existing stack access includes the outward scan, top operation,
return scan and dispatch of the remaining statement. -/
theorem roundtrip (M : Λ → TM2.Stmt Γ Λ V) {k : K}
    (q : TM2.Stmt Γ Λ V) (v : V) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ V k) :
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ j, L'.map (proj j) =
        ListBlank.mk (((Function.update S k (stWrite v (S k) o)) j).map some).reverse) ∧
      (tick M)^[((stWrite v (S k) o).length + 1) + ((S k).length + 1)]
        ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ =
        TM1.stepAux (trNormal q) (stVar v (S k) o) (Tape.mk' ∅ (addBottom L')) := by
  obtain ⟨L', hL', he⟩ := top_action M q v S L hL o
  refine ⟨L', hL', ?_⟩
  have issued : (tick M)^[(S k).length + 1]
      ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ =
      ⟨some (ret q), stVar v (S k) o,
        (Tape.move Dir.right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
    rw [Function.iterate_succ_apply', scan_right M o q v (hL k) _ le_rfl, he]
  rw [Function.iterate_add_apply, issued, Function.iterate_succ_apply', scan_left]
  simp only [tick, TM1.step, Option.getD_some, tr, TM1.stepAux,
    Tape.mk'_head, addBottom_head_fst, cond]

omit [DecidableEq K] in
private theorem write_length {k : K} (v : V) (word : List (Γ k)) (o : StAct K Γ V k) :
    (stWrite v word o).length ≤ word.length + 1 := by
  cases o <;> simp only [stWrite, List.length_cons, List.length_tail] <;> omega

private theorem write_height {k : K} (v : V) (S : ∀ k, List (Γ k))
    (o : StAct K Γ V k) (H : Nat) (hH : ∀ j, (S j).length ≤ H) :
    ∀ j, ((Function.update S k (stWrite v (S k) o)) j).length ≤ H + 1 := by
  intro j
  by_cases hj : j = k
  · subst j
    rw [Function.update_self]
    have := write_length v (S k) o
    have := hH k
    omega
  · rw [Function.update_of_ne hj]
    have := hH j
    omega

/-- Bound after the initial translated entry tick, including growth during
this statement. Finite-domain restrictions on local functions are still needed
when translating TM1 ticks into primitive execution costs. -/
def work (H : Nat) (q : TM2.Stmt Γ Λ V) : Nat :=
  accesses q * (2 * (H + accesses q) + 2)

omit [DecidableEq K] in
private theorem work_mono (H : Nat) {a b : TM2.Stmt Γ Λ V}
    (hab : accesses a ≤ accesses b) : work H a ≤ work H b := by
  exact Nat.mul_le_mul hab (by omega)

/-- The complete existing translated statement has a derived TM1 tick bound
and retains Mathlib's full stack/tape relation. -/
theorem statement (M : Λ → TM2.Stmt Γ Λ V) (q : TM2.Stmt Γ Λ V)
    (H : Nat) (v : V) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (hH : ∀ k, (S k).length ≤ H) :
    ∃ used ≤ work H q, ∃ out,
      TrCfg (TM2.stepAux q v S) out ∧
      (tick M)^[used] (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) = out := by
  induction q using stmtStRec generalizing H v S L with
  | run k o q ih =>
    obtain ⟨L', hL', hr⟩ := roundtrip M q v S L hL o
    obtain ⟨used, hu, out, ho, he⟩ := ih (H + 1) (stVar v (S k) o)
      (Function.update S k (stWrite v (S k) o)) L' hL' (write_height v S o H hH)
    refine ⟨used + (((stWrite v (S k) o).length + 1) + ((S k).length + 1)), ?_, out, ?_, ?_⟩
    · have ha : accesses (stRun o q) = 1 + accesses q := by cases o <;> rfl
      have hl := write_length v (S k) o
      have hh := hH k
      unfold work at hu ⊢
      rw [ha]
      nlinarith
    · rw [step_run]
      exact ho
    · rw [trNormal_run]
      change (tick M)^[used + (((stWrite v (S k) o).length + 1) + ((S k).length + 1))]
        ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ = out
      rw [Function.iterate_add_apply, hr, he]
  | load f q ih => exact ih H (f v) S L hL hH
  | branch f a b ia ib =>
    cases hf : f v with
    | false =>
      obtain ⟨used, hu, out, ho, he⟩ := ib H v S L hL hH
      refine ⟨used, le_trans hu (work_mono H (Nat.le_max_right _ _)), out, ?_, ?_⟩
      · simpa only [TM2.stepAux, hf, cond] using ho
      · simpa only [trNormal, TM1.stepAux, hf, cond] using he
    | true =>
      obtain ⟨used, hu, out, ho, he⟩ := ia H v S L hL hH
      refine ⟨used, le_trans hu (work_mono H (Nat.le_max_left _ _)), out, ?_, ?_⟩
      · simpa only [TM2.stepAux, hf, cond] using ho
      · simpa only [trNormal, TM1.stepAux, hf, cond] using he
  | goto label => exact ⟨0, Nat.zero_le _, _, ⟨L, hL⟩, rfl⟩
  | halt => exact ⟨0, Nat.zero_le _, _, ⟨L, hL⟩, rfl⟩

/-- One source TM2 transition, including the initial translated entry tick.
The full existing `TrCfg` relation is preserved by a bounded actual tape run. -/
theorem source_step (M : Λ → TM2.Stmt Γ Λ V)
    (label : Λ) (v : V) (S : ∀ k, List (Γ k)) (H : Nat)
    (hH : ∀ k, (S k).length ≤ H)
    (cfg : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V))
    (hcfg : TrCfg (⟨some label, v, S⟩ : TM2.Cfg Γ Λ V) cfg) :
    ∃ used ≤ 1 + work H (M label), ∃ out,
      TrCfg (TM2.stepAux (M label) v S) out ∧ (tick M)^[used] cfg = out := by
  cases hcfg with
  | mk L hL =>
    obtain ⟨used, hu, out, ho, he⟩ := statement M (M label) H v S L hL hH
    refine ⟨used + 1, by omega, out, ho, ?_⟩
    rw [Function.iterate_succ_apply]
    exact he

/-- Intermediate stack heights are derived from the executed statement; each
stack access can add at most one cell and branches use their maximum count. -/
theorem statement_height (q : TM2.Stmt Γ Λ V) (H : Nat) (v : V)
    (S : ∀ k, List (Γ k)) (hH : ∀ k, (S k).length ≤ H) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ H + accesses q := by
  induction q using stmtStRec generalizing H v S with
  | run k o q ih =>
    have h := ih (H + 1) (stVar v (S k) o)
      (Function.update S k (stWrite v (S k) o)) (write_height v S o H hH)
    intro j
    rw [step_run]
    have hj := h j
    have ha : accesses (stRun o q) = 1 + accesses q := by cases o <;> rfl
    rw [ha]
    omega
  | load f q ih => exact ih H (f v) S hH
  | branch f a b ia ib =>
    intro j
    cases hf : f v with
    | false =>
      have h := (ib H v S hH j).trans (Nat.add_le_add_left (Nat.le_max_right (accesses a) (accesses b)) H)
      simpa only [TM2.stepAux, hf, cond, accesses] using h
    | true =>
      have h := (ia H v S hH j).trans (Nat.add_le_add_left (Nat.le_max_left (accesses a) (accesses b)) H)
      simpa only [TM2.stepAux, hf, cond, accesses] using h
  | goto => exact hH
  | halt => exact hH

end ExplainableCrypto.Helios.Computational.TM2TapeCost
