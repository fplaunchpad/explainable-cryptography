import ExplainableCrypto.Helios.Computational.TM2TapeCost
import Mathlib.Data.Finset.Lattice.Fold

/-! Compose Mathlib's existing translated statements across finite source runs.
Stack growth is derived, including early halt and repeated pushes. -/
namespace ExplainableCrypto.Helios.Computational.TM2TapeRuns
open Turing TM2to1 TM2TapeCost
variable {K : Type*} {Γ : K → Type*} {Λ V : Type*} [DecidableEq K]

private theorem run_cap (M : Λ → TM2.Stmt Γ Λ V) (A : Nat)
    (hA : ∀ label, accesses (M label) ≤ A) (fuel H cap : Nat)
    (src : TM2.Cfg Γ Λ V) (cfg : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V))
    (hcfg : TrCfg src cfg) (hH : ∀ k, (src.stk k).length ≤ H)
    (hcap : H + fuel * A ≤ cap) :
    ∃ used ≤ fuel * (1 + A * (2 * cap + 2)), ∃ out,
      TrCfg ((TM2ReturnLink.tick M)^[fuel] src) out ∧
      (tick M)^[used] cfg = out ∧
      ∀ k, (((TM2ReturnLink.tick M)^[fuel] src).stk k).length ≤ H + fuel * A := by
  induction fuel generalizing H src cfg with
  | zero => exact ⟨0, Nat.zero_le _, cfg, hcfg, rfl, by simpa using hH⟩
  | succ fuel ih =>
    cases src with
    | mk label v tapes =>
      cases label with
      | none =>
        have fixed : TM2ReturnLink.tick M (⟨none, v, tapes⟩ : TM2.Cfg Γ Λ V) =
            ⟨none, v, tapes⟩ := rfl
        rw [Function.iterate_fixed fixed]
        exact ⟨0, Nat.zero_le _, cfg, hcfg, rfl, fun k => (hH k).trans (Nat.le_add_right _ _)⟩
      | some label =>
        have cap_next : H + A + fuel * A ≤ cap := by
          rw [Nat.succ_mul] at hcap
          omega
        have next_height : ∀ k, ((TM2.stepAux (M label) v tapes).stk k).length ≤ H + A :=
          fun k => (statement_height (M label) H v tapes hH k).trans
            (Nat.add_le_add_left (hA label) H)
        obtain ⟨before, hb, mid, hm, he⟩ := source_step M label v tapes H hH cfg hcfg
        have hb_cap : before ≤ 1 + A * (2 * cap + 2) := by
          have hp := Nat.mul_le_mul (hA label)
            (by have := hA label; omega : 2 * (H + accesses (M label)) + 2 ≤ 2 * cap + 2)
          unfold work at hb
          omega
        obtain ⟨after, ha, out, ho, ht, hh⟩ :=
          ih (H + A) (TM2.stepAux (M label) v tapes) mid hm next_height cap_next
        refine ⟨after + before, ?_, out, ?_, ?_, ?_⟩
        · rw [Nat.succ_mul]
          omega
        · simpa only [Function.iterate_succ_apply, TM2ReturnLink.tick, TM2.step,
            Option.getD_some] using ho
        · rw [Function.iterate_add_apply, he, ht]
        · intro k
          have hk := hh k
          simpa only [Function.iterate_succ_apply, TM2ReturnLink.tick, TM2.step,
            Option.getD_some, Nat.succ_mul, Nat.add_assoc, Nat.add_comm A] using hk

/-- A finite deterministic execution has a derived global height and tape-time
bound. The initial translation relation is preserved across all successors. -/
theorem run (M : Λ → TM2.Stmt Γ Λ V) (A : Nat)
    (hA : ∀ label, accesses (M label) ≤ A) (fuel H : Nat)
    (src : TM2.Cfg Γ Λ V) (cfg : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V))
    (hcfg : TrCfg src cfg) (hH : ∀ k, (src.stk k).length ≤ H) :
    ∃ used ≤ fuel * (1 + A * (2 * (H + fuel * A) + 2)), ∃ out,
      TrCfg ((TM2ReturnLink.tick M)^[fuel] src) out ∧
      (tick M)^[used] cfg = out ∧
      ∀ k, (((TM2ReturnLink.tick M)^[fuel] src).stk k).length ≤ H + fuel * A :=
  run_cap M A hA fuel H (H + fuel * A) src cfg hcfg hH le_rfl

/-- Maximum occupied column height of the actual source stacks. -/
def height [Fintype K] (S : ∀ k, List (Γ k)) : Nat :=
  Finset.univ.sup (fun k => (S k).length)

omit [DecidableEq K] in
theorem length_le_height [Fintype K] (S : ∀ k, List (Γ k)) (k : K) :
    (S k).length ≤ height S := Finset.le_sup (f := fun k => (S k).length) (Finset.mem_univ k)

/-- Canonical bottom-to-top columns; absent cells are blank. This is a data
representation, not an executable input loader. -/
def columns [Fintype K] (S : ∀ k, List (Γ k)) : ListBlank (∀ k, Option (Γ k)) :=
  ListBlank.mk ((List.range (height S)).map (fun n k => (S k).reverse[n]?))

omit [DecidableEq K] in
theorem columns_nth [Fintype K] (S : ∀ k, List (Γ k)) (n : Nat) (k : K) :
    (columns S).nth n k = (S k).reverse[n]? := by
  by_cases hn : n < height S
  · simp [columns, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hn]
  · have hs : (S k).reverse[n]? = none :=
      List.getElem?_eq_none (by have := length_le_height S k; simpa using le_trans this (Nat.le_of_not_gt hn))
    simp [columns, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hn :
        (List.range (height S)).length ≤ n), hs]
    rfl

omit [DecidableEq K] in
theorem columns_presentation [Fintype K] (S : ∀ k, List (Γ k)) (k : K) :
    (columns S).map (proj k) = ListBlank.mk ((S k).map some).reverse := by
  apply ListBlank.ext
  intro n
  rw [proj_map_nth, columns_nth, ← List.map_reverse, ListBlank.nth_mk,
    List.getI_eq_getElem?_getD, List.getElem?_map]
  cases (S k).reverse[n]? <;> rfl

/-- Canonical configuration at a source-instruction boundary. -/
def pack [Fintype K] (c : TM2.Cfg Γ Λ V) : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V) :=
  ⟨c.l.map TM2to1.Λ'.normal, c.var, Tape.mk' ∅ (addBottom (columns c.stk))⟩

omit [DecidableEq K] in
theorem pack_related [Fintype K] (c : TM2.Cfg Γ Λ V) : TrCfg c (pack c) :=
  TrCfg.mk (columns c.stk) (columns_presentation c.stk)

omit [DecidableEq K] in
theorem related_unique (c : TM2.Cfg Γ Λ V)
    (a b : Config (K := K) (Γ := Γ) (Λ := Λ) (V := V))
    (ha : TrCfg c a) (hb : TrCfg c b) : a = b := by
  cases ha with
  | mk L hL =>
    cases hb with
    | mk R hR =>
      have eq : L = R := by
        apply ListBlank.ext
        intro n
        funext k
        rw [← proj_map_nth, ← proj_map_nth, hL k, hR k]
      cases eq
      rfl

/-- Maximum stack-access count of the fixed finite source code. -/
def codeAccesses [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ V) : Nat :=
  Finset.univ.sup (fun label => accesses (M label))

/-- Exact finite tape execution from canonical source data. Initial presentation,
stack heights and the code bound are derived, not supplied as certificates. -/
theorem run_packed [Fintype K] [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ V)
    (fuel : Nat) (src : TM2.Cfg Γ Λ V) :
    ∃ used ≤ fuel * (1 + codeAccesses M *
        (2 * (height src.stk + fuel * codeAccesses M) + 2)),
      (tick M)^[used] (pack src) = pack ((TM2ReturnLink.tick M)^[fuel] src) ∧
      ∀ k, (((TM2ReturnLink.tick M)^[fuel] src).stk k).length ≤
        height src.stk + fuel * codeAccesses M := by
  obtain ⟨used, hu, out, ho, ht, hh⟩ := run M (codeAccesses M)
    (fun label => Finset.le_sup (f := fun label => accesses (M label)) (Finset.mem_univ label)) fuel (height src.stk)
    src (pack src) (pack_related src) (length_le_height src.stk)
  exact ⟨used, hu, ht.trans (related_unique _ _ _ ho (pack_related _)), hh⟩

end ExplainableCrypto.Helios.Computational.TM2TapeRuns
