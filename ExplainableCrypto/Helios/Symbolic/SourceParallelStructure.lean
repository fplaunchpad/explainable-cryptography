import ExplainableCrypto.Helios.Symbolic.SourceParallelSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V W : Type}

@[simp]
theorem threads_nil : (Agent.nil : Agent V).threads = 0 := rfl

@[simp]
theorem threads_par (p q : Agent V) : (Agent.par p q).threads = p.threads + q.threads := rfl

theorem ParEq.zero_left (p : Agent V) : ParEq (.par .nil p) p :=
  (ParEq.comm _ _).trans (ParEq.zero _)

theorem ParEq.swap_middle (p q r : Agent V) : ParEq (.par p (.par q r)) (.par q (.par p r)) :=
  (ParEq.assoc _ _ _).symm.trans ((ParEq.par (ParEq.comm _ _) (.refl _)).trans (ParEq.assoc _ _ _))

/-- Source parallel structure preserves complete prefix syntax and multiplicity. -/
theorem ParEq.threads_eq {p q : Agent V} (h : ParEq p q) : p.threads = q.threads := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | zero p => simp only [threads_par,threads_nil,add_zero]
  | assoc p q r => simp only [threads_par,add_assoc]
  | comm p q => simp only [threads_par,add_comm]
  | par _ _ ih ih' => simp only [threads_par,ih,ih']

theorem parallelList_append (ps qs : List (Agent V)) :
    ParEq (parallelList (ps++qs)) (.par (parallelList ps) (parallelList qs)) := by
  induction ps with
  | nil => exact (ParEq.zero_left _).symm
  | cons p ps ih =>
    exact (ParEq.par (.refl _) ih).trans (ParEq.assoc _ _ _).symm

theorem parallelList_perm {ps qs : List (Agent V)} (h : ps.Perm qs) :
    ParEq (parallelList ps) (parallelList qs) := by
  induction h with
  | nil => exact .refl _
  | cons p _ ih => exact .par (.refl p) ih
  | swap p q ps => exact ParEq.swap_middle _ _ _
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Every process is parallel-equivalent to its active thread list. -/
theorem parEq_parallelList (p : Agent V) : ParEq p (parallelList p.threadList) := by
  induction p with
  | nil => exact .refl _
  | par p q ih ih' => exact (ParEq.par ih ih').trans (parallelList_append _ _).symm
  | output c m p _ => exact (ParEq.zero _).symm
  | input c p _ => exact (ParEq.zero _).symm
  | branch f p q _ _ => exact (ParEq.zero _).symm

/-- Complete characterization of this source structural fragment, rather than
just a one-way invariant. No prefix is unfolded by multiset equality. -/
theorem parEq_iff_threads (p q : Agent V) : ParEq p q ↔ p.threads = q.threads := by
  refine ⟨ParEq.threads_eq,?_⟩
  intro h
  have hp : p.threadList.Perm q.threadList := Multiset.coe_eq_coe.mp h
  exact (parEq_parallelList p).trans ((parallelList_perm hp).trans (parEq_parallelList q).symm)

/-- Capture-avoiding substitution preserves the parallel structural laws. -/
theorem ParEq.subst {p q : Agent V} (h : ParEq p q) (σ : V → Term W) :
    ParEq (p.subst σ) (q.subst σ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | zero p => exact .zero _
  | assoc p q r => exact .assoc _ _ _
  | comm p q => exact .comm _ _
  | par _ _ ih ih' => exact .par ih ih'
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
