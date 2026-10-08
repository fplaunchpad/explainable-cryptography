import ExplainableCrypto.Helios.Computational.ElectionOracle

/-! Finite cache covers derived from supported adaptive oracle executions.
All three election hash domains consume the budget; uniform coins do not. -/
namespace ExplainableCrypto.Helios.Computational.ElectionCacheBudget

open OracleComp OracleSpec ElectionOracle
variable {F G : Type} [DecidableEq G] [SampleableType F]

def Covered (cache : Cache F G) (n : Nat) : Prop :=
  ∃ queries : Finset (Key G),
    queries.card ≤ n ∧ ∀ key, (cache key).isSome = true → key ∈ queries

def isHash : (Spec F G).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (isHash (F := F) (G := G)) := fun key =>
  match key with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

omit [DecidableEq G] [SampleableType F] in
theorem Covered.mono {cache : Cache F G} {n m : Nat}
    (h : Covered cache n) (hn : n ≤ m) : Covered cache m := by
  obtain ⟨Q,hQ,hcov⟩ := h
  exact ⟨Q,hQ.trans hn,hcov⟩

omit [DecidableEq G] [SampleableType F] in
theorem Covered.empty : Covered (∅ : Cache F G) 0 := by
  exact ⟨∅,by simp,by simp⟩

omit [SampleableType F] in
theorem Covered.cacheQuery {cache : Cache F G} {n : Nat}
    (h : Covered cache n) (key : Key G) (c : F) :
    Covered (cache.cacheQuery key c) (n+1) := by
  obtain ⟨Q,hQ,hcov⟩ := h
  refine ⟨insert key Q, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hQ 1), ?_⟩
  intro key' hk
  by_cases he : key' = key
  · exact he ▸ Finset.mem_insert_self _ _
  · rw [QueryCache.cacheQuery_of_ne cache c he] at hk
    exact Finset.mem_insert_of_mem (hcov key' hk)

/-- The cover is derived for each reachable cache, including adaptive queries
whose next input depends on all previous answers. -/
theorem run_covered {α : Type} (oa : Comp F G α)
    (n k : Nat) (hb : oa.IsQueryBoundP (isHash (F := F)) n)
    (cache : Cache F G) (hc : Covered cache k)
    (out : α × Cache F G) (ho : out ∈ support (run oa cache)) :
    Covered out.2 (k+n) := by
  induction oa using OracleComp.inductionOn generalizing n k cache with
  | pure x =>
    simp only [run, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at ho
    subst out
    exact hc.mono (Nat.le_add_right _ _)
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      support_bind, Set.mem_iUnion] at ho
    obtain ⟨answer,ha,ho⟩ := ho
    cases t with
    | inl u =>
      simp only [randomImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at ha
      obtain ⟨v,_,rfl⟩ := ha
      exact ih v n k (by simpa [isHash] using hb.2 v) cache hc ho
    | inr key =>
      have hpos : 0 < n := by simpa [isHash] using hb.1
      have hrest := hb.2
      simp only [randomImpl, QueryImpl.add_apply_inr, randomOracle.run_eq] at ha
      cases hkey : cache key with
      | some c =>
        simp only [hkey, support_pure, Set.mem_singleton_iff] at ha
        subst answer
        exact (ih c (n-1) k (by simpa [isHash] using hrest c) cache hc ho).mono
          (by omega)
      | none =>
        simp only [hkey, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at ha
        obtain ⟨c,_,rfl⟩ := ha
        have h := ih c (n-1) (k+1) (by simpa [isHash] using hrest c)
          (cache.cacheQuery key c) (hc.cacheQuery key c) ho
        simpa [show k+1+(n-1)=k+n by omega] using h

#print axioms Covered.mono
#print axioms Covered.empty
#print axioms Covered.cacheQuery
#print axioms run_covered
end ExplainableCrypto.Helios.Computational.ElectionCacheBudget
