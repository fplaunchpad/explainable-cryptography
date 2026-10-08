import ExplainableCrypto.Helios.Computational.BallotOracleBudget
import Mathlib.Data.List.AList

/-! A finite representation of the existing semantic ballot hash cache.
Mathlib AList supplies executable lookup/insert and unique keys. The interpreter
preserves the actual output, random draws and final semantic cache. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

abbrev BallotFiniteCache (F G : Type) :=
  AList (fun _ : BallotStatement G × BallotCommitment G => F)

variable {F G : Type} [DecidableEq G]

def BallotFiniteCache.denote (cache : BallotFiniteCache F G) : BallotOracleCache F G :=
  fun key => cache.lookup key

@[simp]
theorem BallotFiniteCache.denote_empty :
    (∅ : BallotFiniteCache F G).denote = ∅ := rfl

/-- Finite insertion has exactly the existing semantic update behavior. -/
theorem BallotFiniteCache.denote_insert (cache : BallotFiniteCache F G)
    (key : BallotStatement G × BallotCommitment G) (answer : F) :
    BallotFiniteCache.denote (cache.insert key answer) = cache.denote.cacheQuery key answer := by
  funext other
  by_cases h : other = key
  · subst other; simp [denote]
  · simp [denote,h]

variable [SampleableType F]

def ballotFiniteCacheImpl : QueryImpl (BallotOracleSpec F G)
    (StateT (BallotFiniteCache F G) ProbComp) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (fun n cache => do
      let u ← liftM (unifSpec.query n)
      pure (u,cache))
    (fun key cache => match cache.lookup key with
      | some answer => pure (answer,cache)
      | none => do
        let answer ← uniformSample F
        pure (answer,cache.insert key answer))

def runBallotFiniteCache {α : Type} (oa : BallotOracleComp F G α)
    (cache : BallotFiniteCache F G) :=
  (simulateQ ballotFiniteCacheImpl oa).run cache

private theorem finite_step_eq (t : (BallotOracleSpec F G).Domain)
    (cache : BallotFiniteCache F G) :
    (fun out => (out.1,out.2.denote)) <$> ((ballotFiniteCacheImpl t).run cache) =
      ((ballotRandomImpl t).run cache.denote) := by
  cases t with
  | inl n =>
    change (fun out => (out.1,out.2.denote)) <$>
      (do let u ← liftM (unifSpec.query n); pure (u,cache)) =
      (do let u ← liftM (unifSpec.query n); pure (u,cache.denote))
    simp only [map_bind,map_pure,bind_pure]
  | inr key =>
    change (fun out => (out.1,out.2.denote)) <$>
      (match cache.lookup key with
      | some answer => pure (answer,cache)
      | none => do
        let answer ← uniformSample F
        pure (answer,cache.insert key answer)) = _
    rw [show ((ballotRandomImpl (F := F) (G := G)) (.inr key)).run cache.denote =
      (OracleSpec.randomOracle (spec := BallotHashSpec F G) key).run cache.denote from rfl,
      randomOracle.run_eq]
    rw [show cache.denote key = cache.lookup key from rfl]
    cases hc : cache.lookup key <;>
      simp [BallotFiniteCache.denote_insert,Functor.map_map]

/-- Exact program correspondence, including the final cache and all explicit
oracle draws. No reachable-state or cache-membership premise is supplied. -/
theorem runBallotFiniteCache_eq {α : Type} (oa : BallotOracleComp F G α)
    (cache : BallotFiniteCache F G) :
    (fun out => (out.1,out.2.denote)) <$> runBallotFiniteCache oa cache =
      runBallotOracle oa cache.denote := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [runBallotFiniteCache,runBallotOracle]
  | query_bind t next ih =>
    simp only [runBallotFiniteCache,runBallotOracle,simulateQ_query_bind,StateT.run_bind,
      map_bind]
    change (do let out ← ((ballotFiniteCacheImpl t).run cache)
               (fun final => (final.1,final.2.denote)) <$> runBallotFiniteCache (next out.1) out.2) =
      (do let out ← ((ballotRandomImpl t).run cache.denote)
          runBallotOracle (next out.1) out.2)
    rw [← finite_step_eq t cache,bind_map_left]
    apply bind_congr
    intro out
    exact ih out.1 out.2

omit [DecidableEq G] [SampleableType F] in
private theorem finite_keys_length (cache : BallotFiniteCache F G) :
    cache.keys.length = cache.entries.length := by simp [AList.keys,List.keys]

omit [SampleableType F] in
/-- The finite representation supplies its own initial cache cover. -/
theorem BallotFiniteCache.cache_bound (cache : BallotFiniteCache F G) :
    BallotCacheBound cache.denote cache.entries.length := by
  refine ⟨cache.keys.toFinset,?_,?_⟩
  · rw [List.toFinset_card_of_nodup cache.keys_nodup,finite_keys_length]
  · intro key hk
    exact List.mem_toFinset.mpr (AList.mem_keys.mp (AList.lookup_isSome.mp hk))

omit [SampleableType F] in
private theorem finite_length_of_cover (cache : BallotFiniteCache F G) (n : Nat)
    (h : BallotCacheBound cache.denote n) : cache.entries.length ≤ n := by
  obtain ⟨keys,hk,hcov⟩ := h
  have hs : cache.keys.toFinset ⊆ keys := by
    intro key hkey
    exact hcov key (AList.lookup_isSome.mpr (AList.mem_keys.mpr (List.mem_toFinset.mp hkey)))
  have hc := (Finset.card_le_card hs).trans hk
  rwa [List.toFinset_card_of_nodup cache.keys_nodup,finite_keys_length] at hc

/-- Cache storage grows by at most the source hash-query budget, with the
initial cover and semantic correspondence derived from this finite execution. -/
theorem runBallotFiniteCache_length_le {α : Type} (oa : BallotOracleComp F G α)
    (n : Nat) (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (cache : BallotFiniteCache F G) (out : α × BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteCache oa cache)) :
    out.2.entries.length ≤ cache.entries.length+n := by
  have hs : (out.1,out.2.denote) ∈ support (runBallotOracle oa cache.denote) := by
    rw [← runBallotFiniteCache_eq,support_map]
    exact ⟨out,ho,rfl⟩
  exact finite_length_of_cover _ _ (runBallotOracle_cache_bound oa n cache.entries.length hb
    cache.denote cache.cache_bound (out.1,out.2.denote) hs)

#print axioms BallotFiniteCache.denote_empty
#print axioms BallotFiniteCache.denote_insert
#print axioms runBallotFiniteCache_eq
#print axioms BallotFiniteCache.cache_bound
#print axioms runBallotFiniteCache_length_le
end ExplainableCrypto.Helios.Computational
