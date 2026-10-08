import ExplainableCrypto.Helios.Computational.BallotReplayStorage

/-! Analysis observations at original finite-handler request boundaries. Each
event retains the original request and its prestate, including hits and uniform
requests. Erasure recovers the unchanged interpreter. This is proof bookkeeping,
not a protocol observation or an executed machine-storage requirement. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
variable {F G A : Type} [DecidableEq G]

abbrev Event (F G : Type) := (BallotOracleSpec F G).Domain × BallotFiniteLoggedState F G
abbrev State (F G : Type) := BallotFiniteLoggedState F G × List (Event F G)

/-- Capture the input state once per original handler invocation, before any
lookup, insertion or log append changes it. The original handler is reused. -/
def impl : QueryImpl (BallotOracleSpec F G)
    (StateT (State F G) (OracleComp (FiatShamir.Fork.wrappedSpec F))) := fun t s => do
  let out ← (ballotFiniteLoggedImpl t).run s.1
  pure (out.1,(out.2,s.2++[(t,s.1)]))

def run (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G)
    (events : List (Event F G) := []) := (simulateQ impl oa).run (s,events)

private theorem erase_step (t : (BallotOracleSpec F G).Domain) (s : State F G) :
    Prod.map id Prod.fst <$> (impl t).run s = (ballotFiniteLoggedImpl t).run s.1 := by
  simp [impl,StateT.run]

/-- Erasing only the analysis events preserves the full original output/state
and raw query tree, for every source and initial state. -/
theorem run_eq (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G)
    (events : List (Event F G) := []) :
    Prod.map id Prod.fst <$> run oa s events = runBallotFiniteLogged oa s := by
  exact map_run_simulateQ_eq_of_query_map_eq impl ballotFiniteLoggedImpl Prod.fst
    erase_step oa (s,events)

/-- Every supported original execution has an observed execution with exactly
its original answer and final state. Instrumentation adds no reachability premise. -/
theorem supported_lift (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G)
    (out : A × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged oa s)) :
    ∃ events, (out.1,(out.2,events)) ∈ support (run oa s) := by
  rw [← run_eq oa s] at ho
  obtain ⟨observed,hobs,he⟩ := mem_support_map_peel _ _ ho
  cases observed with
  | mk a state =>
    cases state with
    | mk last events =>
      change out = (a,last) at he
      subst out
      exact ⟨events,hobs⟩

/-- Coverage at each actual original source request: run its original handler,
record this request's prestate, then continue with the actual answer/state.
This equation includes hash hits, which need no lower-level random query. -/
theorem query_run (t : (BallotOracleSpec F G).Domain)
    (next : (BallotOracleSpec F G).Range t → BallotOracleComp F G A)
    (s : BallotFiniteLoggedState F G) (events : List (Event F G)) :
    run (liftM ((BallotOracleSpec F G).query t) >>= next) s events = (do
      let out ← (ballotFiniteLoggedImpl t).run s
      run (next out.1) out.2 (events++[(t,s)])) := by
  have hi : (impl t).run (s,events) = (do
      let out ← (ballotFiniteLoggedImpl t).run s
      pure (out.1,(out.2,events++[(t,s)]))) := rfl
  simp only [run,run_simulateQ_query_bind,hi,bind_assoc,pure_bind]

private theorem step_growth (t : (BallotOracleSpec F G).Domain)
    (s : BallotFiniteLoggedState F G)
    (out : (BallotOracleSpec F G).Range t × BallotFiniteLoggedState F G)
    (ho : out ∈ support ((ballotFiniteLoggedImpl t).run s)) :
    out.2.1.entries.length ≤ s.1.entries.length+(if isBallotHashQuery (F := F) t then 1 else 0) ∧
    out.2.2.length ≤ s.2.length+(if isBallotHashQuery (F := F) t then 1 else 0) := by
  cases t with
  | inl n =>
    simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,mem_support_bind_iff,mem_support_pure_iff] at ho
    obtain ⟨a,_,rfl⟩ := ho
    simp [isBallotHashQuery]
  | inr key =>
    cases h : s.1.lookup key with
    | some a =>
      simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h,mem_support_pure_iff] at ho
      subst out
      simp [isBallotHashQuery]
    | none =>
      simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h,mem_support_bind_iff,mem_support_pure_iff] at ho
      obtain ⟨a,_,rfl⟩ := ho
      have hn : key ∉ s.1 := by
        intro hk
        have hx := AList.lookup_isSome.mpr hk
        simp [h] at hx
      change (s.1.insert key a).entries.length ≤ s.1.entries.length+1 ∧
        (s.2++[((),key)]).length ≤ s.2.length+1
      rw [AList.entries_insert_of_notMem hn]
      simp

private def bounded (C L : Nat) (s : BallotFiniteLoggedState F G) : Prop :=
  s.1.entries.length ≤ C ∧ s.2.length ≤ L

private theorem run_bound (oa : BallotOracleComp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (s : BallotFiniteLoggedState F G) (events : List (Event F G)) (C L : Nat)
    (hs : s.1.entries.length+n ≤ C ∧ s.2.length+n ≤ L)
    (he : ∀ e ∈ events, bounded C L e.2)
    (out : A × State F G) (ho : out ∈ support (run oa s events)) :
    bounded C L out.2.1 ∧ ∀ e ∈ out.2.2, bounded C L e.2 := by
  induction oa using OracleComp.inductionOn generalizing n s events with
  | pure a =>
    have hp : run (pure a) s events = pure (a,(s,events)) := rfl
    rw [hp] at ho
    have h := eq_of_mem_support_pure _ ho
    subst out
    change bounded C L s ∧ (∀ e ∈ events, bounded C L e.2)
    exact ⟨⟨by omega,by omega⟩,he⟩
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [query_run,mem_support_bind_iff] at ho
    obtain ⟨first,hfirst,hlast⟩ := ho
    have hg := step_growth t s first hfirst
    have current : bounded C L s := ⟨by omega,by omega⟩
    have he' : ∀ e ∈ events++[(t,s)], bounded C L e.2 := by
      intro e hm
      simp only [List.mem_append,List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact he e hm
      · exact current
    apply ih first.1 (if isBallotHashQuery (F := F) t then n-1 else n)
      (hb.2 first.1) first.2 (events++[(t,s)]) ?_ he' hlast
    by_cases h : isBallotHashQuery (F := F) t
    · simp only [h,ite_true] at hg ⊢
      have hn : 0 < n := hb.1.resolve_left (not_not.mpr h)
      constructor <;> omega
    · simp only [h,ite_false] at hg ⊢
      constructor <;> omega

/-- Every recorded original-request prestate has a storage bound derived from
the actual source budget and initial offsets. The observation equations include
hits and uniforms; no caller-supplied intermediate invariant is needed. -/
theorem prestates_bound (oa : BallotOracleComp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (s : BallotFiniteLoggedState F G) (out : A × State F G)
    (ho : out ∈ support (run oa s)) :
    ∀ e ∈ out.2.2,
      e.2.1.entries.length ≤ s.1.entries.length+n ∧ e.2.2.length ≤ s.2.length+n := by
  exact (run_bound oa n hb s [] _ _ ⟨le_rfl,le_rfl⟩ (by simp) out ho).2

/-- Every previously recorded request survives every supported continuation,
in its original order and with its original prestate. -/
theorem events_retained (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G)
    (events : List (Event F G)) (out : A × State F G)
    (ho : out ∈ support (run oa s events)) : events.IsPrefix out.2.2 := by
  induction oa using OracleComp.inductionOn generalizing s events with
  | pure a =>
    have hp : run (pure a) s events = pure (a,(s,events)) := rfl
    rw [hp] at ho
    have h := eq_of_mem_support_pure _ ho
    subst out
    exact List.prefix_refl _
  | query_bind t next ih =>
    rw [query_run,mem_support_bind_iff] at ho
    obtain ⟨first,_,hlast⟩ := ho
    exact (List.prefix_append events [(t,s)]).trans
      (ih first.1 first.2 (events++[(t,s)]) hlast)

/-- Any supported completion of this original request contains its actual
prestate event. The subsequent computation cannot erase the event. -/
theorem request_captured (t : (BallotOracleSpec F G).Domain)
    (next : (BallotOracleSpec F G).Range t → BallotOracleComp F G A)
    (s : BallotFiniteLoggedState F G) (events : List (Event F G))
    (out : A × State F G)
    (ho : out ∈ support (run (liftM ((BallotOracleSpec F G).query t) >>= next) s events)) :
    (t,s) ∈ out.2.2 := by
  rw [query_run,mem_support_bind_iff] at ho
  obtain ⟨first,_,hlast⟩ := ho
  exact (events_retained (next first.1) first.2 (events++[(t,s)]) out hlast).sublist.subset (by simp)

#print axioms supported_lift
#print axioms run_eq
#print axioms query_run
#print axioms prestates_bound
#print axioms events_retained
#print axioms request_captured

end ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
