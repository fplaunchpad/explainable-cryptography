import ExplainableCrypto.Helios.Computational.ElectionCache
import ExplainableCrypto.Helios.Computational.BallotForkSource
import ExplainableCrypto.Helios.Computational.BallotJointReplay

/-! Reuse the existing ballot replay source for the full election oracle.
Other proof domains are lazy auxiliary randomness, while every ballot request
remains an explicit replay challenge. No prior execution is replaced by a cache. -/
namespace ExplainableCrypto.Helios.Computational.ElectionReplaySource
open OracleComp OracleSpec ElectionOracle ElectionCache
variable {F G : Type} [DecidableEq G] [SampleableType F]

def auxiliary (key : Key G) (cache : Cache F G) : BallotOracleComp F G (F × Cache F G) :=
  match cache key with
  | some c => pure (c,cache)
  | none => do
    let c ← liftComp (uniformSample F) (BallotOracleSpec F G)
    pure (c,cache.cacheQuery key c)

def impl : QueryImpl (Spec F G) (StateT (Cache F G) (BallotOracleComp F G)) :=
  fun t cache => match t with
    | .inl n => do
      let c ← liftComp (liftM (unifSpec.query n) : ProbComp _) (BallotOracleSpec F G)
      pure (c,cache)
    | .inr (.ballot s c) => do
      let a ← ballotChallengeOracle s c
      pure (a,cache)
    | .inr (.key g pk c) => auxiliary (.key g pk c) cache
    | .inr (.decryption g pk ct share c) => auxiliary (.decryption g pk ct share c) cache

def lower {A : Type} (oa : Comp F G A) : StateT (Cache F G) (BallotOracleComp F G) A :=
  simulateQ impl oa

def restore {A : Type} (out : (A × Cache F G) × BallotOracleCache F G) : A × Cache F G :=
  (out.1.1,replace out.1.2 out.2)

omit [SampleableType F] in
private theorem replace_aux_update (aux : Cache F G) (ballot : BallotOracleCache F G)
    (key : Key G) (hkey : ∀ s c, key ≠ .ballot s c) (a : F) :
    replace (aux.cacheQuery key a) ballot = (replace aux ballot).cacheQuery key a := by
  funext k
  by_cases h : k = key
  · subst k
    cases key with
    | ballot s c => exact False.elim (hkey s c rfl)
    | key g pk c => simp [replace]
    | decryption g pk ct share c => simp [replace]
  · cases k <;> simp [replace,QueryCache.cacheQuery_of_ne _ _ h]

private theorem ballot_pure {A : Type} (a : A) (cache : BallotOracleCache F G) :
    runBallotOracle (pure a) cache = pure (a,cache) := by simp [runBallotOracle]

private theorem auxiliary_run (aux : Cache F G) (ballot : BallotOracleCache F G)
    (key : Key G) (hkey : ∀ s c, key ≠ .ballot s c)
    (hlookup : replace aux ballot key = aux key) :
    restore <$> runBallotOracle (auxiliary key aux) ballot = run (ask key) (replace aux ballot) := by
  rw [run_ask,hlookup]
  cases h : aux key with
  | some c => simp [auxiliary,h,ballot_pure,restore]
  | none =>
    simp only [auxiliary,h,runBallotOracle_lift_bind,ballot_pure,map_bind,map_pure,restore,
      replace_aux_update aux ballot key hkey]

private theorem query_run (t : (Spec F G).Domain) (aux : Cache F G)
    (ballot : BallotOracleCache F G) :
    restore <$> runBallotOracle ((impl t).run aux) ballot =
      run (liftM ((Spec F G).query t)) (replace aux ballot) := by
  cases t with
  | inl n =>
    change restore <$> runBallotOracle
      (do let a ← liftComp (liftM (unifSpec.query n) : ProbComp _) (BallotOracleSpec F G)
          pure (a,aux)) ballot = _
    rw [runBallotOracle_lift_bind]
    simp [ballot_pure,restore,run,randomImpl,StateT.run_monadLift]
  | inr key =>
    cases key with
    | ballot s c =>
      change restore <$> runBallotOracle
        (do let a ← ballotChallengeOracle s c; pure (a,aux)) ballot =
          run (ask (.ballot s c)) (replace aux ballot)
      rw [runBallotOracle_bind,runBallotOracle_query,run_ask]
      cases h : ballot (s,c) <;>
        simp [replace,h,ballot_pure,restore,replace_update]
    | key g pk c =>
      exact auxiliary_run aux ballot (.key g pk c) (by intros; simp) rfl
    | decryption g pk ct share c =>
      exact auxiliary_run aux ballot (.decryption g pk ct share c) (by intros; simp) rfl

/-- Exact full execution and final cache, for arbitrary split initial state.
The auxiliary domain condition is discharged inside the actual query cases. -/
theorem lower_run {A : Type} (oa : Comp F G A) (aux : Cache F G)
    (ballot : BallotOracleCache F G) :
    restore <$> runBallotOracle ((lower oa).run aux) ballot = run oa (replace aux ballot) := by
  induction oa using OracleComp.inductionOn generalizing aux ballot with
  | pure a => simp [lower,ballot_pure,restore,run_pure]
  | query_bind t next ih =>
    simp only [lower,simulateQ_bind,StateT.run_bind,simulateQ_spec_query,
      runBallotOracle_bind,map_bind,run_bind]
    rw [← query_run t aux ballot,bind_map_left]
    apply bind_congr
    intro out
    exact ih out.1.1 out.1.2 out.2

/-- Lower the entire source, including preparation, from the original empty
oracle. The auxiliary cache remains internal to its execution. -/
def source {A : Type} (oa : Comp F G A) : BallotOracleComp F G A :=
  Prod.fst <$> (lower oa).run (fun _ => none)

theorem source_runtime {A : Type} (oa : Comp F G A) :
    Prod.fst <$> runBallotOracle (source oa) ∅ = Prod.fst <$> run oa (fun _ => none) := by
  have h := congrArg (fun m => Prod.fst <$> m) (lower_run oa (fun _ => none) ∅)
  simpa [source,runBallotOracle,simulateQ_map,StateT.run_map,Functor.map_map,
    Function.comp_def,restore,show replace (fun _ => none) (∅ : BallotOracleCache F G) =
      (fun _ => none) by funext k; cases k <;> rfl] using h

theorem source_mem {A : Type} (oa : Comp F G A) (a : A) (cache : BallotOracleCache F G)
    (ho : (a,cache) ∈ support (runBallotOracle (source oa) ∅)) :
    ∃ fullCache, (a,fullCache) ∈ support (run oa (fun _ => none)) := by
  have ha : a ∈ support (Prod.fst <$> runBallotOracle (source oa) ∅) := by
    rw [support_map]
    exact ⟨(a,cache),ho,rfl⟩
  rw [source_runtime,support_map] at ha
  obtain ⟨⟨a,fullCache⟩,h,rfl⟩ := ha
  exact ⟨fullCache,h⟩

private theorem lower_liftBallot {A : Type} (oa : BallotOracleComp F G A) (aux : Cache F G) :
    (lower (liftBallot oa)).run aux = (fun a => (a,aux)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing aux with
  | pure a => simp [lower,liftBallot]
  | query_bind t next ih =>
    simp only [liftBallot,simulateQ_bind,simulateQ_spec_query,lower,StateT.run_bind,
      map_bind] at *
    have hq : (simulateQ impl (ballotImpl F G t)).run aux =
        (do let a ← liftM ((BallotOracleSpec F G).query t); pure (a,aux)) := by
      cases t with
      | inl n =>
        simp only [ballotImpl,simulateQ_spec_query]
        change (do let a ← liftComp (liftM (unifSpec.query n) : ProbComp _)
                      (BallotOracleSpec F G); pure (a,aux)) = _
        rw [OracleComp.liftComp_query]
        rfl
      | inr k => rfl
    rw [hq]
    simp only [bind_assoc,pure_bind]
    exact bind_congr fun a => ih a aux

/-- Existing ballot programs and their positive/negative replay controls embed
without changing their query tree. -/
theorem source_liftBallot {A : Type} (oa : BallotOracleComp F G A) :
    source (liftBallot oa) = oa := by
  simp [source,lower_liftBallot,Functor.map_map]

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F]

def extract {A : Type} (oa : Comp F G A) (select : A → BallotStatement G × Proof01 F G)
    (n : Nat) := ballotForkSourceExtract (source oa) select n

def jointExtract {A : Type} (oa : Comp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) :=
  ballotJointReplay (source oa) select n

variable [Fintype F]

/-- Successful extraction retains an output of the complete original source,
not an execution restarted after its earlier queries. Success probability is separate. -/
theorem extract_valid {A : Type} (oa : Comp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (a : A) (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (a,stmt,wit) ∈ support (extract oa select n)) :
    stmt.Witnesses wit ∧ stmt = (select a).1 ∧
      (∃ cache, (a,cache) ∈ support (run oa (fun _ => none))) ∧
      ∃ c : F, (select a).2.Valid (fun _ => c)
        stmt.generator stmt.publicKey stmt.ciphertext := by
  obtain ⟨hw,hs,⟨cache,hcache⟩,c,hv⟩ :=
    ballotForkSourceExtract_valid (source oa) select n a stmt wit ho
  exact ⟨hw,hs,source_mem oa a cache hcache,c,hv⟩

/-- The existing shared-path construction ties all three witnesses to one
retained full-source output, with actual full-proof equations for each. -/
theorem jointExtract_valid {A : Type} (oa : Comp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (a : A) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (a,w) ∈ support (jointExtract oa select n)) :
    (∀ i, (select i a).1.Witnesses (w i) ∧ ∃ c : F,
      (select i a).2.Valid (fun _ => c) (select i a).1.generator
        (select i a).1.publicKey (select i a).1.ciphertext) ∧
      ∃ cache, (a,cache) ∈ support (run oa (fun _ => none)) := by
  obtain ⟨hw,cache,hcache⟩ := ballotJointReplay_valid (source oa) select n a w ho
  exact ⟨hw,source_mem oa a cache hcache⟩

#print axioms lower_run
#print axioms source_runtime
#print axioms source_mem
#print axioms extract_valid
#print axioms jointExtract_valid
#print axioms source_liftBallot
end ExplainableCrypto.Helios.Computational.ElectionReplaySource
