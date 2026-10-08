import ExplainableCrypto.Helios.Computational.BallotFork

/-! Relate selected replay targets to the actual full-proof verifier, including
its final hash query. Prior programmed honest points are a separate obligation. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

local instance (p : Proof01 F G) (c : F) (stmt : BallotStatement G) :
    Decidable (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

private def cacheLogged (st : FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) : Prop :=
  ∀ key c, st.1 key = some c → key ∈ st.2

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
private theorem logged_run_cacheLogged {α : Type} (oa : BallotOracleComp F G α)
    (st : FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) (hc : cacheLogged st)
    (out : α × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (ho : out ∈ support ((simulateQ ballotForkLoggedImpl oa).run st)) : cacheLogged out.2 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
    subst out; exact hc
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind,
      Set.mem_iUnion] at ho
    obtain ⟨ans,ha,ho⟩ := ho
    apply ih ans.1 ans.2 _ ho
    rcases st with ⟨cache,log⟩
    cases t with
    | inl n =>
      change ans ∈ support ((FiatShamir.Fork.unifForward Unit (BallotForkPoint G) F n).run
        (cache,log)) at ha
      rw [FiatShamir.Fork.unifForward_run] at ha
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ha
      obtain ⟨u,_,rfl⟩ := ha
      exact hc
    | inr key =>
      change ans ∈ support ((FiatShamir.Fork.roImpl Unit (BallotForkPoint G) F ((),key)).run
        (cache,log)) at ha
      cases hkey : cache ((),key) with
      | some c =>
        rw [FiatShamir.Fork.roImpl_run_some Unit _ _ _ _ hkey] at ha
        simp only [support_pure, Set.mem_singleton_iff] at ha
        subst ans; exact hc
      | none =>
        rw [FiatShamir.Fork.roImpl_run_none Unit _ _ _ hkey] at ha
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ha
        obtain ⟨c,_,rfl⟩ := ha
        intro other d hd
        by_cases he : other = ((),key)
        · subst other; simp
        · simp only [QueryCache.cacheQuery_of_ne _ _ he] at hd
          exact List.mem_append_left _ (hc other d hd)

/-- For a bounded program, verification in the live trace implies the selector
covers the target. The cache/log invariant is derived from the empty runtime. -/
theorem ballotFork_selector_of_bound [Fintype F]
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) (n+1))
    (x : BallotForkTrace F G) (hx : x ∈ support (ballotForkRunTrace oa)) :
    (ballotForkSelector n x).isSome = x.verified := by
  rw [ballotForkRunTrace_eq] at hx
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
  obtain ⟨out,ho,rfl⟩ := hx
  have hl := ballotFork_log_bound oa (n+1) hb (∅,[]) out ho
  have hc := logged_run_cacheLogged oa (∅,[]) (by simp [cacheLogged]) out ho
  simp only [List.length_nil, Nat.zero_add] at hl
  cases hkey : out.2.1 ((),out.1.1,out.1.2.commitment) with
  | none => simp [ballotForkSelector, FiatShamir.Fork.forkPoint]
  | some c =>
    have hm := hc _ c hkey
    have hi : out.2.2.findIdx (· == ((),out.1.1,out.1.2.commitment)) < n+1 :=
      (List.findIdx_lt_length_of_exists (by exact ⟨_,hm,by simp⟩)).trans_le hl
    simp only [ballotForkSelector, FiatShamir.Fork.forkPoint, FiatShamir.Fork.Trace.target,
      hm, ite_true]
    simp only [Bool.beq_eq_decide_eq] at hi ⊢
    simp only [hi, dite_true]
    split_ifs <;> simp_all

/-- Append the verifier's actual hash query, retaining the original full proof. -/
def ballotForkComplete (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    BallotOracleComp F G (BallotStatement G × Proof01 F G) := do
  let out ← oa
  let _ ← ballotChallengeOracle out.1 out.2.commitment
  pure out

def ballotVerificationGame (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    BallotOracleComp F G Bool := do
  let out ← oa
  strongBallotVerifyOracle out.1 out.2

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [SampleableType F] in
theorem ballotForkComplete_query_bound
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    (ballotForkComplete oa).IsQueryBoundP (isBallotHashQuery (F := F)) (n+1) := by
  apply isQueryBoundP_bind hb
  intro out _
  simp [ballotChallengeOracle, isBallotHashQuery]

/-- The trace verification flag performs exactly the original verifier, even
when that verifier must sample a previously unqueried challenge. -/
theorem ballotFork_complete_verified
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    (fun x => x.verified) <$> ballotForkRunTrace (ballotForkComplete oa) =
      Prod.fst <$> ((simulateQ ballotForkLoggedImpl (ballotVerificationGame oa)).run (∅,[])) := by
  rw [ballotForkRunTrace_eq]
  simp only [ballotForkComplete, ballotVerificationGame, strongBallotVerifyOracle,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    bind_assoc, pure_bind]
  apply bind_congr
  intro out
  simp only [ballotChallengeOracle, simulateQ_spec_query, ballotForkLoggedImpl, QueryImpl.add]
  rcases out with ⟨⟨stmt,p⟩,cache,log⟩
  cases hc : cache ((),stmt,p.commitment) with
  | some c =>
    rw [FiatShamir.Fork.roImpl_run_some Unit _ _ _ _ hc]
    simp [hc]
  | none =>
    rw [FiatShamir.Fork.roImpl_run_none Unit _ _ _ hc]
    simp

/-- Exact acceptance runtime, after interpreting the replay entropy by the
same uniform sampler as the original lazy oracle. -/
theorem ballotFork_complete_runtime
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    simulateQ ballotForkEntropyImpl
      ((fun x => x.verified) <$> ballotForkRunTrace (ballotForkComplete oa)) =
        Prod.fst <$> runBallotOracle (ballotVerificationGame oa) ∅ := by
  rw [ballotFork_complete_verified, simulateQ_map]
  have h := congrArg (fun m => Prod.fst <$> m)
    (ballotFork_runtime_eq (ballotVerificationGame oa) (∅,[]))
  have he : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ F).QueryCache) =
      (∅ : BallotOracleCache F G) := by funext key; rfl
  rw [he] at h
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

section Probability
variable [Fintype F]
local instance : Inhabited F := ⟨0⟩
noncomputable local instance : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

omit [DecidableEq F] in
theorem ballotFork_entropy_eval {α : Type}
    (oa : OracleComp (FiatShamir.Fork.wrappedSpec F) α) :
    evalSPMF (simulateQ ballotForkEntropyImpl oa) = evalSPMF oa := by
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  rintro (n | u)
  · simp only [ballotForkEntropyImpl, QueryImpl.add, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    rw [evalSPMF_query (spec := FiatShamir.Fork.wrappedSpec F)]
    exact evalSPMF_query (spec := unifSpec) n
  · simp only [ballotForkEntropyImpl, QueryImpl.add]
    exact show (evalSPMF ($ᵗ F) : SPMF F) = _ by
      rw [evalSPMF_uniformSample, evalSPMF_query]
      rfl

/-- All actual verifier acceptance is covered, including an unqueried target.
Only the original program's structural hash-query budget is assumed. -/
theorem ballotFork_acceptance_probability_eq
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    Pr[fun x => (ballotForkSelector n x).isSome | ballotForkRunTrace (ballotForkComplete oa)] =
      Pr[fun out => out.1 | runBallotOracle (ballotVerificationGame oa) ∅] := by
  calc
    _ = Pr[fun x => x.verified | ballotForkRunTrace (ballotForkComplete oa)] :=
      probEvent_congr' (fun x hx => by
        rw [ballotFork_selector_of_bound _ n (ballotForkComplete_query_bound oa n hb) x hx]) rfl
    _ = Pr[fun b : Bool => b = true | (fun x => x.verified) <$>
        ballotForkRunTrace (ballotForkComplete oa)] := by simp only [probEvent_map, Function.comp_def]
    _ = Pr[fun b : Bool => b = true | simulateQ ballotForkEntropyImpl ((fun x => x.verified) <$>
        ballotForkRunTrace (ballotForkComplete oa))] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
    _ = _ := by simp only [ballotFork_complete_runtime, probEvent_map, Function.comp_def]

/-- Replay extraction under actual full-proof acceptance. This is a raw ballot
oracle theorem; prior simulated honest proof points and election integration
are not assumed or discharged here. -/
theorem ballotFork_acceptance_extraction_le
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    let acc := Pr[fun out => out.1 | runBallotOracle (ballotVerificationGame oa) ∅]
    acc * (acc / (n+1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun out => out.isSome | ballotForkExtract (ballotForkComplete oa) n] := by
  have h := ballotFork_extraction_probability_le (ballotForkComplete oa) n
  simpa only [ballotFork_acceptance_probability_eq oa n hb] using h
private theorem ballotFork_trace_source
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G))
    (x : BallotForkTrace F G) (log : QueryLog (FiatShamir.Fork.wrappedSpec F))
    (hx : (x,log) ∈ support (replayFirstRun (ballotForkRunTrace oa))) :
    ∃ cache, ((x.forgery.2.1.1,x.forgery.2.2),cache) ∈ support (runBallotOracle oa ∅) := by
  have hm : x ∈ support (Prod.fst <$> replayFirstRun (ballotForkRunTrace oa)) := by
    rw [support_map]
    exact ⟨(x,log),hx,rfl⟩
  simp only [replayFirstRun,withQueryLog,QueryImpl.fst_map_run_withLogging,
    simulateQ_ofLift_eq_self] at hm
  rw [ballotForkRunTrace_eq] at hm
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hm
  obtain ⟨raw,hraw,rfl⟩ := hm
  have hent := (mem_support_iff_of_evalSPMF_eq (ballotFork_entropy_eval
    ((simulateQ ballotForkLoggedImpl oa).run (∅,[]))) raw).mpr hraw
  have hproject : (raw.1,ballotForkCacheProject raw.2.1) ∈ support
      (Prod.map id (fun state => ballotForkCacheProject state.1) <$>
        simulateQ ballotForkEntropyImpl ((simulateQ ballotForkLoggedImpl oa).run (∅,[]))) := by
    rw [support_map]
    exact ⟨raw,hent,rfl⟩
  rw [ballotFork_runtime_eq] at hproject
  exact ⟨ballotForkCacheProject raw.2.1,hproject⟩

/-- A successful replay witness originates in a full valid proof actually
returned by the source oracle program in a supported original execution. -/
theorem ballotFork_extract_source
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (stmt,wit) ∈ support (ballotForkExtract oa n)) :
    ∃ (p : Proof01 F G) (cache : BallotOracleCache F G) (c : F),
      ((stmt,p),cache) ∈ support (runBallotOracle oa ∅) ∧
      p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext := by
  rw [ballotForkExtract,support_map] at ho
  obtain ⟨pair,hpair,he⟩ := ho
  cases pair with
  | none => simp at he
  | some pair =>
    have he' := congrArg Prod.fst (Option.some.inj he)
    obtain ⟨lx,ly,s,hx,hy,hrx,hry,hne⟩ := contextFork_propertyTransfer
      (main := ballotForkRunTrace oa) (qb := ballotForkBudget (F := F) n) (i := .inr ())
      (cf := ballotForkSelector n)
      (P_out := fun z log => (z,log) ∈ support (replayFirstRun (ballotForkRunTrace oa)))
      (hP := fun h => h) hpair
    obtain ⟨cache,hcache⟩ := ballotFork_trace_source oa pair.1 lx hrx
    obtain ⟨c,hc,hcommit,hvalid⟩ := ballotFork_selected_challenge oa n pair.1 lx hrx s hx
    change pair.1.forgery.2.1.1 = stmt at he'
    exact ⟨pair.1.forgery.2.2,cache,c,he' ▸ hcache,he' ▸ hvalid⟩

end Probability

#print axioms ballotFork_entropy_eval
#print axioms ballotFork_selector_of_bound
#print axioms ballotForkComplete_query_bound
#print axioms ballotFork_complete_verified
#print axioms ballotFork_complete_runtime
#print axioms ballotFork_acceptance_probability_eq
#print axioms ballotFork_acceptance_extraction_le
#print axioms ballotFork_extract_source
end ExplainableCrypto.Helios.Computational
