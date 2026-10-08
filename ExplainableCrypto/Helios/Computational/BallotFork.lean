import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork

/-! Replay machinery for complete ballot statement/commitment targets.
The private Unit-relation adapter only supplies VCVio's trace interface; no
security theorem about that relation or its unused interactive methods is used.
Extraction uses the actual full Proof01 verification equations. -/
namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

abbrev BallotForkPoint (G : Type) := BallotStatement G × BallotCommitment G
abbrev BallotForkSpec (F G : Type) := unifSpec + (Unit × BallotForkPoint G →ₒ F)
abbrev BallotForkTrace (F G : Type) := FiatShamir.Fork.Trace
  (M := Unit) (Commit := BallotForkPoint G) (Resp := Proof01 F G) (Chal := F)

local instance (p : Proof01 F G) (c : F) (stmt : BallotStatement G) :
    Decidable (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

private def forkVerifierAdapter : SigmaProtocol Unit Unit (BallotForkPoint G) Unit F
    (Proof01 F G) (fun _ _ => true) where
  commit _ _ := pure ((⟨0,0,(0,0)⟩,((0,0),(0,0))),())
  respond _ _ _ _ := pure (ballotTranscriptProof ((0,0),(0,0)) 0 (0,0,0))
  verify _ point c p := decide (p.commitment = point.2 ∧
    p.Valid (fun _ => c) point.1.generator point.1.publicKey point.1.ciphertext)
  sim _ := pure (⟨0,0,(0,0)⟩,((0,0),(0,0)))
  extract _ _ _ _ := pure ()

private def forkUnitRelation : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((),())
  gen_sound _ _ _ := rfl

def ballotForkQueryAdapter : QueryImpl (BallotOracleSpec F G) (OracleComp (BallotForkSpec F G)) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (fun n => liftM ((BallotForkSpec F G).query (.inl n)))
    (fun key => liftM ((BallotForkSpec F G).query (.inr ((),key))))

private def ballotForkAdversary (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    SignatureAlg.managedRoNmaAdv (FiatShamir (m := OracleComp (BallotForkSpec F G))
      (forkVerifierAdapter (F := F) (G := G)) forkUnitRelation Unit) where
  main _ := do
    let out ← simulateQ ballotForkQueryAdapter oa
    pure (((),(out.1,out.2.commitment),out.2),∅)

def ballotForkRunTrace (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (BallotForkTrace F G) :=
  FiatShamir.Fork.runTrace forkVerifierAdapter forkUnitRelation Unit (ballotForkAdversary oa) ()

def ballotForkLoggedImpl : QueryImpl (BallotOracleSpec F G)
    (StateT (FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
      (OracleComp (FiatShamir.Fork.wrappedSpec F))) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (FiatShamir.Fork.unifForward Unit (BallotForkPoint G) F)
    (fun key => FiatShamir.Fork.roImpl Unit (BallotForkPoint G) F ((),key))

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
private theorem ballotFork_compile {α : Type} (oa : BallotOracleComp F G α) :
    simulateQ (FiatShamir.Fork.unifForward Unit (BallotForkPoint G) F +
      FiatShamir.Fork.roImpl Unit (BallotForkPoint G) F) (simulateQ ballotForkQueryAdapter oa) =
      simulateQ (ballotForkLoggedImpl (F := F) (G := G)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    have h : simulateQ (FiatShamir.Fork.unifForward Unit (BallotForkPoint G) F +
        FiatShamir.Fork.roImpl Unit (BallotForkPoint G) F) (ballotForkQueryAdapter t) =
        (ballotForkLoggedImpl (F := F) (G := G)) t := by
      cases t <;> simp [ballotForkQueryAdapter, ballotForkLoggedImpl, QueryImpl.add]
    rw [h]
    exact bind_congr fun x => ih x

/-- Explicit trace semantics after erasing the unused signature interface. -/
theorem ballotForkRunTrace_eq
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) :
    ballotForkRunTrace oa = (do
      let (out,st) ← (simulateQ (ballotForkLoggedImpl (F := F) (G := G)) oa).run (∅,[])
      pure ({ forgery := ((),(out.1,out.2.commitment),out.2)
              advCache := ∅
              roCache := st.1
              queryLog := st.2
              verified := match st.1 ((),out.1,out.2.commitment) with
                | none => false
                | some c => decide (out.2.commitment = out.2.commitment ∧
                    out.2.Valid (fun _ => c) out.1.generator out.1.publicKey out.1.ciphertext)
      } : BallotForkTrace F G)) := by
  simp only [ballotForkRunTrace, FiatShamir.Fork.runTrace, ballotForkAdversary,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    ballotFork_compile, forkVerifierAdapter]
  apply bind_congr
  intro out
  cases out.2.1 ((),out.1.1,out.1.2.commitment) <;> rfl

def ballotForkEntropyImpl : QueryImpl (FiatShamir.Fork.wrappedSpec F) ProbComp :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := (Unit →ₒ F))
    (QueryImpl.ofLift unifSpec ProbComp) (fun _ => uniformSample F)

def ballotForkCacheProject (cache : (Unit × BallotForkPoint G →ₒ F).QueryCache) :
    BallotOracleCache F G := fun key => cache ((),key)

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
private theorem ballotForkCacheProject_insert
    (cache : (Unit × BallotForkPoint G →ₒ F).QueryCache) (key : BallotForkPoint G) (c : F) :
    ballotForkCacheProject (cache.cacheQuery ((),key) c) =
      (ballotForkCacheProject cache).cacheQuery key c := by
  funext other
  by_cases h : key = other
  · subst other; simp [ballotForkCacheProject]
  · simp [ballotForkCacheProject, Ne.symm h]

private def ballotForkEvaluatedImpl : QueryImpl (BallotOracleSpec F G)
    (StateT (FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) ProbComp) :=
  fun t st => simulateQ ballotForkEntropyImpl ((ballotForkLoggedImpl t).run st)

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
/-- Forgetting the miss log and the Unit key wrapper gives exactly the existing
lazy ballot-oracle runtime, for any adaptive program and any initial cache. -/
theorem ballotFork_runtime_eq {α : Type} (oa : BallotOracleComp F G α)
    (st : FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) :
    Prod.map id (fun state => ballotForkCacheProject state.1) <$>
      simulateQ ballotForkEntropyImpl ((simulateQ ballotForkLoggedImpl oa).run st) =
        runBallotOracle oa (ballotForkCacheProject st.1) := by
  rw [simulateQ_StateT_compose ballotForkLoggedImpl ballotForkEntropyImpl
    ballotForkEvaluatedImpl (fun _ _ => rfl)]
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t state
  rcases state with ⟨cache,log⟩
  cases t with
  | inl n =>
    change Prod.map id (fun state => ballotForkCacheProject state.1) <$>
      simulateQ ballotForkEntropyImpl ((FiatShamir.Fork.unifForward Unit
        (BallotForkPoint G) F n).run (cache,log)) = _
    rw [FiatShamir.Fork.unifForward_run]
    simp [ballotForkEntropyImpl, FiatShamir.Fork.wrappedUniformQuery,
      ballotRandomImpl, QueryImpl.add, QueryImpl.ofLift]
  | inr key =>
    change Prod.map id (fun state => ballotForkCacheProject state.1) <$>
      simulateQ ballotForkEntropyImpl ((FiatShamir.Fork.roImpl Unit
        (BallotForkPoint G) F ((),key)).run (cache,log)) = _
    cases hc : cache ((),key) with
    | some c =>
      rw [FiatShamir.Fork.roImpl_run_some Unit _ _ _ _ hc]
      simp [ballotRandomImpl, ballotForkCacheProject, hc]
    | none =>
      rw [FiatShamir.Fork.roImpl_run_none Unit _ _ _ hc]
      simp [ballotRandomImpl, ballotForkCacheProject, hc,
        ballotForkEntropyImpl, QueryImpl.add, FiatShamir.Fork.wrappedChallengeQuery,
        ballotForkCacheProject_insert]

omit [AddCommGroup G] [Module F G] [DecidableEq F] in
/-- Structural source query budgets also bound the actual miss log. -/
theorem ballotFork_log_bound [Fintype F] {α : Type} (oa : BallotOracleComp F G α)
    (n : Nat) (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (st : FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (out : α × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (ho : out ∈ support ((simulateQ ballotForkLoggedImpl oa).run st)) :
    out.2.2.length ≤ st.2.length + n := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec ((Unit × BallotForkPoint G →ₒ F) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  have hq : FiatShamir.nmaHashQueryBound Unit (simulateQ ballotForkQueryAdapter oa) n := by
    apply IsQueryBoundP.simulateQ_of_step hb
    · intro t ht
      cases t with
      | inl u => exact ht.elim
      | inr key => simp [ballotForkQueryAdapter, QueryImpl.add]
    · intro t ht
      cases t with
      | inl u => simp [ballotForkQueryAdapter, QueryImpl.add]
      | inr key => exact (ht trivial).elim
  apply FiatShamir.Fork.queryLog_length_le_of_nmaHashQueryBound Unit hq st
  rwa [ballotFork_compile]

def ballotForkSelector (n : Nat) : BallotForkTrace F G → Option (Fin (n+1)) :=
  FiatShamir.Fork.forkPoint Unit n

def ballotForkBudget (n : Nat) : (FiatShamir.Fork.wrappedSpec F).Domain → Nat
  | .inl _ => 0
  | .inr _ => n

/-- The selected index denotes an actual sampled hash challenge in the trace. -/
theorem ballotFork_selector_reachable
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat) :
    CfReachable (ballotForkRunTrace oa) (ballotForkBudget (F := F) n) (.inr ())
      (ballotForkSelector n) :=
  FiatShamir.Fork.runTrace_forkPoint_CfReachable forkVerifierAdapter forkUnitRelation Unit
    (ballotForkAdversary oa) n ()

/-- Shared replay context, rather than equality of numeric indices alone,
forces the entire statement and all four commitments to agree. -/
theorem ballotFork_target_eq
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (x y : BallotForkTrace F G) (s : Fin (n+1))
    (hfork : some (x,y) ∈ support (contextFork (ballotForkRunTrace oa)
      (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n)))
    (hx : ballotForkSelector n x = some s) (hy : ballotForkSelector n y = some s) :
    x.forgery.2.1 = y.forgery.2.1 := by
  let : Inhabited F := ⟨0⟩
  have h := FiatShamir.Fork.runTrace_target_eq_of_mem_contextFork forkVerifierAdapter
    forkUnitRelation Unit (ballotForkAdversary oa) n () x y s hfork hx hy
  exact congrArg Prod.snd h

/-- Decoding the actual full-proof acceptance flag of a reachable trace. -/
theorem ballotFork_verified_valid
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G))
    (x : BallotForkTrace F G) (log : QueryLog (FiatShamir.Fork.wrappedSpec F))
    (hx : (x,log) ∈ support (replayFirstRun (ballotForkRunTrace oa)))
    (hv : x.verified = true) :
    ∃ c : F, x.roCache x.target = some c ∧ x.forgery.2.2.commitment = x.forgery.2.1.2 ∧
      x.forgery.2.2.Valid (fun _ => c) x.forgery.2.1.1.generator
        x.forgery.2.1.1.publicKey x.forgery.2.1.1.ciphertext := by
  obtain ⟨c,hc,hv⟩ := FiatShamir.Fork.exists_cached_verify_of_runTrace_verified
    forkVerifierAdapter forkUnitRelation Unit (ballotForkAdversary oa) () hx hv
  exact ⟨c,hc,of_decide_eq_true hv⟩

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
theorem Proof01.eq_transcript_of_valid (p : Proof01 F G) (stmt : BallotStatement G) (c : F)
    (hv : p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext) :
    p = ballotTranscriptProof p.commitment c (p.zero.challenge,p.zero.response,p.one.response) := by
  have hs : p.one.challenge = c - p.zero.challenge := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hv.2.2
  rcases p with ⟨⟨a,b,e,z⟩,⟨a',b',e',z'⟩⟩
  simp_all [ballotTranscriptProof, Proof01.commitment]

omit [DecidableEq G] [SampleableType F] in
/-- Special soundness applied without dropping or reconstructing an unchecked
adversarial branch challenge. The reconstruction equality follows from validity. -/
theorem ballotExtract_full_valid (stmt : BallotStatement G) (p q : Proof01 F G) (c d : F)
    (hpc : p.commitment = q.commitment) (hcd : c ≠ d)
    (hp : p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext)
    (hq : q.Valid (fun _ => d) stmt.generator stmt.publicKey stmt.ciphertext) :
    stmt.Witnesses (ballotExtract c (p.zero.challenge,p.zero.response,p.one.response)
      d (q.zero.challenge,q.zero.response,q.one.response)) := by
  have hp' := hp
  have hq' := hq
  rw [p.eq_transcript_of_valid stmt c hp] at hp'
  rw [q.eq_transcript_of_valid stmt d hq, ← hpc] at hq'
  exact ballotExtract_valid stmt p.commitment c d _ _ hcd hp' hq'

/-- The challenge selected from the physical replay log is the challenge that
accepted the original full proof at its complete target. -/
theorem ballotFork_selected_challenge
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (x : BallotForkTrace F G) (log : QueryLog (FiatShamir.Fork.wrappedSpec F))
    (hx : (x,log) ∈ support (replayFirstRun (ballotForkRunTrace oa))) (s : Fin (n+1))
    (hs : ballotForkSelector n x = some s) :
    ∃ c : F, QueryLog.getQueryValue? log (.inr ()) s = some c ∧
      x.forgery.2.2.commitment = x.forgery.2.1.2 ∧
      x.forgery.2.2.Valid (fun _ => c) x.forgery.2.1.1.generator
        x.forgery.2.1.1.publicKey x.forgery.2.1.1.ciphertext := by
  have hi := FiatShamir.Fork.forkPoint_getElem?_eq_some_target Unit hs
  obtain ⟨hlt,hkey⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨c,hc,hl⟩ := FiatShamir.Fork.runTrace_cache_outer_lockstep forkVerifierAdapter
    forkUnitRelation Unit (ballotForkAdversary oa) () hx s hlt
  rw [hkey] at hc
  have hv := FiatShamir.Fork.verified_of_forkPoint_eq_some Unit hs
  obtain ⟨d,hd,hcommit,hvalid⟩ := ballotFork_verified_valid oa x log hx hv
  have he : d = c := Option.some.inj (hd.symm.trans hc)
  subst d
  exact ⟨c,hl,hcommit,hvalid⟩

def ballotForkExtractPair (x y : BallotForkTrace F G) : BallotStatement G × BallotWitness F :=
  let p := x.forgery.2.2
  let q := y.forgery.2.2
  (x.forgery.2.1.1, ballotExtract (p.zero.challenge+p.one.challenge)
    (p.zero.challenge,p.zero.response,p.one.response) (q.zero.challenge+q.one.challenge)
    (q.zero.challenge,q.zero.response,q.one.response))

variable [Fintype F]

theorem ballotFork_pair_extract_valid
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (x y : BallotForkTrace F G)
    (hfork : some (x,y) ∈ support (contextFork (ballotForkRunTrace oa)
      (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n))) :
    (ballotForkExtractPair x y).1.Witnesses (ballotForkExtractPair x y).2 := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) := IsUniformSpec.ofFintypeInhabited _
  obtain ⟨lx,ly,s,hx,hy,hrx,hry,hne⟩ := contextFork_propertyTransfer
    (main := ballotForkRunTrace oa) (qb := ballotForkBudget (F := F) n) (i := .inr ())
    (cf := ballotForkSelector n)
    (P_out := fun z log => (z,log) ∈ support (replayFirstRun (ballotForkRunTrace oa)))
    (hP := fun h => h) hfork
  obtain ⟨c,hlc,hpc,hp⟩ := ballotFork_selected_challenge oa n x lx hrx s hx
  obtain ⟨d,hld,hqc,hq⟩ := ballotFork_selected_challenge oa n y ly hry s hy
  have he := ballotFork_target_eq oa n x y s hfork hx hy
  have hstmt := congrArg Prod.fst he
  have hcommit := hpc.trans ((congrArg Prod.snd he).trans hqc.symm)
  have hcd : c ≠ d := by
    intro h
    exact hne (by rw [hlc,hld,h])
  rw [← hstmt] at hq
  have hv := ballotExtract_full_valid x.forgery.2.1.1 x.forgery.2.2 y.forgery.2.2
    c d hcommit hcd hp hq
  simpa only [ballotForkExtractPair, hp.2.2, hq.2.2] using hv

def ballotForkExtract (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat) :=
  Option.map (fun pair => ballotForkExtractPair pair.1 pair.2) <$>
    contextFork (ballotForkRunTrace oa) (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n)

theorem ballotFork_extract_valid
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (stmt,wit) ∈ support (ballotForkExtract oa n)) : stmt.Witnesses wit := by
  rw [ballotForkExtract, support_map] at ho
  obtain ⟨out,hs,he⟩ := ho
  cases out with
  | none => simp at he
  | some pair =>
    have he' : ballotForkExtractPair pair.1 pair.2 = (stmt,wit) := Option.some.inj he
    have h := ballotFork_pair_extract_valid oa n pair.1 pair.2 hs
    simpa only [he'] using h

/-- Quantitative replay extraction for selected, live queried targets. The
acceptance probability here includes the selector condition; relating it to
all accepted malicious ballots remains a separate obligation. -/
theorem ballotFork_extraction_probability_le
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat) :
    letI : Inhabited F := ⟨0⟩
    letI : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) := IsUniformSpec.ofFintypeInhabited _
    let acc := Pr[fun x => (ballotForkSelector n x).isSome | ballotForkRunTrace oa]
    acc * (acc / (n+1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun out => out.isSome | ballotForkExtract oa n] := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) := IsUniformSpec.ofFintypeInhabited _
  have hb := FiatShamir.Fork.replayForkingBound forkVerifierAdapter forkUnitRelation Unit
    (ballotForkAdversary oa) n () (fun _ _ => True) (by intros; trivial)
    (ballotFork_selector_reachable oa n)
  apply hb.trans
  rw [ballotForkExtract, probEvent_map]
  apply probEvent_mono
  intro out _ hout
  obtain ⟨x,y,_,_,_,heq,_⟩ := hout
  simp [heq]

#print axioms ballotForkRunTrace_eq
#print axioms ballotFork_runtime_eq
#print axioms ballotFork_selector_reachable
#print axioms ballotFork_target_eq
#print axioms ballotFork_verified_valid
#print axioms ballotExtract_full_valid
#print axioms ballotFork_selected_challenge
#print axioms ballotFork_pair_extract_valid
#print axioms ballotFork_extract_valid
#print axioms ballotFork_extraction_probability_le

end ExplainableCrypto.Helios.Computational
