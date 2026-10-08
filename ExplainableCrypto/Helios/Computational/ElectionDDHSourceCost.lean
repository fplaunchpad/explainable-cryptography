import ExplainableCrypto.Helios.Computational.ElectionDDHExtractedFinish
import ExplainableCrypto.Helios.Computational.PrimeSamplers

/-! Derived interaction costs for the actual public-input construction.
Uniform-index draws count as oracle nodes, not as constant-time bit operations. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (State Source raw trustee)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem total_map {ι A B : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec A) (f : A → B) (n : Nat) :
    (f <$> oa).IsTotalQueryBound n ↔ oa.IsTotalQueryBound n :=
  isQueryBound_map_iff oa f n _ _

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem auxiliary_total (hc : (uniformSample F).IsTotalQueryBound 1)
    (key : Key G) (cache : Cache F G) :
    (ElectionReplaySource.auxiliary key cache).IsTotalQueryBound 1 := by
  unfold ElectionReplaySource.auxiliary
  split
  · trivial
  · simpa only [bind_pure_comp,total_map] using
      liftComp_total_query_bound (BallotOracleSpec F G) _ 1 hc

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem lower_step_total (hc : (uniformSample F).IsTotalQueryBound 1)
    (t : (Spec F G).Domain) (cache : Cache F G) :
    ((ElectionReplaySource.impl t).run cache).IsTotalQueryBound 1 := by
  cases t with
  | inl n =>
    change (do let c ← liftComp (liftM (unifSpec.query n) : ProbComp _) (BallotOracleSpec F G)
               pure (c,cache)).IsTotalQueryBound 1
    simp only [bind_pure_comp,total_map]
    exact liftComp_total_query_bound _ _ 1 (by exact ⟨by norm_num,fun _ => trivial⟩)
  | inr key =>
    cases key with
    | ballot s c =>
      change (do let a ← ballotChallengeOracle s c; pure (a,cache)).IsTotalQueryBound 1
      unfold ballotChallengeOracle
      rw [bind_pure_comp,total_map]
      exact ⟨by norm_num,fun _ => trivial⟩
    | key g pk c => exact auxiliary_total hc (.key g pk c) cache
    | decryption g pk ct share c => exact auxiliary_total hc (.decryption g pk ct share c) cache

omit [DecidableEq F] [AddCommGroup G] [Module F G] in
/-- Lowering charges auxiliary misses and ordinary random draws as well as
ballot queries, from any incoming full cache. -/
theorem lower_total_bound {A : Type} (oa : Comp F G A) (n : Nat)
    (hc : (uniformSample F).IsTotalQueryBound 1) (hb : oa.IsTotalQueryBound n)
    (cache : Cache F G) :
    ((ElectionReplaySource.lower oa).run cache).IsTotalQueryBound n := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec (BallotHashSpec F G) := IsUniformSpec.ofFintypeInhabited _
  exact hb.simulateQ_run_of_step (lower_step_total hc) cache

omit [DecidableEq F] in
private theorem raw_total {A : Type} (g pk : G) (oa : Comp F G A) (n : Nat)
    (hc : (uniformSample F).IsTotalQueryBound 1) (hb : oa.IsTotalQueryBound n)
    (s : State F G) : ((raw g pk oa).run s).IsTotalQueryBound (4*n) := by
  have hl := lower_total_bound oa n hc hb s.cache
  have h := ballotProgrammed_total_query_bound g pk hc _ n
    (liftComp_total_query_bound (BallotProofOracleSpec F G) _ n hl) s.ballot
  change (do let out ← (simulateQ (ballotProgrammedImpl g pk)
               (liftComp ((ElectionReplaySource.lower oa).run s.cache) (BallotProofOracleSpec F G))).run s.ballot
             pure (out.1.1,ElectionProgrammedSource.rebuild out.1.2 out.2)).IsTotalQueryBound (4*n)
  simpa only [bind_pure_comp,total_map] using h

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem trustee_total {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool))
    (n : Nat) (hb : ∀ cache, (step.run cache).IsTotalQueryBound n) (s : State F G) :
    ((trustee step).run s).IsTotalQueryBound n := by
  change (do let out ← liftComp (step.run s.cache) (BallotOracleSpec F G)
             pure (out.1.1,(⟨out.2,s.bad || out.1.2,s.programmed⟩ : State F G))).IsTotalQueryBound n
  simpa only [bind_pure_comp,total_map] using
    liftComp_total_query_bound (BallotOracleSpec F G) _ n (hb s.cache)

omit [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem trustee_sim_total {H : Type} [AddCommGroup H] [Module F H]
    (base key : H) (tag : H → Key G) (hc : (uniformSample F).IsTotalQueryBound 1)
    (cache : Cache F G) :
    ((TrusteeOracleSimulation.sim base key tag).run cache).IsTotalQueryBound 2 := by
  simp only [TrusteeOracleSimulation.sim,StateT.run,total_map]
  unfold TrusteeSimulation.transcript Schnorr.simTranscript
  change IsTotalQueryBound _ (1+(1+0))
  exact isTotalQueryBound_bind hc (fun _ => isTotalQueryBound_bind hc (fun _ => trivial))

omit [Fintype F] [DecidableEq F] in
private theorem statement_total (stmt : BallotStatement G)
    (hc : (uniformSample F).IsTotalQueryBound 1) (s : BallotProgrammedState F G) :
    ((ballotProgrammedStatement stmt).run s).IsTotalQueryBound 4 := by
  change (do let out ← liftComp ((strongBallotSimOracle (F := F) stmt).run s.cache) (BallotOracleSpec F G)
             pure (out.1.1,(⟨out.2,s.bad || out.1.2,stmt :: s.programmed⟩ : BallotProgrammedState F G))).IsTotalQueryBound 4
  simpa only [bind_pure_comp,total_map] using
    liftComp_total_query_bound (BallotOracleSpec F G) _ 4 (ballotSim_total_query_bound stmt s.cache hc)

omit [Fintype F] [DecidableEq F] in
private theorem ballot_total (g pk : G) (cts : Fin 2 → Ciphertext G)
    (hc : (uniformSample F).IsTotalQueryBound 1) (s : BallotProgrammedState F G) :
    ((ballot g pk cts).run s).IsTotalQueryBound 12 := by
  simp only [ballot,StateT.run_bind,StateT.run_pure]
  change IsTotalQueryBound _ (4+(4+(4+0)))
  apply isTotalQueryBound_bind (statement_total _ hc s)
  intro a
  apply isTotalQueryBound_bind (statement_total _ hc a.2)
  intro b
  exact isTotalQueryBound_bind (statement_total _ hc b.2) (fun _ => trivial)

omit [Fintype F] in
private theorem submit_total (g pk : G) (voter : Fin 3) (board : List (BoardEntry F G))
    (b : Ballot F G 2) (hc : (uniformSample F).IsTotalQueryBound 1)
    (s : BallotProgrammedState F G) : ((submit g pk voter board b).run s).IsTotalQueryBound 12 :=
  ballotProgrammed_total_query_bound g pk hc _ 3
    (liftComp_total_query_bound (BallotProofOracleSpec F G) _ 3
      (repairedSubmitOracle_total_query_bound g pk voter board b)) s

omit [Fintype F] in
private theorem ballots_total (g pk A T : G) (total a b : F) (vote : Bool)
    (hc : (uniformSample F).IsTotalQueryBound 1) (s : State F G) :
    ((ballots g pk A T total a b vote).run s).IsTotalQueryBound 48 := by
  have hh (cts : ElectionDDHConstruction.Pair G) (s : BallotProgrammedState F G) :
      ((honestPair g pk cts).run s).IsTotalQueryBound 48 := by
    simp only [honestPair,StateT.run_bind,StateT.run_pure]
    change IsTotalQueryBound _ (12+(12+(12+(12+0))))
    apply isTotalQueryBound_bind (ballot_total _ _ _ hc s)
    intro alice
    apply isTotalQueryBound_bind (submit_total _ _ _ _ _ hc alice.2)
    intro first
    apply isTotalQueryBound_bind (ballot_total _ _ _ hc first.2)
    intro bob
    exact isTotalQueryBound_bind (submit_total _ _ _ _ _ hc bob.2) (fun _ => trivial)
  change (do let out ← (challengePair g pk A T total a b vote).run s.ballot
             pure (out.1,ElectionProgrammedSource.rebuild s.cache out.2)).IsTotalQueryBound 48
  rw [bind_pure_comp,total_map]
  simpa only [challengePair,StateT.run_bind,StateT.run_pure,bind_pure_comp,StateT.run_map,total_map] using
    hh (ElectionDDHConstruction.paired g pk A T total a b vote).1 s.ballot

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem drawKnown_total (hc : (uniformSample F).IsTotalQueryBound 1) :
    (drawKnown (F := F)).IsTotalQueryBound 3 := by
  unfold drawKnown
  change IsTotalQueryBound _ (1+(1+(1+0)))
  exact isTotalQueryBound_bind hc (fun _ => isTotalQueryBound_bind hc
    (fun _ => isTotalQueryBound_bind hc (fun _ => trivial)))

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem liftBallot_total {A : Type} (oa : BallotOracleComp F G A)
    (n : Nat) (hb : oa.IsTotalQueryBound n) : (liftBallot oa).IsTotalQueryBound n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp only [liftBallot,simulateQ_pure]; trivial
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hb
    simp only [liftBallot,simulateQ_query_bind]
    cases t <;> exact ⟨hb.1,fun a => ih a _ (hb.2 a)⟩

/-- The actual prefix's complete interaction budget, including preparation,
key proof coins, vote/nonces, six ballot proofs and all three submissions.
The conservative factor four reuses the existing programmer cost theorem. -/
theorem prefix_total_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (P C : Nat) (hs : (uniformSample F).IsTotalQueryBound 1)
    (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C) :
    (prefixSource fingerprint g pk A T prepare adversary).IsTotalQueryBound (4*P+4*C+78) := by
  change ((preparedPrefix fingerprint g pk A T prepare adversary).run .empty).IsTotalQueryBound _
  simp only [preparedPrefix,StateT.run_bind,StateT.run_pure]
  rw [show 4*P+4*C+78 = 4*P+(4+(2+(12+(48+(4*C+(12+0)))))) by omega]
  apply isTotalQueryBound_bind (raw_total g 0 prepare P hs hp .empty)
  intro initial
  apply isTotalQueryBound_bind (raw_total g 0 _ 1 hs
    (liftComp_total_query_bound _ _ 1 (by change (1 : Nat) > 0 ∧ _; exact ⟨by norm_num,fun _ => trivial⟩)) initial.2)
  intro vote
  apply isTotalQueryBound_bind (trustee_total _ 2 (trustee_sim_total g pk _ hs) vote.2)
  intro key
  apply isTotalQueryBound_bind (raw_total g pk _ 3 hs
    (liftComp_total_query_bound _ _ 3 (drawKnown_total hs)) key.2)
  intro coins
  apply isTotalQueryBound_bind (ballots_total g pk A T coins.1.1 coins.1.2.1 coins.1.2.2 vote.1 hs coins.2)
  intro honest
  apply isTotalQueryBound_bind (raw_total g pk _ C hs (hc initial.1 _) honest.2)
  intro made
  apply isTotalQueryBound_bind (raw_total g pk _ 3 hs
    (liftBallot_total _ 3 (repairedSubmitOracle_total_query_bound g pk 2 _ made.1.1)) made.2)
  intro cast
  trivial

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
/-- Interpreting live ballot queries charges scalar draws on misses and preserves the total bound. -/
theorem ballot_runtime_total_bound {A : Type} (oa : BallotOracleComp F G A) (n : Nat)
    (hs : (uniformSample F).IsTotalQueryBound 1) (hb : oa.IsTotalQueryBound n)
    (cache : BallotOracleCache F G) : (runBallotOracle oa cache).IsTotalQueryBound n := by
  apply hb.simulateQ_run_of_step
  intro t state
  cases t with
  | inl index =>
    change (do let a ← liftM (unifSpec.query index); pure (a,state) : ProbComp _).IsTotalQueryBound 1
    exact ⟨by norm_num,fun _ => trivial⟩
  | inr key =>
    simp only [ballotRandomImpl,QueryImpl.add_apply_inr,randomOracle.run_eq]
    split
    · trivial
    · simpa only [bind_pure_comp,total_map] using hs

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem sampled_replay_total {A : Type} (oa : OracleComp (FiatShamir.Fork.wrappedSpec F) A)
    (n : Nat) (hs : (uniformSample F).IsTotalQueryBound 1) (hb : oa.IsTotalQueryBound n) :
    (simulateQ uniformSampleImpl oa).IsTotalQueryBound n := by
  apply hb.simulateQ_of_step
  intro t
  cases t with
  | inl index => exact ⟨by norm_num,fun _ => trivial⟩
  | inr token => exact hs

omit [Fintype F] [DecidableEq F] in
private theorem pair_total (g pk : G) (cts : Fin 2 → Ciphertext G) (shares : Fin 2 → G)
    (hs : (uniformSample F).IsTotalQueryBound 1) (cache : Cache F G) :
    ((ElectionTrusteeSimulation.simPair g pk cts shares).run cache).IsTotalQueryBound 4 := by
  change (do
    let a ← (TrusteeReachableSimulation.partialSim g pk (cts 0) (shares 0)).run cache
    let b ← (TrusteeReachableSimulation.partialSim g pk (cts 1) (shares 1)).run a.2
    pure ((![a.1.1,b.1.1],a.1.2 || b.1.2),b.2)).IsTotalQueryBound (2+(2+0))
  apply isTotalQueryBound_bind (trustee_sim_total _ _ _ hs cache)
  intro a
  exact isTotalQueryBound_bind (trustee_sim_total _ _ _ hs a.2) (fun _ => trivial)

omit [DecidableEq F] in
/-- Finishing includes four trustee-proof draws and the original guessing
callback, from any state/cache and on every fallback or rejection branch. -/
theorem finish_total_bound {Init Saved : Type} (g pk : G) (adversary : Init → Adversary F G Saved)
    (out : PrefixResult F G Init Saved) (w : Option (Option (Fin 2) → BallotWitness F))
    (D : Nat) (hs : (uniformSample F).IsTotalQueryBound 1)
    (hd : ∀ initial saved view, ((adversary initial).guessVote saved view).IsTotalQueryBound D)
    (s : State F G) (live : BallotOracleCache F G) :
    (ElectionProgrammedSource.evaluate (finishExtracted g pk adversary out w) s live).IsTotalQueryBound (4+4*D) := by
  apply ballot_runtime_total_bound _ _ hs
  simp only [finishExtracted,StateT.run_bind,StateT.run_pure]
  rw [show 4+4*D = 4+(4*D+0) by omega]
  apply isTotalQueryBound_bind (trustee_total _ 4 (pair_total g pk _ _ hs) s)
  intro proofs
  apply isTotalQueryBound_bind (raw_total g pk _ D hs (hd out.initial out.saved _) proofs.2)
  intro guess
  trivial

/-- Derived complete interaction cost for the implemented public-input game.
The complete prefix premise of the old repetition bound is discharged here.
This counts primitive uniform-index queries, not local bit-operation costs. -/
theorem extractedGame_total_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (n k P C D : Nat) (hs : (uniformSample F).IsTotalQueryBound 1)
    (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C)
    (hd : ∀ initial saved view, ((adversary initial).guessVote saved view).IsTotalQueryBound D) :
    (extractedGame fingerprint g pk A T prepare adversary n k).IsTotalQueryBound
      ((1+3*k)*(4*P+4*C+78)+(4+4*D)) := by
  have hpref := prefix_total_bound fingerprint g pk A T prepare adversary P C hs hp hc
  have hr := prefix_repeated_query_bound fingerprint g pk A T prepare adversary n k _ hpref
  unfold extractedGame
  apply isTotalQueryBound_bind (sampled_replay_total _ _ hs hr)
  intro out
  exact finish_total_bound g pk adversary out.1.1.1 out.2 D hs hd out.1.1.2 out.1.2

/-- Instantiate the primitive sampler premise with the existing pinned prime
scalar sampler. Attacker callback bounds remain explicit; no abstract source
budget or scalar-sampler cost is supplied by this caller. -/
theorem extractedGame_prime_total_bound {q : Nat} [Fact q.Prime] {H : Type}
    [AddCommGroup H] [Module (ZMod q) H] [DecidableEq H] {Init Saved : Type}
    (fingerprint : PublicParameters (ZMod q) H → Nat) (g pk A T : H)
    (prepare : Comp (ZMod q) H Init) (adversary : Init → Adversary (ZMod q) H Saved)
    (n k P C D : Nat) (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C)
    (hd : ∀ initial saved view, ((adversary initial).guessVote saved view).IsTotalQueryBound D) :
    (extractedGame fingerprint g pk A T prepare adversary n k).IsTotalQueryBound
      ((1+3*k)*(4*P+4*C+78)+(4+4*D)) :=
  extractedGame_total_bound fingerprint g pk A T prepare adversary n k P C D
    primeScalarSampler_total_bound hp hc hd

#print axioms ballot_runtime_total_bound
#print axioms extractedGame_prime_total_bound
#print axioms extractedGame_total_bound
#print axioms finish_total_bound
#print axioms lower_total_bound
#print axioms prefix_total_bound
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
