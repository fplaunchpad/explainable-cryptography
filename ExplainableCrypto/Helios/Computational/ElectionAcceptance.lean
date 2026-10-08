import ExplainableCrypto.Helios.Computational.ElectionExtraction

/-! Actual accepted submissions remain valid in the final shared cache after
all trustee and attacker actions. These invariants feed full-source selection. -/
namespace ExplainableCrypto.Helios.Computational.ElectionAcceptance
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionExtraction
variable {F G : Type} [DecidableEq G] [SampleableType F]

/-- Every full adaptive computation retains every earlier proof-domain answer. -/
theorem run_cache_le {A : Type} (oa : Comp F G A) (cache : Cache F G)
    (out : A × Cache F G) (ho : out ∈ support (run oa cache)) : cache ≤ out.2 := by
  classical
  apply simulateQ_run_preservesInv randomImpl (cache ≤ ·) ?_ oa cache le_rfl out ho
  apply QueryImpl.PreservesInv.add
  · intro t cache' hle out' ho'
    simp only [QueryImpl.ofLift_apply,StateT.run_monadLift,support_bind,support_pure,
      Set.mem_iUnion,Set.mem_singleton_iff] at ho'
    obtain ⟨_,_,rfl⟩ := ho'
    exact hle
  · exact QueryImpl.PreservesInv.withCaching_le uniformSampleImpl cache

omit [DecidableEq G] [SampleableType F] in
private theorem project_mono {a b : Cache F G} (h : a ≤ b) : project a ≤ project b := by
  intro key c hc
  exact h hc

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F]

private theorem prefix_generator (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret nonce : F) (vote : Bool) (alice bob : HonestCoins F) (cache : Cache F G)
    (out : PublicPrefix F G × Cache F G)
    (ho : out ∈ support (run (prefixWithCoins fingerprint g secret nonce vote alice bob) cache)) :
    out.1.parameters.generator = g := by
  simp only [prefixWithCoins,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨key,_,cast,_,rfl⟩ := ho
  rfl

private theorem finish_cached (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (cache : Cache F G) (out : PublicResult F G × Cache F G)
    (ho : out ∈ support (run (finishWithCoins secret nonces before submission) cache))
    (ha : out.1.decision = .accepted) :
    out.1.submission.CachedStrongValid out.1.beforeTally.parameters.generator
      out.1.beforeTally.parameters.publicKey (project out.2) := by
  simp only [finishWithCoins,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨cast,hcast,p0,h0,p1,h1,rfl⟩ := ho
  rw [liftBallot_run,support_map] at hcast
  obtain ⟨raw,hraw,he⟩ := hcast
  cases he
  have hv := (repairedSubmitOracle_accepted before.parameters.generator
    before.parameters.publicKey 2 before.board submission (project cache) raw hraw ha).1
  exact hv.mono _ _ _ (project_mono ((run_cache_le _ _ _ h0).trans (run_cache_le _ _ _ h1)))

variable [Fintype F]

private theorem sampled_generator (fingerprint : PublicParameters F G → Nat) (g : G)
    (vote : Bool) (cache : Cache F G) (out : (F × (F × F) × PublicPrefix F G) × Cache F G)
    (ho : out ∈ support (run (samplePrefix fingerprint g vote) cache)) :
    out.1.2.2.parameters.generator = g := by
  simp only [samplePrefix,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨secret,_,nonce,_,dec,_,pair,_,before,hbefore,rfl⟩ := ho
  exact prefix_generator fingerprint g secret.1 nonce.1 vote pair.1.1 pair.1.2 _ _ hbefore

/-- Derive final cached validity from the actual complete world, including the
attacker's final adaptive queries. The public generator is derived from setup. -/
theorem world_cached {State : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (adversary : Adversary F G State) (vote : Bool) (cache : Cache F G)
    (out : (PublicResult F G × Bool) × Cache F G)
    (ho : out ∈ support (run (worldSource fingerprint g adversary vote) cache))
    (ha : out.1.1.decision = .accepted) :
    out.1.1.submission.CachedStrongValid g out.1.1.beforeTally.parameters.publicKey (project out.2) := by
  simp only [worldSource,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,cast,hcast,view,hview,guess,hguess,rfl⟩ := ho
  have hv := finish_cached initial.1.1 ![initial.1.2.1.1,initial.1.2.1.2]
    initial.1.2.2 cast.1.1 cast.2 view hview ha
  have hbefore : view.1.beforeTally = initial.1.2.2 := by
    simp only [finishWithCoins,run_bind,run_pure,support_bind,support_pure,
      Set.mem_iUnion,Set.mem_singleton_iff] at hview
    obtain ⟨_,_,_,_,_,_,rfl⟩ := hview
    rfl
  have hg : view.1.beforeTally.parameters.generator = g := by
    rw [hbefore,sampled_generator fingerprint g vote cache initial hi]
  rw [hg] at hv
  exact hv.mono _ _ _ (project_mono (run_cache_le (adversary.guessVote cast.1.2 view.1) view.2 guess hguess))

/-- Acceptance in the original prepared election supplies all three valid
proofs in its final cache, with arbitrary earlier queries and saved state. -/
theorem prepared_cached {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (cache : Cache F G) (out : (PublicResult F G × Bool) × Cache F G)
    (ho : out ∈ support (run (preparedSource fingerprint g prepare adversary) cache))
    (ha : out.1.1.decision = .accepted) :
    out.1.1.submission.CachedStrongValid g out.1.1.beforeTally.parameters.publicKey (project out.2) := by
  simp only [preparedSource,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,_,vote,_,world,hw,rfl⟩ := ho
  exact world_cached fingerprint g (adversary initial.1) vote.1 vote.2 world hw ha

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [Fintype F] in
private theorem source_cache_runtime {A : Type} (oa : Comp F G A) :
    runBallotOracle (ElectionReplaySource.source oa) ∅ =
      (fun out => (out.1,project out.2)) <$> run oa (fun _ => none) := by
  have h := congrArg (fun m => (fun out => (out.1,project out.2)) <$> m)
    (ElectionReplaySource.lower_run oa (fun _ => none) ∅)
  simpa [ElectionReplaySource.source,runBallotOracle,simulateQ_map,StateT.run_map,
    Functor.map_map,Function.comp_def,ElectionReplaySource.restore,project_replace,
    show replace (fun _ => none) (∅ : BallotOracleCache F G) = (fun _ => none) by
      funext k; cases k <;> rfl] using h

/-- The replay source's actual final ballot cache contains each accepted proof
challenge. Its correspondence is reconstructed, not supplied by the caller. -/
theorem source_cached {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (out : (PublicResult F G × Bool) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle
      (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary)) ∅))
    (ha : out.1.1.decision = .accepted) :
    out.1.1.submission.CachedStrongValid g out.1.1.beforeTally.parameters.publicKey out.2 := by
  rw [source_cache_runtime,support_map] at ho
  obtain ⟨full,hfull,rfl⟩ := ho
  exact prepared_cached fingerprint g prepare adversary (fun _ => none) full hfull ha

#print axioms run_cache_le
#print axioms world_cached
#print axioms source_cached
#print axioms prepared_cached
end ExplainableCrypto.Helios.Computational.ElectionAcceptance
