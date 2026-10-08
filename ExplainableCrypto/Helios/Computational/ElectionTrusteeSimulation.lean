import ExplainableCrypto.Helios.Computational.TrusteeReachableSimulation
import ExplainableCrypto.Helios.Computational.ElectionNonceSchedule
import ExplainableCrypto.Helios.Computational.RepairedSubmissionCost

/-! Compose the two actual trustee proofs, retaining public results, all cache
entries and a private sticky collision flag. This simulates proofs given correct
public shares; public-input share construction is proved separately. -/
namespace ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulation
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionCacheBudget TrusteeReachableSimulation
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev PartialProof (F G : Type) := SchnorrProof F (G × G)

/-- Both flags contribute to a private sticky flag; neither proof is discarded. -/
def pair (first second : StateT (Cache F G) ProbComp (PartialProof F G × Bool)) :
    StateT (Cache F G) ProbComp ((Fin 2 → PartialProof F G) × Bool) := fun cache => do
  let a ← first.run cache
  let b ← second.run a.2
  pure ((![a.1.1,b.1.1],a.1.2 || b.1.2),b.2)

noncomputable def realStep (g : G) (secret : F) (ct : Ciphertext G) :=
  TrusteeOracleSimulation.real (g,ct.1) secret
    (Key.decryption g (secret • g) ct (partialDecrypt secret ct))

noncomputable def realPair (g : G) (secret : F) (cts : Fin 2 → Ciphertext G) :=
  pair (realStep g secret (cts 0)) (realStep g secret (cts 1))

def simPair (g pk : G) (cts : Fin 2 → Ciphertext G) (shares : Fin 2 → G) :=
  pair (partialSim (F := F) g pk (cts 0) (shares 0)) (partialSim g pk (cts 1) (shares 1))

private theorem step_le (g : G) (secret : F) (ct : Ciphertext G)
    (hg : Function.Injective (fun r : F => r • g)) (cache : Cache F G) (k : Nat)
    (hc : Covered cache k) :
    tvDist ((realStep g secret ct).run cache)
      ((partialSim g (secret • g) ct (partialDecrypt secret ct)).run cache) ≤
        (1+(k : ℝ)) * (Fintype.card F : ℝ)⁻¹ := by
  obtain ⟨Q,hQ,hcov⟩ := hc
  have htag : Function.Injective (Key.decryption g (secret • g) ct (partialDecrypt secret ct)) := by
    intro x y h; cases h; rfl
  exact (TrusteeOracleSimulation.distance_le (g,ct.1) secret _ htag
    (TrusteeSimulation.partial_injective g hg ct) cache Q hcov).trans (by gcongr)

omit [Fintype F] [DecidableEq F] in
private theorem sim_step_covered (g pk : G) (ct : Ciphertext G) (share : G)
    (cache : Cache F G) (k : Nat) (hc : Covered cache k)
    (out : (PartialProof F G × Bool) × Cache F G)
    (ho : out ∈ support ((partialSim g pk ct share).run cache)) : Covered out.2 (k+1) := by
  simp only [partialSim,TrusteeOracleSimulation.sim,StateT.run,support_map] at ho
  obtain ⟨t,_,rfl⟩ := ho
  unfold TrusteeOracleSimulation.finish
  cases cache (Key.decryption g pk ct share t.1)
  · exact hc.cacheQuery _ _
  · exact hc.mono (Nat.le_succ k)

/-- Two proof simulations cost (2k+3)/|F| from a k-entry cover. The second
step's bound includes the first simulated proof's possible cache insertion. -/
theorem pair_distance_le (g : G) (secret : F) (cts : Fin 2 → Ciphertext G)
    (hg : Function.Injective (fun r : F => r • g)) (cache : Cache F G) (k : Nat)
    (hc : Covered cache k) :
    tvDist ((realPair g secret cts).run cache)
      ((simPair g (secret • g) cts (fun j => partialDecrypt secret (cts j))).run cache) ≤
        (2*(k : ℝ)+3) * (Fintype.card F : ℝ)⁻¹ := by
  let first := (realStep g secret (cts 0)).run cache
  let simulated := (partialSim g (secret • g) (cts 0) (partialDecrypt secret (cts 0))).run cache
  let after := fun (step : StateT (Cache F G) ProbComp (PartialProof F G × Bool))
      (a : (PartialProof F G × Bool) × Cache F G) =>
    (fun b => ((![a.1.1,b.1.1],a.1.2 || b.1.2),b.2)) <$> step.run a.2
  have hfirst := (tvDist_bind_right_le (after (realStep g secret (cts 1))) first simulated).trans
    (step_le g secret (cts 0) hg cache k hc)
  have hsecond : tvDist (simulated >>= after (realStep g secret (cts 1)))
      (simulated >>= after (partialSim g (secret • g) (cts 1) (partialDecrypt secret (cts 1)))) ≤
        (1+((k+1 : Nat) : ℝ)) * (Fintype.card F : ℝ)⁻¹ := by
    apply tvDist_bind_left_le_const
    intro a ha
    have hcov := sim_step_covered g (secret • g) (cts 0) (partialDecrypt secret (cts 0)) cache k hc a ha
    exact (tvDist_map_le _ _ _).trans (step_le g secret (cts 1) hg a.2 (k+1) hcov)
  have h := (tvDist_triangle _ _ _).trans (add_le_add hfirst hsecond)
  simpa only [realPair,simPair,pair,StateT.run,after,first,simulated,bind_pure_comp,
    Nat.cast_add,Nat.cast_one,show (1+(k : ℝ))+(1+((k : ℝ)+1))=2*(k : ℝ)+3 by ring,← add_mul] using h

/-- The original public fields, with an explicit public share vector. -/
def publication (before : PublicPrefix F G) (submission : Ballot F G 2)
    (cast : Decision × List (BoardEntry F G)) (shares : Fin 2 → G)
    (proofs : Fin 2 → PartialProof F G) : PublicResult F G :=
  ⟨before,submission,cast.1,cast.2,boardTally cast.2,shares,proofs,
    fun j => decodeBounded (F := F) before.parameters.generator cast.2.length
      (decryptWithPartial (boardTally cast.2 j) (shares j))⟩

/-- Proof simulation uses public key and supplied public shares. Deriving the
share function inside the DDH reduction is a separate construction obligation. -/
def finishSim (before : PublicPrefix F G) (submission : Ballot F G 2)
    (shareFor : Ciphertext G → G) :
    StateT (Cache F G) ProbComp (PublicResult F G × Bool) := fun cache => do
  let cast ← run (liftBallot (repairedSubmitOracle before.parameters.generator
    before.parameters.publicKey 2 before.board submission)) cache
  let shares := fun j => shareFor (boardTally cast.1.2 j)
  let out ← (simPair before.parameters.generator before.parameters.publicKey
    (boardTally cast.1.2) shares).run cast.2
  pure ((publication before submission cast.1 shares out.1.1,out.1.2),out.2)

omit [SampleableType F] in
private theorem submit_bound (g pk : G) (board : List (BoardEntry F G))
    (submission : Ballot F G 2) :
    (liftBallot (repairedSubmitOracle g pk 2 board submission)).IsQueryBoundP
      (isHash (F := F)) 3 := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec (HashSpec F G) := IsUniformSpec.ofFintypeInhabited _
  apply IsTotalQueryBound.isQueryBoundP
  apply (repairedSubmitOracle_total_query_bound g pk 2 board submission).simulateQ_of_step
  intro t
  cases t <;> exact ⟨Nat.zero_lt_succ _,fun _ => trivial⟩

private theorem real_finish_eq (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (cache : Cache F G) :
    (fun out => ((out.1,false),out.2)) <$> run (ElectionNonceSchedule.finish secret before submission) cache =
      (do let cast ← run (liftBallot (repairedSubmitOracle before.parameters.generator
            before.parameters.publicKey 2 before.board submission)) cache
          let shares := fun j => partialDecrypt secret (boardTally cast.1.2 j)
          let out ← (realPair before.parameters.generator secret (boardTally cast.1.2)).run cast.2
          pure ((publication before submission cast.1 shares out.1.1,out.1.2),out.2)) := by
  simp only [ElectionNonceSchedule.finish,run_bind,run_pure,run_liftProb,bind_map_left,map_bind,map_pure]
  apply bind_congr
  intro cast
  simp only [realPair,pair,StateT.run,realStep,TrusteeOracleSimulation.real]
  simp only [TrusteeOracleSimulation.withCoins,partialWithCoins,run_bind,run_pure,
    bind_assoc,pure_bind]
  rfl

/-- The actual scheduled finish, including submission rejection and full
publication, differs by at most (2k+9)/|F|. The three verification queries and
first simulated insertion are derived in the proof. -/
theorem finish_distance_le (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2)
    (hpk : before.parameters.publicKey = secret • before.parameters.generator)
    (hg : Function.Injective (fun r : F => r • before.parameters.generator))
    (cache : Cache F G) (k : Nat) (hc : Covered cache k) :
    tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionNonceSchedule.finish secret before submission) cache)
      ((finishSim before submission (partialDecrypt secret)).run cache) ≤
        (2*(k : ℝ)+9) * (Fintype.card F : ℝ)⁻¹ := by
  rw [real_finish_eq]
  unfold finishSim StateT.run
  apply tvDist_bind_left_le_const
  intro cast hcast
  have hcov := run_covered _ 3 k (submit_bound before.parameters.generator
    before.parameters.publicKey before.board submission) cache hc cast hcast
  have h := pair_distance_le before.parameters.generator secret (boardTally cast.1.2) hg cast.2 (k+3) hcov
  have hm := (tvDist_map_le (fun out => ((publication before submission cast.1
    (fun j => partialDecrypt secret (boardTally cast.1.2 j)) out.1.1,out.1.2),out.2)) _ _).trans h
  simpa only [hpk,StateT.run,bind_pure_comp,Nat.cast_add,Nat.cast_ofNat,
    show 2*((k : ℝ)+3)+3=2*(k : ℝ)+9 by ring] using hm

/-- Later attacker queries see the public result, while the collision flag
stays private and sticky. The result itself remains in the compared output. -/
def observe {A : Type} (next : PublicResult F G → Comp F G A)
    (out : (PublicResult F G × Bool) × Cache F G) :
    ProbComp (((PublicResult F G × A) × Bool) × Cache F G) :=
  (fun tail => (((out.1.1,tail.1),out.1.2),tail.2)) <$> run (next out.1.1) out.2

private theorem historical_observe_eq {A : Type} (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (next : PublicResult F G → Comp F G A) (cache : Cache F G) :
    𝒮[(fun out => ((out.1,false),out.2)) <$> run
      (do let rs ← liftProb (drawNoncePair F)
          let view ← finishWithCoins secret ![rs.1,rs.2] before submission
          let tail ← next view
          pure (view,tail)) cache] =
      𝒮[((fun out => ((out.1,false),out.2)) <$>
        run (ElectionNonceSchedule.finish secret before submission) cache) >>= observe next] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq
    (ElectionNonceSchedule.finish_eq secret before submission
      (fun view => do let tail ← next view; pure (view,tail)) cache)
    (fun out => ((out.1,false),out.2))
  simpa only [observe,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,
    run_bind,run_pure] using h

/-- The original historical finish after arbitrary bounded prior queries,
including arbitrary later oracle computation and complete result/cache output.
No initial cache cover or freshness premise is supplied. -/
theorem finish_after_queries_le {A B : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (next : PublicResult F G → Comp F G B)
    (hpk : before.parameters.publicKey = secret • before.parameters.generator)
    (hg : Function.Injective (fun r : F => r • before.parameters.generator)) :
    tvDist ((fun result => ((result.1,false),result.2)) <$> run
      (do let rs ← liftProb (drawNoncePair F)
          let view ← finishWithCoins secret ![rs.1,rs.2] before submission
          let tail ← next view
          pure (view,tail)) out.2)
      (((finishSim before submission (partialDecrypt secret)).run out.2) >>= observe next) ≤
        (2*(n : ℝ)+9) * (Fintype.card F : ℝ)⁻¹ := by
  have hc : Covered out.2 n := by
    simpa using run_covered prior n 0 hb ∅ Covered.empty out ho
  have h := (tvDist_bind_right_le (observe next) _ _).trans
    (finish_distance_le secret before submission hpk hg out.2 n hc)
  unfold tvDist at h ⊢
  rw [historical_observe_eq]
  exact h

omit [Fintype F] in
/-- Actual prefix execution supplies the trustee public-key/generator relation
needed by the local finish comparison. No acceptance or freshness is assumed. -/
theorem prefix_parameters (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret keyNonce : F) (vote : Bool) (alice bob : HonestCoins F)
    (cache : Cache F G) (out : PublicPrefix F G × Cache F G)
    (ho : out ∈ support (run (prefixWithCoins fingerprint g secret keyNonce vote alice bob) cache)) :
    out.1.parameters.generator = g ∧ out.1.parameters.publicKey = secret • g := by
  simp only [prefixWithCoins,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨key,_,cast,_,rfl⟩ := ho
  exact ⟨rfl,rfl⟩

#print axioms pair_distance_le
#print axioms finish_distance_le
#print axioms finish_after_queries_le
#print axioms prefix_parameters
end ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulation
