import ExplainableCrypto.Helios.Computational.PrimeReplay

/-! The explicit source's own saved-bit extractor, with newly derived selector
coverage and the existing generic joint bound. No old/new replay equality. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]
local instance primeExtractionInhabited : Inhabited (ZMod q) := ⟨0⟩
noncomputable local instance primeExtractionUniform : IsUniformSpec ((Unit →ₒ ZMod q) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _
attribute [local irreducible] repairedSubmissionPrimeSourceOracle repairedSubmissionSourceOracle

/-- Each accepted path supplies a physical replay occurrence for every covered
proof. The locations are derived from the existing path reachability theorem. -/
theorem repairedSubmissionPrimePath_locations (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (repairedSubmissionPrimeSourceOracle g pk vote attacker)))
    (ha : (PFunctor.FreeM.output _ path).1.Accepted) (i : Option (Fin 2)) :
    let oa := repairedSubmissionSelect g pk i <$> repairedSubmissionPrimeSourceOracle g pk vote attacker
    let selected := ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path
    ∃ s : Fin (n+15+1), ballotForkSelector (n+15) (PFunctor.FreeM.output _ selected) = some s ∧
      (PFunctor.FreeM.Cursor.locateAt? (P := (FiatShamir.Fork.wrappedSpec (ZMod q)).toPFunctor)
        (Sum.inr ()) (ballotForkRunTrace oa) selected s).isSome := by
  dsimp only
  have hs := repairedSubmissionPrimePath_selector g pk hg vote attacker n hb path i
  rw [show decide (PFunctor.FreeM.output _ path).1.Accepted = true from decide_eq_true ha] at hs
  cases he : ballotForkSelector (n+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path)) with
  | none => simp [he] at hs
  | some s =>
    refine ⟨s,rfl,?_⟩
    exact CfReachable.toPathCfReachable (ballotFork_selector_reachable _ (n+15)) _ s he

/-- All three selectors are enabled together with probability exactly equal
to actual joint submission acceptance. This is not joint replay success. -/
theorem repairedSubmissionPrimePath_selection_probability (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n) :
    Pr[fun path => ∀ i : Option (Fin 2),
      (ballotForkSelector (n+15) (PFunctor.FreeM.output _
        (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun (repairedSubmissionPrimeSourceOracle g pk vote attacker))] =
    Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
  let source := repairedSubmissionPrimeSourceOracle g pk vote attacker
  have hsource : Pr[fun raw => raw.1.Accepted | ballotReplaySourceRun source] =
      Pr[fun out => out.1.1.Accepted |
        runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
    calc
      _ = Pr[fun raw => raw.1.Accepted |
          simulateQ ballotForkEntropyImpl (ballotReplaySourceRun source)] :=
        (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
      _ = Pr[fun out => out.1.Accepted | runBallotOracle source ∅] := by
        have h := congrArg (fun m => Pr[fun out => out.1.Accepted | m])
          (ballotFork_runtime_eq source (∅,[]))
        have hempty : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ (ZMod q)).QueryCache) =
            (∅ : BallotOracleCache (ZMod q) G) := by funext key; rfl
        simpa only [hempty,probEvent_map,Function.comp_def,Prod.map,id_eq,ballotReplaySourceRun] using h
      _ = _ := by
        dsimp only [source]
        rw [probEvent_congr' (fun _ _ => Iff.rfl)
          (repairedSubmissionPrimeSource_semantic_runtime g pk vote attacker),
          repairedSubmissionSource_runtime,probEvent_map]
        rfl
  calc
    _ = Pr[fun path => (PFunctor.FreeM.output _ path).1.Accepted |
        replayFirstPath (ballotReplaySourceRun source)] := by
      apply probEvent_congr' _ rfl
      intro path _
      simp only [repairedSubmissionPrimePath_selector g pk hg vote attacker n hb path,
        decide_eq_true_eq,forall_const]
      rfl
    _ = Pr[fun raw => raw.1.Accepted | ballotReplaySourceRun source] := by
      have h := congrArg (fun m => Pr[fun raw => raw.1.Accepted | m])
        (map_output_replayFirstPath (ballotReplaySourceRun source))
      simpa only [probEvent_map,Function.comp_def] using h
    _ = _ := hsource

/-- Collect encoded entropy and run all three finite replay attempts on the
explicit nonce/scalar source. The old sampler is absent from this definition. -/
def repairedSubmissionPrimeBits_extract (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) := ballotJointReplayBits (repairedSubmissionPrimeSourceOracle g pk vote attacker)
      (repairedSubmissionSelect g pk) (n+15)

/-- Exact equality with generic joint replay of this same explicit source. -/
theorem repairedSubmissionPrimeBits_extract_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) : repairedSubmissionPrimeBits_extract g pk vote attacker n =
      ballotJointReplay (repairedSubmissionPrimeSourceOracle g pk vote attacker)
        (repairedSubmissionSelect g pk) (n+15) := by
  unfold repairedSubmissionPrimeBits_extract
  rw [ballotJointReplayBits_eq,ballotFiniteJointReplay_eq]

/-- Every successful run returns its accepting source result and all three
actual covered-ciphertext witnesses. Origin is in the explicit source itself. -/
theorem repairedSubmissionPrimeBits_extract_valid (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (result : RepairedSubmissionResult (ZMod q) G)
    (w : Option (Fin 2) → BallotWitness (ZMod q))
    (ho : some (result,w) ∈ support (repairedSubmissionPrimeBits_extract g pk vote attacker n)) :
    result.Accepted ∧ (∀ i, (result.ballot.coveredStatement g pk i).Witnesses (w i)) ∧
      ∃ cache, (result,cache) ∈ support
        (runBallotOracle (repairedSubmissionPrimeSourceOracle g pk vote attacker) ∅) := by
  rw [repairedSubmissionPrimeBits_extract_eq] at ho
  obtain ⟨hv,cache,hcache⟩ := ballotJointReplay_valid _ _ (n+15) result w ho
  have ha : result.Accepted := by
    by_contra hn
    obtain ⟨c,hproof⟩ := (hv none).2
    simp only [repairedSubmissionSelect,if_neg hn,Ballot.coveredStatement] at hproof
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hproof.1.1.symm)
  exact ⟨ha,fun i => (hv i).1,cache,hcache⟩

/-- The same historical prime-field integer vote constraint applies to witnesses
actually produced by the explicit-source extractor. -/
theorem repairedSubmissionPrimeBits_extract_consistent (g pk : G)
    (hg : Function.Injective (fun r : ZMod q => r • g)) (hq : 2 < q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (result : RepairedSubmissionResult (ZMod q) G)
    (w : Option (Fin 2) → BallotWitness (ZMod q))
    (ho : some (result,w) ∈ support (repairedSubmissionPrimeBits_extract g pk vote attacker n)) :
    result.Accepted ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    have hh : (1 : ZMod q) = 0 := hg (by simp [he])
    exact one_ne_zero hh
  obtain ⟨ha,hw,_⟩ := repairedSubmissionPrimeBits_extract_valid g pk hg0 vote attacker n result w ho
  exact ⟨ha,(result.ballot.covered_witnesses_sum g pk hg w hw).1,
    result.ballot.covered_witnesses_atMostOne_prime g pk hg hq w hw⟩

/-- Apply generic joint replay to the explicit source's own selectors. -/
theorem repairedSubmissionPrimeBits_extract_accepted_le (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (δ : ENNReal) :
    let α := Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    (α - 3*(n+16 : ENNReal)*δ) * (δ - (q : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | repairedSubmissionPrimeBits_extract g pk vote attacker n] := by
  have h := ballotJointReplay_selection_le (repairedSubmissionPrimeSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15) δ
  dsimp only at h ⊢
  rw [repairedSubmissionPrimePath_selection_probability g pk hg vote attacker n hb] at h
  rw [repairedSubmissionPrimeBits_extract_eq]
  simpa only [ZMod.card,Nat.cast_add,Nat.cast_ofNat,add_assoc,
    show (15 : ENNReal)+1=16 by norm_num] using h

/-- Preserve the historical honest-rejection/simulation loss in the actual
explicit-source extractor bound. δ is an analysis parameter, not algorithm input. -/
theorem repairedSubmissionPrimeBits_extract_le (g pk : G)
    (hg : Function.Injective (fun r : ZMod q => r • g)) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (δ : ENNReal) :
    let accepted := Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    let a := accepted - (9 * noncePointBound (ZMod q) + ENNReal.ofReal (90 / (q : ℝ)))
    (a - 3*(n+16 : ENNReal)*δ) * (δ - (q : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | repairedSubmissionPrimeBits_extract g pk vote attacker n] := by
  have hg0 : g ≠ 0 := by
    intro he
    have h : (1 : ZMod q) = 0 := hg (by simp [he])
    exact one_ne_zero h
  apply le_trans ?_ (repairedSubmissionPrimeBits_extract_accepted_le g pk hg0 vote attacker n hb δ)
  apply mul_le_mul' (tsub_le_tsub_right ?_ _) le_rfl
  simpa only [ZMod.card] using repairedSubmission_joint_acceptance_loss g pk hg vote attacker

#print axioms repairedSubmissionPrimePath_locations
#print axioms repairedSubmissionPrimePath_selection_probability
#print axioms repairedSubmissionPrimeBits_extract_accepted_le
#print axioms repairedSubmissionPrimeBits_extract_le
#print axioms repairedSubmissionPrimeBits_extract_eq
#print axioms repairedSubmissionPrimeBits_extract_valid
#print axioms repairedSubmissionPrimeBits_extract_consistent
end ExplainableCrypto.Helios.Computational
