import ExplainableCrypto.Helios.Computational.ElectionDDHParameters
import ExplainableCrypto.Helios.Computational.ElectionDDHRandomSource
import ExplainableCrypto.Helios.Computational.ElectionDDHRejection

/-! Finite reduction of the actual prepared election to two public DDH tests.
No secret or successful-extraction certificate is an input to the reduction. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (evaluate)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual reduction: run the public-input game with the effective natural
repetition count and return its winning bit. All rejection/failure branches run. -/
noncomputable def ballotSecrecyDistinguisher {Init Saved : Type}
    (fingerprint : PublicParameters F G → Nat) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (N e : Nat) : DiffieHellman.DDHAdversary F G :=
  fun g pk A T => (fun out => out.1.1.2) <$>
    extractedGame fingerprint g pk A T prepare adversary N (ballotReplayTrials N e)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem event_le_of_tv {B : Type} (mx my : ProbComp B) (f : B → Bool) (ε : ENNReal)
    (h : ENNReal.ofReal (tvDist mx my) ≤ ε) :
    Pr[= true | f <$> mx] ≤ Pr[= true | f <$> my]+ε := by
  have ha := (abs_probOutput_toReal_sub_le_tvDist (f <$> mx) (f <$> my)).trans
    (tvDist_map_le f mx my)
  have hr : (Pr[= true | f <$> mx]).toReal ≤ (Pr[= true | f <$> my]).toReal+tvDist mx my :=
    by linarith [(abs_le.mp ha).2]
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (tvDist_nonneg _ _),
    ENNReal.ofReal_toReal probOutput_ne_top,ENNReal.ofReal_toReal probOutput_ne_top] at he
  exact he.trans (add_le_add le_rfl h)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem average_add {B : Type} (mx : ProbComp B) (f g r : B → ProbComp Bool) (ε : ENNReal)
    (h : ∀ x, Pr[= true | f x] ≤ Pr[= true | g x]+Pr[= true | r x]+ε) :
    Pr[= true | mx >>= f] ≤ Pr[= true | mx >>= g]+Pr[= true | mx >>= r]+ε := by
  simp only [probOutput_bind_eq_tsum]
  calc _ ≤ ∑' x, Pr[= x | mx]*(Pr[= true | g x]+Pr[= true | r x]+ε) :=
      ENNReal.tsum_le_tsum (fun x => mul_le_mul' le_rfl (h x))
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add,ENNReal.tsum_add,ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (by simp),one_mul]

private abbrev FullOutput (F G : Type) :=
  ((PublicResult F G × Bool) × ElectionProgrammedSource.State F G) × BallotOracleCache F G

private def comparisonWin {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (input : F × G × G) : ProbComp Bool :=
  (fun out => out.1.1.2) <$> evaluate
    (completedReal fingerprint g (input.1 • g) input.2.1 input.2.2 input.1 prepare adversary) .empty ∅

/-- Averaging actual complete-output comparisons over any distribution of
secret/challenge coordinates. This helper is used for both pinned DDH worlds. -/
private theorem averaged_accuracy {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c e : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c)
    (he : 0 < e) (hq : 12*(p+c+10)*e ≤ Fintype.card F) (inputs : ProbComp (F × G × G)) :
    let actual := inputs >>= fun x => ballotSecrecyDistinguisher fingerprint prepare adversary (p+c+9) e
      g (x.1 • g) x.2.1 x.2.2
    let ideal := inputs >>= comparisonWin fingerprint g prepare adversary
    let rejected := inputs >>= fun x => honestRejectDistinguisher fingerprint prepare adversary
      g (x.1 • g) x.2.1 x.2.2
    (Pr[= true | actual] ≤ Pr[= true | ideal]+Pr[= true | rejected]+(e:ENNReal)⁻¹) ∧
    (Pr[= true | ideal] ≤ Pr[= true | actual]+Pr[= true | rejected]+(e:ENNReal)⁻¹) := by
  constructor
  · apply average_add
    intro x
    have h := event_le_of_tv _ _ (fun out : FullOutput F G => out.1.1.2) _
      (extracted_finish_accuracy fingerprint g x.2.1 x.2.2 hg x.1 prepare adversary p c e hp hc he hq)
    simpa only [ballotSecrecyDistinguisher,comparisonWin,honestRejectDistinguisher,probOutput_map,
      decide_eq_true_eq,add_assoc] using h
  · apply average_add
    intro x
    have ht := extracted_finish_accuracy fingerprint g x.2.1 x.2.2 hg x.1 prepare adversary p c e hp hc he hq
    rw [tvDist_comm] at ht
    have h := event_le_of_tv _ _ (fun out : FullOutput F G => out.1.1.2) _ ht
    simpa only [ballotSecrecyDistinguisher,comparisonWin,honestRejectDistinguisher,probOutput_map,
      decide_eq_true_eq,add_assoc] using h


omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem gap_le (a b r : ENNReal) (e : Nat) (he : 0 < e)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hr : r ≠ ⊤)
    (h : (a ≤ b+r+(e:ENNReal)⁻¹) ∧ (b ≤ a+r+(e:ENNReal)⁻¹)) :
    |a.toReal-b.toReal| ≤ r.toReal+(e:ℝ)⁻¹ := by
  have hε : (e:ENNReal)⁻¹ ≠ ⊤ := by simp [ne_of_gt he]
  have h1 := ENNReal.toReal_mono (by simp [hb,hr,hε]) h.1
  have h2 := ENNReal.toReal_mono (by simp [ha,hr,hε]) h.2
  rw [ENNReal.toReal_add (by simp [hb,hr]) hε,ENNReal.toReal_add hb hr,
    ENNReal.toReal_inv,ENNReal.toReal_natCast] at h1
  rw [ENNReal.toReal_add (by simp [ha,hr]) hε,ENNReal.toReal_add ha hr,
    ENNReal.toReal_inv,ENNReal.toReal_natCast] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The pinned real DDH experiment is close to the actual secret-using
comparison. The error is its actual public honest-rejection probability plus
1/e; the secret/challenge coordinates are sampled, not supplied as premises. -/
theorem ballotSecrecy_real_gap {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c e : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c)
    (he : 0 < e) (hq : 12*(p+c+10)*e ≤ Fintype.card F) :
    |(Pr[= true | DiffieHellman.ddhExpReal g
        (ballotSecrecyDistinguisher fingerprint prepare adversary (p+c+9) e)]).toReal -
      (Pr[fun out => out.1.1.2 = true | realGame fingerprint g prepare adversary]).toReal| ≤
      (Pr[= true | DiffieHellman.ddhExpReal g
        (honestRejectDistinguisher fingerprint prepare adversary)]).toReal+(e:ℝ)⁻¹ := by
  have h := averaged_accuracy fingerprint g hg prepare adversary p c e hp hc he hq
    (do let secret ← uniformSample F; let x ← uniformSample F
        pure (secret,x • g,(secret*x) • g))
  simp only [bind_assoc,pure_bind,comparisonWin,← map_bind,probOutput_map] at h
  apply gap_le _ _ _ e he probOutput_ne_top probEvent_ne_top probOutput_ne_top
  simpa only [DiffieHellman.ddhExpReal,realGame,smul_smul,mul_comm] using h

/-- The actual random DDH experiment has bias at most its honest-rejection
probability plus 1/e. The ideal one-half probability is derived from the complete
random-mask theorem, not an assumption about public transcript secrecy. -/
theorem ballotSecrecy_random_gap {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c e : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c)
    (he : 0 < e) (hq : 12*(p+c+10)*e ≤ Fintype.card F) :
    |(Pr[= true | DiffieHellman.ddhExpRand g
        (ballotSecrecyDistinguisher fingerprint prepare adversary (p+c+9) e)]).toReal - 1/2| ≤
      (Pr[= true | DiffieHellman.ddhExpRand g
        (honestRejectDistinguisher fingerprint prepare adversary)]).toReal+(e:ℝ)⁻¹ := by
  let inputs : ProbComp (F × G × G) := do
    let secret ← uniformSample F; let x ← uniformSample F; let z ← uniformSample F
    pure (secret,x • g,z • g)
  have hi : Pr[= true | inputs >>= comparisonWin fingerprint g prepare adversary] = (2:ENNReal)⁻¹ := by
    simp only [inputs,bind_assoc,pure_bind,comparisonWin,← map_bind,probOutput_map]
    trans (1-Pr[⊥ | uniformSample F])*(2:ENNReal)⁻¹
    · apply probEvent_bind_of_const
      intro secret _
      trans (1-Pr[⊥ | uniformSample F])*(2:ENNReal)⁻¹
      · apply probEvent_bind_of_const
        intro x _
        exact completed_random_win fingerprint g (secret • g) (x • g) secret prepare adversary .empty ∅
      · simp
    · simp
  have h := averaged_accuracy fingerprint g hg prepare adversary p c e hp hc he hq inputs
  have hgap := gap_le _ _ _ e he probOutput_ne_top probOutput_ne_top probOutput_ne_top h
  rw [hi] at hgap
  simpa only [inputs,bind_assoc,pure_bind,DiffieHellman.ddhExpRand,
    ENNReal.toReal_inv,ENNReal.toReal_ofNat,one_div] using hgap


private theorem prepared_comparison_gap {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c) :
    |(Pr[fun out => out.1 = true | run (preparedGame fingerprint g prepare adversary) ∅]).toReal-
      (Pr[fun out => out.1.1.2 = true | realGame fingerprint g prepare adversary]).toReal| ≤
        (11*(p:ℝ)+2*c+131)/(Fintype.card F : ℝ) := by
  let actual := (fun out => ((out.1,false),out.2)) <$>
    run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅
  let ideal := ElectionProgrammedSource.result <$> realGame fingerprint g prepare adversary
  let win : ElectionFullSimulation.Output F G → Bool := fun out => out.1.1.2
  have h := (abs_probOutput_toReal_sub_le_tvDist (win <$> actual) (win <$> ideal)).trans
    ((tvDist_map_le win actual ideal).trans (prepared_real_distance_le fingerprint g hg prepare adversary p c hp hc))
  have hproj : run (preparedGame fingerprint g prepare adversary) ∅ =
      (fun out => (out.1.2,out.2)) <$> run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅ := by
    rw [← ElectionExtraction.preparedSource_project]
    simp only [run,simulateQ_map,StateT.run_map]
  rw [hproj]
  simpa only [actual,ideal,win,ElectionProgrammedSource.result,probOutput_map,probEvent_map,Function.comp_def] using h

/-- Full finite ballot-secrecy advantage bound for the original prepared
historical election. Both named DDH tests run actual public-input algorithms.
This theorem gives an explicit reduction, not yet standard-PPT adequacy or an
asymptotic claim that its right-hand side is negligible. -/
theorem prepared_ballot_secrecy_ddh_bound {Init Saved : Type}
    (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (p c e : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c)
    (he : 0 < e) (hq : 12*(p+c+10)*e ≤ Fintype.card F) :
    |(Pr[fun out => out.1 = true | run (preparedGame fingerprint g prepare adversary) ∅]).toReal-1/2| ≤
      18*(noncePointBound F).toReal + 3*((11*(p:ℝ)+2*c+131)/(Fintype.card F : ℝ)) +
      2*(e:ℝ)⁻¹ +
      DiffieHellman.ddhDistAdvantage g (ballotSecrecyDistinguisher fingerprint prepare adversary (p+c+9) e) +
      DiffieHellman.ddhDistAdvantage g (honestRejectDistinguisher fingerprint prepare adversary) := by
  have hsub : ∀ t, ElectionQueryBound.isBallot (F := F) (G := G) t → ElectionCacheBudget.isHash t := by
    intro t
    cases t <;> simp [ElectionQueryBound.isBallot,ElectionCacheBudget.isHash]
  have hp' := IsQueryBoundP.of_imp hsub hp
  have hc' := fun initial before => IsQueryBoundP.of_imp hsub (hc initial before)
  have hg0 : g ≠ 0 := by
    intro hz
    have hf : (1:F) = 0 := hg (by simp [hz])
    exact one_ne_zero hf
  have ho := prepared_comparison_gap fingerprint g hg prepare adversary p c hp hc
  have hr := ballotSecrecy_real_gap fingerprint g hg0 prepare adversary p c e hp' hc' he hq
  have hn := ballotSecrecy_random_gap fingerprint g hg0 prepare adversary p c e hp' hc' he hq
  have hrr := honestReject_real_le fingerprint g hg prepare adversary p c hp hc
  have hnr := honestReject_random_le fingerprint g hg prepare adversary p c hp hc
  have hb : noncePointBound F ≠ ⊤ := by
    simp only [noncePointBound,ENNReal.inv_ne_top]
    have hf : 1 < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast (by omega : Fintype.card F - 1 ≠ 0)
  have hrr' := ENNReal.toReal_mono (by finiteness) hrr
  have hnr' := ENNReal.toReal_mono (by finiteness) hnr
  have hL : 0 ≤ (11*(p:ℝ)+2*c+131)/(Fintype.card F : ℝ) := by positivity
  have hD : 0 ≤ DiffieHellman.ddhDistAdvantage g (honestRejectDistinguisher fingerprint prepare adversary) :=
    abs_nonneg _
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hL] at hrr'
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hL,
    ENNReal.toReal_ofReal hD] at hnr'
  have hd := abs_le.mp (le_refl (DiffieHellman.ddhDistAdvantage g
    (ballotSecrecyDistinguisher fingerprint prepare adversary (p+c+9) e)))
  exact abs_le.mpr ⟨by linarith only [hrr',hnr',(abs_le.mp ho).1,(abs_le.mp hr).2,(abs_le.mp hn).1,hd.1],
    by linarith only [hrr',hnr',(abs_le.mp ho).2,(abs_le.mp hr).1,(abs_le.mp hn).2,hd.2]⟩

/-- Complete interaction cost of the exact public DDH distinguisher over the
pinned prime-field sampler, with the same effective repetition count. Pure bit
operations and standard-PPT lowering remain separate obligations. -/
theorem ballotSecrecy_prime_cost {q : Nat} [Fact q.Prime] {H : Type}
    [AddCommGroup H] [Module (ZMod q) H] [DecidableEq H] {Init Saved : Type}
    (fingerprint : PublicParameters (ZMod q) H → Nat) (prepare : Comp (ZMod q) H Init)
    (adversary : Init → Adversary (ZMod q) H Saved) (g pk A T : H)
    (N e P C D : Nat) (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C)
    (hd : ∀ initial saved view, ((adversary initial).guessVote saved view).IsTotalQueryBound D) :
    (ballotSecrecyDistinguisher fingerprint prepare adversary N e g pk A T).IsTotalQueryBound
      ((1+3*(3456*(N+1)^3*e^4))*(4*P+4*C+78)+(4+4*D)) := by
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  exact extractedGame_accuracy_cost fingerprint g pk A T prepare adversary N e P C D hp hc hd

#print axioms prepared_ballot_secrecy_ddh_bound
#print axioms ballotSecrecy_prime_cost
#print axioms ballotSecrecy_real_gap
#print axioms ballotSecrecy_random_gap
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
