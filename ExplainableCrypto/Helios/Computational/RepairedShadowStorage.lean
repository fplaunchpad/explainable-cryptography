import ExplainableCrypto.Helios.Computational.RepairedFiniteProgrammed
import ExplainableCrypto.Helios.Computational.RepairedSubmissionCost

/-! Retained finite shadow-state bounds derived from actual source execution.
These count entries, not bits, sampler interactions or local computation time. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [DecidableEq G]

private theorem fresh_length (cache : BallotFiniteCache F G)
    (key : BallotStatement G × BallotCommitment G) (c : F) (h : cache.lookup key = none) :
    (cache.insert key c).entries.length = cache.entries.length+1 := by
  have hn : key ∉ cache := by
    intro hk
    have he := AList.lookup_isSome.mpr hk
    simp [h] at he
  rw [AList.entries_insert_of_notMem hn,List.length_cons]

private theorem raw_sizes (t : (BallotOracleSpec F G).Domain)
    (s : BallotFiniteProgrammedState F G)
    (out : (BallotOracleSpec F G).Range t × BallotFiniteProgrammedState F G)
    (ho : out ∈ support ((ballotFiniteProgrammedRaw t).run s)) :
    out.2.cache.entries.length ≤ s.cache.entries.length+1 ∧
      out.2.programmed.length = s.programmed.length := by
  cases t with
  | inl n =>
    simp only [ballotFiniteProgrammedRaw,QueryImpl.add,StateT.run,mem_support_bind_iff,
      mem_support_pure_iff] at ho
    obtain ⟨a,_,rfl⟩ := ho
    exact ⟨Nat.le_add_right _ _,rfl⟩
  | inr key =>
    cases h : s.cache.lookup key with
    | some a =>
      simp only [ballotFiniteProgrammedRaw,QueryImpl.add,StateT.run,h,mem_support_pure_iff] at ho
      subst out
      exact ⟨Nat.le_add_right _ _,rfl⟩
    | none =>
      simp only [ballotFiniteProgrammedRaw,QueryImpl.add,StateT.run,h,mem_support_bind_iff,
        mem_support_pure_iff] at ho
      obtain ⟨a,_,rfl⟩ := ho
      exact ⟨(fresh_length s.cache key a h).le,rfl⟩

variable [Field F] [AddCommGroup G] [Module F G]

omit [AddCommGroup G] [Module F G] in
private theorem program_sizes (s : BallotFiniteProgrammedState F G)
    (stmt : BallotStatement G) (t : BallotCommitment G × F × BallotResponse F) :
    (s.program stmt t).2.cache.entries.length ≤ s.cache.entries.length+1 ∧
      (s.program stmt t).2.programmed.length = s.programmed.length+1 := by
  unfold BallotFiniteProgrammedState.program
  split
  · exact ⟨Nat.le_add_right _ _,rfl⟩
  · rename_i h
    exact ⟨(fresh_length s.cache _ _ h).le,rfl⟩

variable [SampleableType F]

private theorem step_sizes (g pk : G) (t : (BallotProofOracleSpec F G).Domain)
    (s : BallotFiniteProgrammedState F G)
    (out : (BallotProofOracleSpec F G).Range t × BallotFiniteProgrammedState F G)
    (ho : out ∈ support (((ballotFiniteProgrammedImpl g pk) t).run s)) :
    out.2.cache.entries.length ≤ s.cache.entries.length+1 ∧
      out.2.programmed.length ≤ s.programmed.length+1 := by
  cases t with
  | inl t =>
    have h := raw_sizes t s out ho
    exact ⟨h.1,by omega⟩
  | inr wit =>
    simp only [ballotFiniteProgrammedImpl,QueryImpl.add,StateT.run,mem_support_bind_iff,
      mem_support_pure_iff] at ho
    obtain ⟨transcript,_,rfl⟩ := ho
    have h := program_sizes s (honestProofStatement g pk wit) transcript
    exact ⟨h.1,h.2.le⟩

/-- Every supported simulated execution has additive cache/history growth bounded
by the source's total queries, from arbitrary finite initial shadow state. -/
theorem runBallotFiniteProgrammed_storage_le {A : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) A) (m : Nat)
    (hb : oa.IsTotalQueryBound m) (s : BallotFiniteProgrammedState F G)
    (out : A × BallotFiniteProgrammedState F G)
    (ho : out ∈ support ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run s)) :
    out.2.cache.entries.length ≤ s.cache.entries.length+m ∧
      out.2.programmed.length ≤ s.programmed.length+m := by
  induction oa using OracleComp.inductionOn generalizing m s with
  | pure a =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at ho
    subst out
    exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _⟩
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hb
    simp only [simulateQ_query_bind,StateT.run_bind,mem_support_bind_iff] at ho
    obtain ⟨mid,hm,ho⟩ := ho
    have hs := step_sizes g pk t s mid hm
    have hr := ih mid.1 (m-1) (hb.2 mid.1) mid.2 ho
    constructor <;> omega

variable [DecidableEq F] [Fintype F]

/-- The actual repaired source's retained shadow cache and request history each
have at most m+19 entries. This uses the derived source budget, without a scalar
sampler-cost or caller-supplied state-invariant premise. -/
theorem repairedSubmissionFinite_shadow_storage_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (m : Nat)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m)
    (out : RepairedSubmissionResult F G × BallotFiniteProgrammedState F G)
    (ho : out ∈ support ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionOracle g pk vote attacker)).run .empty)) :
    out.2.cache.entries.length ≤ m+19 ∧ out.2.programmed.length ≤ m+19 := by
  simpa only [BallotFiniteProgrammedState.empty,AList.empty_entries,List.length_nil,
    Nat.zero_add] using runBallotFiniteProgrammed_storage_le g pk _ (m+19)
    (repairedSubmissionOracle_total_query_bound g pk vote attacker m hb) .empty out ho

/-- The same retained-state bound holds in the complete probabilistic execution
with the actual finite live oracle, rather than only in the raw source tree. -/
theorem repairedSubmissionFinite_shadow_runtime_storage_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (m : Nat)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m)
    (out : (RepairedSubmissionResult F G × BallotFiniteProgrammedState F G) ×
      BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteProgrammed g pk
      (repairedSubmissionOracle g pk vote attacker))) :
    out.1.2.cache.entries.length ≤ m+19 ∧ out.1.2.programmed.length ≤ m+19 := by
  apply repairedSubmissionFinite_shadow_storage_le g pk vote attacker m hb out.1
  apply support_simulateQ_run'_subset ballotFiniteCacheImpl _ ∅
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst ho

#print axioms runBallotFiniteProgrammed_storage_le
#print axioms repairedSubmissionFinite_shadow_storage_le
#print axioms repairedSubmissionFinite_shadow_runtime_storage_le
end ExplainableCrypto.Helios.Computational
