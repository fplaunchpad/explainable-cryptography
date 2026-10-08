import ExplainableCrypto.Helios.Computational.BallotFiniteLogged

/-! Concrete entry counts in the actual finite replay interpreter. Initial
cache/log offsets are retained; no unproved cache/log equality is assumed. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G A : Type} [DecidableEq G] [Field F] [Fintype F]
local instance storageInhabited : Inhabited F := ⟨0⟩
noncomputable local instance storageUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private def storageBalance (c l : Nat) (s : BallotFiniteLoggedState F G) : Prop :=
  s.1.entries.length+l = c+s.2.length

omit [Field F] [Fintype F] in
private theorem storage_step (c l : Nat) (t : (BallotOracleSpec F G).Domain)
    (s : BallotFiniteLoggedState F G) (hs : storageBalance c l s)
    (y : (BallotOracleSpec F G).Range t × BallotFiniteLoggedState F G)
    (hy : y ∈ support ((ballotFiniteLoggedImpl t).run s)) : storageBalance c l y.2 := by
  cases t with
  | inl n =>
    simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,mem_support_bind_iff,
      mem_support_pure_iff] at hy
    obtain ⟨a,_,rfl⟩ := hy
    exact hs
  | inr key =>
    cases h : s.1.lookup key with
    | some a =>
      simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h,mem_support_pure_iff] at hy
      subst y
      exact hs
    | none =>
      simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h,mem_support_bind_iff,
        mem_support_pure_iff] at hy
      obtain ⟨a,_,rfl⟩ := hy
      have hn : key ∉ s.1 := by
        intro hk
        have hx := AList.lookup_isSome.mpr hk
        simp [h] at hx
      unfold storageBalance at hs ⊢
      rw [AList.entries_insert_of_notMem hn,List.length_cons,List.length_append,List.length_singleton]
      omega

/-- The actual interpreter preserves the initial offset between stored cache
entries and chronological miss-log entries, for every supported execution. -/
theorem runBallotFiniteLogged_storage_balance (oa : BallotOracleComp F G A)
    (s : BallotFiniteLoggedState F G) (out : A × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged oa s)) :
    out.2.1.entries.length+s.2.length = s.1.entries.length+out.2.2.length := by
  exact simulateQ_run_preserves_inv_of_query ballotFiniteLoggedImpl
    (storageBalance s.1.entries.length s.2.length) (storage_step _ _)
    oa s (by rfl) out ho

/-- Empty initialization derives equal cache/log sizes; equality is not a
premise about an arbitrary state supplied by a caller. -/
theorem runBallotFiniteLogged_empty_sizes (oa : BallotOracleComp F G A)
    (out : A × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged oa (∅,[]))) :
    out.2.1.entries.length = out.2.2.length := by
  simpa only [AList.empty_entries,List.length_nil,Nat.add_zero,Nat.zero_add] using
    runBallotFiniteLogged_storage_balance oa (∅,[]) out ho

/-- Cache storage grows by at most the source's hash-query bound, with initial
cache and log sizes accounted for independently. -/
theorem runBallotFiniteLogged_cache_length_le [SampleableType F]
    (oa : BallotOracleComp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (s : BallotFiniteLoggedState F G) (out : A × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged oa s)) :
    out.2.1.entries.length ≤ s.1.entries.length+n := by
  have hbalance := runBallotFiniteLogged_storage_balance oa s out ho
  have hlog := runBallotFiniteLogged_log_length_le oa n hb s out ho
  omega

#print axioms runBallotFiniteLogged_storage_balance
#print axioms runBallotFiniteLogged_empty_sizes
#print axioms runBallotFiniteLogged_cache_length_le
end ExplainableCrypto.Helios.Computational
