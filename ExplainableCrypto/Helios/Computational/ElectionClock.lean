import ExplainableCrypto.Helios.Computational.QueryClock
import ExplainableCrypto.Helios.Computational.ElectionCacheBudget

/-! Clock the two original election callbacks, with an explicit fallback ballot and absent
private state. Global caps hold even on arbitrary oversized callback inputs. Exact original-world
agreement requires bounds only on the actual prefix/cast/finish supports stated below.
These are source query clocks, not local-runtime or standard-PPT certificates.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionClock
open OracleComp OracleSpec ElectionOracle
variable {F G Saved : Type}
section Basic
variable [Zero F] [Zero G]

/-- A concrete fallback payload; its validity or acceptance is not assumed. -/
def zeroBallot : Ballot F G 2 :=
  ⟨fun _ => (0,0), fun _ => ⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩,
    ⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

/-- A cast timeout records no private state; guessing then returns false without querying. -/
def adversary (C J : Nat) (original : Adversary F G Saved) :
    Adversary F G (Option Saved) where
  castBallot before := QueryClock.clock C (zeroBallot, none)
    ((fun out => (out.1, some out.2)) <$> original.castBallot before)
  guessVote saved view := match saved with
    | none => pure false
    | some state => QueryClock.clock J false (original.guessVote state view)

theorem cast_bound (C J : Nat) (original : Adversary F G Saved) (before : PublicPrefix F G) :
    ((adversary C J original).castBallot before).IsTotalQueryBound C :=
  QueryClock.total_bound _ _ _

theorem guess_bound (C J : Nat) (original : Adversary F G Saved)
    (saved : Option Saved) (view : PublicResult F G) :
    ((adversary C J original).guessVote saved view).IsTotalQueryBound J := by
  cases saved with
  | none => trivial
  | some state => exact QueryClock.total_bound _ _ _

theorem cast_hash_bound (C J : Nat) (original : Adversary F G Saved)
    (before : PublicPrefix F G) :
    ((adversary C J original).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F) (G := G)) C :=
  (cast_bound C J original before).isQueryBoundP

theorem guess_hash_bound (C J : Nat) (original : Adversary F G Saved)
    (saved : Option Saved) (view : PublicResult F G) :
    ((adversary C J original).guessVote saved view).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F) (G := G)) J :=
  (guess_bound C J original saved view).isQueryBoundP

theorem cast_eq (C J : Nat) (original : Adversary F G Saved) (before : PublicPrefix F G)
    (h : (original.castBallot before).IsTotalQueryBound C) :
    (adversary C J original).castBallot before =
      (fun out => (out.1, some out.2)) <$> original.castBallot before := by
  apply QueryClock.eq_of_total_bound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using h

theorem guess_eq (C J : Nat) (original : Adversary F G Saved)
    (saved : Saved) (view : PublicResult F G)
    (h : (original.guessVote saved view).IsTotalQueryBound J) :
    (adversary C J original).guessVote (some saved) view = original.guessVote saved view :=
  QueryClock.eq_of_total_bound J false _ h

namespace Controls
private def immediate : Adversary F G Bool where
  castBallot _ := pure (zeroBallot, true)
  guessVote saved _ := pure saved

private def querying : Adversary F G Bool where
  castBallot _ := do
    let _ ← ask (.key 0 0 0)
    pure (zeroBallot, true)
  guessVote saved _ := pure saved

/-- Zero query fuel does not erase a returned private state. -/
theorem immediate_retains_state (before : PublicPrefix F G) :
    (adversary 0 0 (immediate (F := F) (G := G))).castBallot before =
      pure (zeroBallot, some true) := rfl

/-- A pending first query really takes the absent-state fallback. -/
theorem pending_query_times_out (before : PublicPrefix F G) :
    (adversary 0 0 (querying (F := F) (G := G))).castBallot before =
      pure (zeroBallot, none) := rfl

/-- The fallback cannot accidentally invoke the original guess on an invented saved value. -/
theorem absent_state_guess (view : PublicResult F G) :
    (adversary 0 0 (querying (F := F) (G := G))).guessVote none view = pure false ∧
      (adversary 0 0 (immediate (F := F) (G := G))).guessVote (some true) view =
        pure true := ⟨rfl, rfl⟩

#print axioms immediate_retains_state
#print axioms pending_query_times_out
#print axioms absent_state_guess
end Controls
end Basic

section Worlds
variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Preserve one actual cast/finish/guess interaction using only reached private states/views. -/
theorem interaction_eq (C J : Nat) (original : Adversary F G Saved)
    (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (hcast : (original.castBallot before).IsTotalQueryBound C)
    (hguess : ∀ submission saved, (submission, saved) ∈ support (original.castBallot before) →
      ∀ view ∈ support (finishWithCoins secret nonces before submission),
        (original.guessVote saved view).IsTotalQueryBound J) :
    (do
      let (submission,saved) ← (adversary C J original).castBallot before
      let view ← finishWithCoins secret nonces before submission
      (adversary C J original).guessVote saved view) = (do
      let (submission,saved) ← original.castBallot before
      let view ← finishWithCoins secret nonces before submission
      original.guessVote saved view) := by
  rw [cast_eq C J original before hcast]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr_of_forall_mem_support
  rintro ⟨submission, saved⟩ hout
  apply bind_congr_of_forall_mem_support
  intro view hview
  exact guess_eq C J original saved view (hguess submission saved hout view hview)

variable [Fintype F]

/-- Exact world equality on all typed-response source supports. No universal bound on
unreachable private states or arbitrary oversized public views is assumed. Prefix support is
kept in both callback premises, so the second bound concerns the same actual interaction. -/
theorem world_eq (C J : Nat) (original : Adversary F G Saved)
    (fingerprint : PublicParameters F G → Nat) (g : G) (vote : Bool)
    (hcast : ∀ secret keyNonce alice bob before,
      before ∈ support (prefixWithCoins fingerprint g secret keyNonce vote alice bob) →
        (original.castBallot before).IsTotalQueryBound C)
    (hguess : ∀ secret keyNonce alice bob before,
      before ∈ support (prefixWithCoins fingerprint g secret keyNonce vote alice bob) →
      ∀ submission saved, (submission, saved) ∈ support (original.castBallot before) →
      ∀ nonces view, view ∈ support (finishWithCoins secret nonces before submission) →
        (original.guessVote saved view).IsTotalQueryBound J) :
    world fingerprint g (adversary C J original) vote = world fingerprint g original vote := by
  unfold world
  apply bind_congr
  intro secret
  apply bind_congr
  intro keyNonce
  apply bind_congr
  intro nonces
  apply bind_congr
  intro pair
  apply bind_congr_of_forall_mem_support
  intro before hbefore
  exact interaction_eq C J original secret ![nonces.1,nonces.2] before
    (hcast secret keyNonce pair.1 pair.2 before hbefore)
    (fun submission saved hout view hview =>
      hguess secret keyNonce pair.1 pair.2 before hbefore submission saved hout _ view hview)
end Worlds

#print axioms cast_bound
#print axioms guess_bound
#print axioms cast_hash_bound
#print axioms guess_hash_bound
#print axioms cast_eq
#print axioms guess_eq
#print axioms interaction_eq
#print axioms world_eq
end ExplainableCrypto.Helios.Computational.ElectionClock
