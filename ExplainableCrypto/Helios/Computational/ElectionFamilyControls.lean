import ExplainableCrypto.Helios.Computational.ElectionSecurityFamily

/-! Nonvacuity controls for the attacker resource interface. Public cryptographic-family
policies are parameters: these controls neither construct a hard DDH group nor prove DDH.
Both a passive member and a member issuing an actual hash query satisfy the resource fields.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionFamilyControls
open OracleComp OracleSpec ElectionOracle ElectionSecurityFamily ReductionEfficiency
variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]

private def passiveAdversary (F G : Type) [Zero F] [Zero G] : Adversary F G Unit where
  castBallot _ := pure (ElectionClock.zeroBallot, ())
  guessVote _ _ := pure false

/-- An actual member whose private encodings are injective empty encodings of Unit. -/
noncomputable def passive (representation : GroupRepresentation G) (scalarWidth : Polynomial Nat)
    (hwidth : ∀ n, (q n).size ≤ scalarWidth.eval n) (generator : ∀ n, G n)
    (hinjective : ∀ n, Function.Injective (fun r : ZMod (q n) => r • generator n)) :
    Family q G where
  representation := representation
  scalarWidth := scalarWidth
  scalar_width := hwidth
  fingerprintWidth := 0
  fingerprint := fun _ _ => 0
  fingerprint_width := by intros; simp
  generator := generator
  generator_injective := hinjective
  Init := fun _ => Unit
  Saved := fun _ => Unit
  encodeInit := fun _ _ => []
  encodeSaved := fun _ _ => []
  init_injective := fun _ _ _ _ => Subsingleton.elim _ _
  saved_injective := fun _ _ _ _ => Subsingleton.elim _ _
  prepare := fun _ => pure ()
  adversary := fun n _ => passiveAdversary (ZMod (q n)) (G n)
  prepareCost := 0
  initGrowth := 0
  castCost := 0
  savedGrowth := 0
  guessCost := 0
  prepare_queries := by intros; trivial
  prepare_size := by intros; simp
  cast_queries := by intros; trivial
  cast_size := by intros; simp
  guess_queries := by intros; trivial

variable (representation : GroupRepresentation G) (scalarWidth : Polynomial Nat)
  (hwidth : ∀ n, (q n).size ≤ scalarWidth.eval n) (generator : ∀ n, G n)
  (hinjective : ∀ n, Function.Injective (fun r : ZMod (q n) => r • generator n))

include representation scalarWidth hwidth generator hinjective in
/-- The public interface has a member under the separately supplied group/parameter policies. -/
theorem passive_member : Nonempty (Family q G) :=
  ⟨passive representation scalarWidth hwidth generator hinjective⟩

/-- Its exact source still executes the original election, including submission validation;
only the two adversarial callbacks are passive. -/
theorem passive_source (n : Nat) :
    let A := passive representation scalarWidth hwidth generator hinjective
    preparedGame (A.fingerprint n) (A.generator n) (A.prepare n) (A.adversary n) =
      game (fun _ => 0) (generator n) (passiveAdversary (ZMod (q n)) (G n)) := rfl

private def queryingAdversary {F G : Type} [Zero F] [Zero G] (g : G) : Adversary F G Unit where
  castBallot _ := do
    let _ ← ask (.key g g g)
    pure (ElectionClock.zeroBallot, ())
  guessVote _ _ := pure false

/-- A non-passive member with one real oracle query; its cap is not a semantic assumption. -/
noncomputable def querying : Family q G :=
  { passive representation scalarWidth hwidth generator hinjective with
    adversary := fun n _ => queryingAdversary (generator n)
    castCost := 1
    cast_queries := by
      intros
      exact ⟨by simp, fun _ => trivial⟩
    cast_size := by intros; exact Nat.zero_le _
    guess_queries := by intros; trivial }

/-- Exact callback tree: one original key-proof hash, followed by the retained payload. -/
theorem querying_cast (n : Nat) (before : PublicPrefix (ZMod (q n)) (G n)) :
    ((querying representation scalarWidth hwidth generator hinjective).adversary n ()).castBallot
      before = (do
        let _ ← ask (.key (generator n) (generator n) (generator n))
        pure (ElectionClock.zeroBallot, ())) := rfl

/-- The one-query control cannot collapse to the passive pure callback. -/
theorem querying_not_passive (n : Nat) (before : PublicPrefix (ZMod (q n)) (G n)) :
    ((querying representation scalarWidth hwidth generator hinjective).adversary n ()).castBallot
      before ≠ (pure (ElectionClock.zeroBallot, ()) : Comp (ZMod (q n)) (G n) _) := by
  rw [querying_cast]
  intro h
  cases h

private def many {F G : Type} [Zero F] [Zero G] (g : G) :
    List Bool → Comp F G (Ballot F G 2 × Unit)
  | [] => pure (ElectionClock.zeroBallot, ())
  | _ :: rest => do
    let _ ← ask (.key g g g)
    many g rest

private theorem many_bound_iff {F G : Type} [Zero F] [Zero G] (g : G)
    (word : List Bool) (fuel : Nat) :
    (many (F := F) g word).IsTotalQueryBound fuel ↔ word.length ≤ fuel := by
  induction word generalizing fuel with
  | nil => exact ⟨fun _ => Nat.zero_le _, fun _ => trivial⟩
  | cons bit rest ih =>
    change IsTotalQueryBound (liftM ((Spec F G).query (.inr (.key g g g))) >>=
      (fun _ => many g rest)) fuel ↔ _
    rw [isTotalQueryBound_query_bind_iff]
    constructor
    · rintro ⟨hp, hr⟩
      have h := (ih (fuel - 1)).mp (hr 0)
      simp only [List.length_cons]
      omega
    · intro h
      simp only [List.length_cons] at h
      exact ⟨by omega, fun _ => (ih (fuel - 1)).mpr (by omega)⟩

/-- An actual input-size-bounded family with arbitrarily large but unreachable private inputs.
Its preparation produces only the empty input; each supplied input bit causes one real hash. -/
noncomputable def lengthSensitive : Family q G :=
  { passive representation scalarWidth hwidth generator hinjective with
    Init := fun _ => List Bool
    encodeInit := fun _ => id
    init_injective := fun _ => Function.injective_id
    prepare := fun _ => pure []
    adversary := fun n word => {
      castBallot := fun _ => many (generator n) word
      guessVote := fun _ _ => pure false }
    castCost := Polynomial.X
    prepare_queries := by intros; trivial
    prepare_size := by
      intro n initial hi
      have he : initial = [] := by simpa using hi
      subst initial
      exact Nat.zero_le _
    cast_queries := by
      intro n initial before
      apply (many_bound_iff (generator n) initial _).mpr
      simp only [Polynomial.eval_X]
      change initial.length ≤ n + initial.length + _
      omega
    cast_size := by intros; exact Nat.zero_le _
    guess_queries := by intros; trivial }

/-- Exactly one private input is reachable from this family's actual preparation. -/
theorem lengthSensitive_reachable (n : Nat) (word : List Bool) :
    word ∈ support ((lengthSensitive representation scalarWidth hwidth generator hinjective).prepare n)
      ↔ word = [] := by
  change word ∈ support (pure [] : Comp (ZMod (q n)) (G n) (List Bool)) ↔ word = []
  rw [support_pure]
  rfl

/-- The actual prepared-family clock is transparent on the reached private input. -/
theorem lengthSensitive_reached_cast (n : Nat)
    (before : PublicPrefix (ZMod (q n)) (G n)) :
    let A := lengthSensitive representation scalarWidth hwidth generator hinjective
    (A.prepared.adversary n []).castBallot before = pure (ElectionClock.zeroBallot, some ()) := by
  exact QueryClock.clock_pure _ _ _

/-- A private word longer than the derived global cap is unreachable from preparation. -/
theorem lengthSensitive_overwide_unreachable (n : Nat) :
    let A := lengthSensitive representation scalarWidth hwidth generator hinjective
    List.replicate (A.castCap.eval n + 1) false ∉ support (A.prepare n) := by
  dsimp only
  rw [lengthSensitive_reachable]
  intro h
  have hl := congrArg List.length h
  simp at hl

/-- The globally clocked callback really differs on that unreachable oversized input.
The contradiction uses exact source query counts, without expanding the large polynomial cap. -/
theorem lengthSensitive_overwide_changed (n : Nat)
    (before : PublicPrefix (ZMod (q n)) (G n)) :
    let A := lengthSensitive representation scalarWidth hwidth generator hinjective
    let word := List.replicate (A.castCap.eval n + 1) false
    (A.prepared.adversary n word).castBallot before ≠
      (fun out => (out.1, some out.2)) <$> (A.adversary n word).castBallot before := by
  dsimp only
  let A := lengthSensitive representation scalarWidth hwidth generator hinjective
  let cap := A.castCap.eval n
  let word := List.replicate (cap + 1) false
  intro he
  have hb := ElectionClock.cast_bound cap (A.guessCap.eval n) (A.adversary n word) before
  change ((A.prepared.adversary n word).castBallot before).IsTotalQueryBound cap at hb
  rw [he] at hb
  let tag : Ballot (ZMod (q n)) (G n) 2 × Unit →
      Ballot (ZMod (q n)) (G n) 2 × Option Unit := fun out => (out.1, some out.2)
  have hm : (tag <$> many (F := ZMod (q n)) (generator n) word).IsTotalQueryBound cap := hb
  have ho := (isQueryBound_map_iff (many (F := ZMod (q n)) (generator n) word) tag cap
    (fun _ b => 0 < b) (fun _ b => b - 1)).mp hm
  have hl := (many_bound_iff (F := ZMod (q n)) (generator n) word cap).mp ho
  simp only [word, List.length_replicate] at hl
  omega

#print axioms lengthSensitive
#print axioms lengthSensitive_reachable
#print axioms lengthSensitive_reached_cast
#print axioms lengthSensitive_overwide_unreachable
#print axioms lengthSensitive_overwide_changed
#print axioms passive_member
#print axioms passive_source
#print axioms querying
#print axioms querying_cast
#print axioms querying_not_passive
end ExplainableCrypto.Helios.Computational.ElectionFamilyControls
