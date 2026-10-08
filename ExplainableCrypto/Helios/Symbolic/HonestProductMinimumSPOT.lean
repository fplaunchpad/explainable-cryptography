import ExplainableCrypto.Helios.Symbolic.HonestProductMinima
import ExplainableCrypto.Helios.Symbolic.HonestProductMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.HonestProductMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev first : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.mul (.leaf (1,0)) (.leaf (0,1)))
abbrev second : Combination (HonestIndex 1) := .mul (.mul (.leaf (0,1)) (.leaf (0,1))) (.leaf (1,0))
abbrev repeated : Combination (HonestIndex 1) := .mul (.leaf (0,0)) (.leaf (0,0))

/-- Reassociation preserves every indexed selector cost, including repeated
three-node selectors. Distinct ten-node recipes are globally minimum and shared. -/
theorem indexed_reassociation_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (combinationRecipe first) ∧
    MinimalRecipe names.restricted (world swap).value (combinationRecipe second) ∧
    combinationRecipe first ≠ combinationRecipe second ∧
    BaseEq (combinationRecipe first) (combinationRecipe second) ∧
    (combinationRecipe first).nodeCount = 10 ∧ first.indices.card = 3 ∧
    Frame.SharedMinimum (world swap) (world (!swap)) (combinationRecipe first) := by
  have hi : first.indices = second.indices := by simp only [Combination.indices]; ac_rfl
  exact ⟨minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right first,
    minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right second,
    by decide,Combination.evaluate_baseEq_of_indices .mul trivial _ hi,rfl,rfl,
    honest_combination_shared names HistoricalFrameSPOT.fixture_names_fresh swap left right first _⟩

/-- Homomorphic fusion does not erase a duplicate nonce occurrence. The
five-node repeated product is minimum and differs from the two-node selector. -/
theorem duplicates_remain_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (combinationRecipe repeated) ∧
    (combinationRecipe repeated).nodeCount = 5 ∧
    ¬ EqE ((world swap).eval (combinationRecipe repeated))
      ((world swap).eval (combinationRecipe (n := 1) (.leaf (0,0)))) := by
  refine ⟨minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right repeated,rfl,?_⟩
  intro he
  have h := (combination_equality_iff_indices names HistoricalFrameSPOT.fixture_names_fresh swap left right repeated (.leaf (0,0))).mp he
  have hc := congrArg Multiset.card h
  simp [Combination.indices] at hc

/-- Every minimum competitor retains the full indexed occurrence bag and
the exact ten-node cost, even for valid nonliteral input vote representations. -/
theorem competitor_origin_and_cost (swap : Bool) (r : Recipe 3)
    (hm : MinimalRecipe names.restricted (world swap).value r)
    (he : EqE ((world swap).eval r) ((world swap).eval (combinationRecipe first))) :
    (∃ a, r = combinationRecipe a ∧ a.indices = first.indices) ∧ r.nodeCount = 10 := by
  obtain ⟨a,ha,hi⟩ := minimum_honest_combination_origin names HistoricalFrameSPOT.fixture_names_fresh
    swap left right r hm first he
  refine ⟨⟨a,ha,hi⟩,?_⟩
  rw [ha,combinationRecipe_nodeCount_eq hi]
  rfl

/-- One candidate still retains repeated voter occurrences; there is no
aggregate-proof alias in this ciphertext-selector minimum theorem. -/
theorem one_candidate_product_minimum (swap : Bool) :
    let a : Combination (HonestIndex 0) := .mul (.leaf (0,0)) (.mul (.leaf (1,0)) (.leaf (0,0)))
    MinimalRecipe ProofObservationSPOT.oneNames.restricted (ProofObservationSPOT.oneWorld swap).value (combinationRecipe a) ∧
    (combinationRecipe a).nodeCount = 8 :=
  ⟨minimum_honest_combination ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh swap
    ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight _,rfl⟩

/-- Colliding nonces let a cheaper selector represent a different candidate
position. The global product theorem includes singleton combinations. -/
theorem nonce_freshness_required (swap : Bool) :
    ¬ ProofObservationSPOT.colliding.Fresh ∧
    ¬ MinimalRecipe ProofObservationSPOT.colliding.restricted
      (frame ProofObservationSPOT.colliding swap right right).value (combinationRecipe (n := 1) (.leaf (0,1))) :=
  CompleteProjectionSPOT.ciphertext_freshness_required swap

abbrev twoVoters : Combination (HonestIndex 1) := .mul (.leaf (0,0)) (.leaf (1,0))
def publishedFrame : Frame names.restricted 3 :=
  ⟨fun i => if i = 0 then (world false).eval (combinationRecipe twoVoters) else (world false).value i⟩

/-- Publishing the whole honest product as another handle invalidates the
initial-frame minimum claim; the public five-node product then has a one-node equivalent. -/
theorem initial_frame_required :
    MinimalRecipe names.restricted (world false).value (combinationRecipe twoVoters) ∧
    (combinationRecipe twoVoters).Public names.restricted ∧
    ¬ MinimalRecipe names.restricted publishedFrame.value (combinationRecipe twoVoters) := by
  refine ⟨minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh false left right twoVoters,
    combinationRecipe_public _ _,?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- A real remaining nonminimum ciphertext product obtains an exact coherent
assembly with a constructed or mixed public group; no honest-only case is omitted. -/
theorem remaining_product_has_public_contribution (swap : Bool) :
    ∃ t : CiphertextAssembly 1,
      t.recipe = .binary .mul MultiplicationMinimumSPOT.first MultiplicationMinimumSPOT.second ∧
      t.recipe.Public names.restricted ∧ t.Coherent (world swap) ∧
      ((∃ r p, t.group = .constructed r p) ∨ (∃ r p a, t.group = .mixed r p a)) := by
  have h := MultiplicationMinimumSPOT.fusion_requires_normal_endpoint swap
  exact nonminimum_ciphertext_product_public_group names HistoricalFrameSPOT.fixture_names_fresh swap left right _ _
    h.1 h.2.1 h.2.2.2.1 ⟨.name 40,.binary .compose (.name 41) (.name 42),.const .one,h.2.2.1⟩

end ExplainableCrypto.Helios.Symbolic.HonestProductMinimumSPOT
