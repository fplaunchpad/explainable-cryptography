import ExplainableCrypto.Helios.Symbolic.SourceCommonFramePolicy

namespace ExplainableCrypto.Helios.Symbolic.SourcePolicyPaddingSPOT
open Historical General Source

def left : Frame {40} 1 := ⟨fun _ => .name 40⟩
def leftExpanded : Frame {40} 1 := ⟨fun _ => .unary .fst (.binary .pair (.name 40) (.name 99))⟩
def right : Frame {99} 1 := ⟨fun _ => .name 99⟩
def rightExpanded : Frame {99} 1 := ⟨fun _ => .unary .fst (.binary .pair (.name 99) (.name 40))⟩

theorem different_syntax_equal_observations : left.StaticEq leftExpanded :=
  Frame.staticEq_of_pointwise (fun _ => (EqE.equation (.fst _ _)).symm)

theorem unused_padding_preserves_and_reflects :
    (left.withPolicy ({40} ∪ {40,42,43})).StaticEq (leftExpanded.withPolicy ({40} ∪ {40,42,43})) ↔
      left.StaticEq leftExpanded :=
  Frame.staticEq_union_unused_iff left leftExpanded {40,42,43}
    (by simp [Frame.nameSupport,left,Term.nameSupport])
    (by simp [Frame.nameSupport,leftExpanded,Term.nameSupport])

theorem full_frame_values_unchanged :
    (leftExpanded.withPolicy {40,42,43}).value 0 =
      .unary .fst (.binary .pair (.name 40) (.name 99)) := rfl

/-- The new forbidden literal is replaced in the recipe by the fresh 43. -/
theorem forbidden_test_literal_has_fresh_surrogate :
    ((.binary .pair (.var (0 : Fin 1)) (.name 42) : Recipe 1).mapNames (Equiv.swap 42 43)) =
      .binary .pair (.var 0) (.name 43) ∧
      ((.binary .pair (.var (0 : Fin 1)) (.name 42) : Recipe 1).mapNames (Equiv.swap 42 43)).Public {40,42} := by
  constructor
  · simp [Term.mapNames]
  · simpa only [show ({42,40} : Finset Nat) = {40,42} by decide] using
      (show (.binary .pair (.var (0 : Fin 1)) (.name 42) : Recipe 1).Public {40} by simp [Term.Public]).swap_unused_policy
        42 43 (by decide) (by decide)

theorem literal_capture_changes_recipe_admissibility :
    (.name 40 : Recipe 1).Public ∅ ∧ ¬ (.name 40 : Recipe 1).Public {40} := by simp [Term.Public]

abbrev proofFrame : Frame ∅ 1 := ⟨fun _ => .spk (.name 1) (.name 2) (.const .zero)
  (.ternary .penc (.name 1) (.name 42) (.const .one))⟩

theorem fourth_proof_field_blocks_unused_padding : 42 ∈ proofFrame.nameSupport := by decide

theorem used_proof_name_fails_padding_premise :
    ¬ (∀ n ∈ ({42} : Finset Nat), n ∉ (∅ : Finset Nat) → n ∉ proofFrame.nameSupport) := by
  intro h
  exact h 42 (by simp) (by simp) fourth_proof_field_blocks_unused_padding

/-- A restriction unused by the entire executable body is removable too. -/
theorem unused_base_restriction_eliminates :
    Named.Structural
      (.newName (.base 99) (.embed (.plain (.input 9 (.output 0 (.var none) .nil)))) : Named Empty)
      (.embed (.plain (.input 9 (.output 0 (.var none) .nil)))) :=
  Named.Structural.name_unused _ _ (by decide)

theorem duplicate_restriction_eliminates :
    Named.Structural
      (.newName (.base 40) (.newName (.base 40) (.embed (.active (0 : Fin 1) (.name 40)))))
      (.newName (.base 40) (.embed (.active 0 (.name 40)))) :=
  Named.Structural.name_duplicate _ _

/-- Channel-policy irrelevance is only for extracted frames. Removing a used
channel binder from an executable process changes an invariant of Structural. -/
theorem used_channel_restriction_cannot_eliminate :
    ¬ Named.Structural
      (.newName (.channel 9) (.embed (.plain (.output 9 (.const .zero) .nil))) : Named Empty)
      (.embed (.plain (.output 9 (.const .zero) .nil))) := by
  intro h
  have hm : 9 ∈ (Named.embed (.plain (.output 9 (.const .zero) .nil)) : Named Empty).channels := by decide
  rw [← h.channels] at hm
  exact (by decide : 9 ∉ (Named.newName (.channel 9)
    (.embed (.plain (.output 9 (.const .zero) .nil))) : Named Empty).channels) hm

theorem canonical_padding_has_source_path :
    Named.Structural (Named.canonicalFrame {7,8} (leftExpanded.withPolicy ({40} ∪ {40,42,43})))
      (Named.canonicalFrame {9} leftExpanded) :=
  Named.canonicalFrame_policy_padding leftExpanded {7,8} {9} {40,42,43}
    (by simp [Frame.nameSupport,leftExpanded,Term.nameSupport])

theorem canonical_presentation_retains_padding_witness :
    (Named.canonicalFrame {7} left).RepresentsFrame {8,9} (left.withPolicy ({40} ∪ {42,43})) :=
  (Named.canonicalFrame_represents left).pad_policy {8,9} {42,43}
    (by simp [Frame.nameSupport,left,Term.nameSupport])

/-- Both pairs contain a free literal used privately by the other pair.
The general theorem supplies the required cross-freshening itself. -/
theorem independent_colliding_policies_align :
    ∃ (policy : Finset Nat) (φ ψ χ δ : Frame policy 1),
      (Named.canonicalFrame {7} left).RepresentsFrame ∅ φ ∧
      (Named.canonicalFrame {7} leftExpanded).RepresentsFrame ∅ ψ ∧
      (Named.canonicalFrame {8} right).RepresentsFrame ∅ χ ∧
      (Named.canonicalFrame {8} rightExpanded).RepresentsFrame ∅ δ ∧
      φ.StaticEq ψ ∧ χ.StaticEq δ :=
  Named.StaticEq.common_policy
    (.of_presentations (Named.canonicalFrame_represents left) (Named.canonicalFrame_represents leftExpanded)
      different_syntax_equal_observations)
    (.of_presentations (Named.canonicalFrame_represents right) (Named.canonicalFrame_represents rightExpanded)
      (Frame.staticEq_of_pointwise (fun _ => (EqE.equation (.fst _ _)).symm)))

def zeros : Frame ∅ 1 := ⟨fun _ => .const .zero⟩
def ones : Frame ∅ 1 := ⟨fun _ => .const .one⟩

theorem arbitrary_padding_does_not_hide_zero_one_difference (policy : Finset Nat) :
    ¬ (zeros.withPolicy policy).StaticEq (ones.withPolicy policy) := by
  intro h
  have he := (h (.var 0) (.const .zero) True.intro True.intro).mp (EqE.refl _)
  exact zero_not_one he.symm

/-- A common policy and two pairwise certificates do not assert cross-pair
equivalence. The missing middle-frame comparison cannot be silently dropped. -/
theorem common_policy_is_not_cross_pair_equivalence :
    zeros.StaticEq zeros ∧ ones.StaticEq ones ∧ ¬ zeros.StaticEq ones :=
  ⟨.refl _,.refl _,arbitrary_padding_does_not_hide_zero_one_difference ∅⟩

end ExplainableCrypto.Helios.Symbolic.SourcePolicyPaddingSPOT
