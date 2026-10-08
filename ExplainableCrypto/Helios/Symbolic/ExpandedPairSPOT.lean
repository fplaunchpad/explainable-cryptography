import ExplainableCrypto.Helios.Symbolic.ExpandedPairTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedPairExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPairSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev tail (i : Fin 2) (k : Nat) : Recipe (ExpandedHandles 1) := (Term.var (expandedOld i.succ)).drop k

/-- Every nonempty retained tail preserves its exact voter and length identity. -/
theorem fresh_tail_identity (swap : Bool) (i j : Fin 2) (k l : Nat) (hk : k < 5) (hl : l < 5) :
    EqE ((world swap).eval (tail i k)) ((world swap).eval (tail j l)) ↔ i = j ∧ k = l :=
  expanded_ballot_tail_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right [] i j k l hk hl

/-- At the first empty position, different selector recipes are equal bottom
values. This refutes dropping the nonempty bound from tail identity. -/
theorem empty_tails_coincide (swap : Bool) :
    tail 0 5 ≠ tail 1 5 ∧
    EqE ((world swap).eval (tail 0 5)) (.const .bottom) ∧
    EqE ((world swap).eval (tail 1 5)) (.const .bottom) ∧
    EqE ((world swap).eval (tail 0 5)) ((world swap).eval (tail 1 5)) := by
  have h (i : Fin 2) : EqE ((world swap).eval (tail i 5)) (.const .bottom) := by
    have ht := expanded_ballot_tail_value names swap left right [] i 5 (by decide)
    have hl : (ballotFields names i (choice swap left right i).value).length = 5 := ballot_fields_length _ _ _
    simpa only [← hl,List.drop_length,Term.tuple] using ht
  exact ⟨by decide,h 0,h 1,(h 0).trans (h 1).symm⟩

/-- The accepted minimum equality branch is inhabited by unequal one-node
honest ballot handles in the actual different-vote worlds. -/
theorem minimum_pair_step_inhabited :
    MinimalRecipe names.restricted (world false).value (.var (expandedOld 1)) ∧
    MinimalRecipe names.restricted (world false).value (.var (expandedOld 2)) ∧
    ¬ EqE ((world false).eval (.var (expandedOld 1))) ((world false).eval (.var (expandedOld 2))) ∧
    (EqE ((world false).eval (.var (expandedOld 1))) ((world false).eval (.var (expandedOld 2))) ↔
      EqE ((world true).eval (.var (expandedOld 1))) ((world true).eval (.var (expandedOld 2)))) := by
  have hr : MinimalRecipe names.restricted (world false).value (.var (expandedOld 1)) := .of_nodeCount_one trivial rfl
  have hs : MinimalRecipe names.restricted (world false).value (.var (expandedOld 2)) := .of_nodeCount_one trivial rfl
  obtain ⟨a,b,hva⟩ := expanded_ballot_tail_pair_value names false left right [] 0 0 (by decide)
  obtain ⟨c,d,hvb⟩ := expanded_ballot_tail_pair_value names false left right [] 1 0 (by decide)
  refine ⟨hr,hs,?_,accepted_expanded_minimum_pair_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial _ _ hr hs hva hvb ?_⟩
  · intro he
    have hi := ((fresh_tail_identity false 0 1 0 0 (by decide) (by decide)).mp he).1
    exact absurd hi (by decide)
  · intro r s _ _ hsize
    have hr := r.nodeCount_pos
    have hs := s.nodeCount_pos
    change r.nodeCount+s.nodeCount < 2 at hsize
    omega

/-- Nested published pair fields preserve equality under the generic smaller
projection tests. Changing the second field is observable. -/
theorem constructed_pair_equality_nonconstant :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.binary .pair a (.binary .partialDecrypt a (.name 40))
    let s := Term.binary .pair a (.binary .partialDecrypt a (.name 41))
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let r := Term.binary .pair a (.binary .partialDecrypt a (.name 40))
  let s := Term.binary .pair a (.binary .partialDecrypt a (.name 41))
  have hr : r.Public names.restricted := by change True ∧ True ∧ 40 ∉ names.restricted; decide
  have hs : s.Public names.restricted := by change True ∧ True ∧ 41 ∉ names.restricted; decide
  refine ⟨expanded_pair_form_equality_swap names HistoricalFrameSPOT.fixture_names_fresh left left [] r s hr hs
    (Or.inl ⟨_,_,rfl⟩) (Or.inl ⟨_,_,rfl⟩) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  have h := ((EqE.partialDecrypt_iff _ _ _ _).mp ((EqE.pair_iff _ _ _ _).mp he).2).2
  exact absurd ((EqE.name_iff 40 41).mp h) (by decide)

/-- Both projections reconstruct an honest pair; replacing the tail with
bottom truncates real fields. No universal eta law is used. -/
theorem reconstruction_and_truncation (swap : Bool) :
    let h : Recipe (ExpandedHandles 1) := .var (expandedOld 1)
    EqE ((world swap).eval (.binary .pair (.unary .fst h) (.unary .snd h))) ((world swap).eval h) ∧
    ¬ EqE ((world swap).eval (.binary .pair (.unary .fst h) (.const .bottom))) ((world swap).eval h) := by
  obtain ⟨a,b,hv⟩ := expanded_ballot_tail_pair_value names swap left right [] 0 0 (by decide)
  refine ⟨(pair_reconstruction_of_value hv).symm,?_⟩
  intro he
  have hs := ((pair_equality_iff_projections _ _ _ ⟨a,b,hv⟩).mp he).2
  obtain ⟨x,y,hp⟩ := expanded_ballot_tail_pair_value names swap left right [] 0 1 (by decide)
  have h := tuple_eqE_pair_nonempty ([] : List Ground) (hs.trans hp)
  simp at h

/-- A published partial is not a pair, so eta on it is a false equation. -/
theorem partial_pair_eta_is_false (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    ¬ EqE ((world swap).eval r) ((world swap).eval (.binary .pair (.unary .fst r) (.unary .snd r))) := by
  dsimp only
  intro he
  have hv : EqE (tallyPartial names swap left right [] 0)
      (.binary .pair ((world swap).eval (.unary .fst (.var (expandedPartial 0))))
        ((world swap).eval (.unary .snd (.var (expandedPartial 0))))) := by
    simpa only [world,Frame.eval,Term.subst,expanded_frame_partial] using he
  have hf := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp hv).1
  cases hf

/-- Independent fixture: minimum public children give a nonminimum pair when
one public handle already contains that pair. This prevents false closure. -/
theorem minimum_children_do_not_imply_minimum_pair :
    MinimalRecipe ∅ ExpandedPairExperiments.pairHandle.value (.name 40) ∧
    MinimalRecipe ∅ ExpandedPairExperiments.pairHandle.value (.name 41) ∧
    EqE (ExpandedPairExperiments.pairHandle.eval (.binary .pair (.name 40) (.name 41)))
      (ExpandedPairExperiments.pairHandle.eval (.var 0)) ∧
    ¬ MinimalRecipe ∅ ExpandedPairExperiments.pairHandle.value (.binary .pair (.name 40) (.name 41)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ (∅ : Finset Nat); simp) rfl,
    .of_nodeCount_one (by change 41 ∉ (∅ : Finset Nat); simp) rfl,.refl _,?_⟩
  intro hm
  have h := hm.least (.var 0) trivial (.refl _)
  change 3 ≤ 1 at h
  omega

/-- Without minimum size, a successful projection wrapper lies outside both
exact pair forms. Its retained honest handle is a strictly shorter recipe. -/
theorem minimum_origin_requires_minimum (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 1)) (.const .bottom))
    EqE ((world swap).eval r) ((world swap).eval (.var (expandedOld 1))) ∧
    ¬ ExpandedPairObservationForm r ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 1)) (.const .bottom))
  have he : EqE ((world swap).eval r) ((world swap).eval (.var (expandedOld 1))) := .equation (.fst _ _)
  refine ⟨he,?_,fun hm => hm.no_smaller (s := .var (expandedOld 1)) trivial he (by decide)⟩
  rintro (⟨a,b,h⟩ | ⟨i,k,_,h⟩)
  · cases h
  · cases k with
    | zero => cases h
    | succ k => rw [Term.drop_succ_outer] at h; cases h

end ExplainableCrypto.Helios.Symbolic.ExpandedPairSPOT
