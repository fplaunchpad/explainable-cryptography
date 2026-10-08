import ExplainableCrypto.Helios.Symbolic.StuckCheckOrigins
import ExplainableCrypto.Helios.Symbolic.AtomicObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.MinimumDestructorSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev first : Recipe 3 := .unary .fst (.var 1)
abbrev keyWrapper : Recipe 3 := .unary .fst (.binary .pair (.var 0) (.const .bottom))
abbrev checking (name : Nat) : Recipe 3 := .ternary .checkspk (.name 40) (.name 41) (.name name)

private theorem named_second_no_match (a c : Ground) (name : Nat) :
    ¬ ProofCheckMatch a (.name name) c := by
  rintro ⟨k, r, bit, _, _, hb, _⟩
  have hh := ((name_irreducible name).reducesModulo hb).head_eq
  cases hh

/-- The first honest ciphertext projection is an actual two-node minimum.
Its classified argument reaches a pair in both candidate worlds. -/
theorem first_projection_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value first ∧
    HonestProjectionForm 1 .fst (.var 1) ∧
    ∀ swap' : Bool, ∃ x y, ReducesModulo ((world swap').eval (.var 1)) (.binary .pair x y) := by
  have hv : EqE ((world swap).eval first)
      (General.ciphertext names 0 (General.choice swap left right 0).value 0) := by
    simpa [Frame.eval, first, Term.project, Term.drop, Term.subst, General.frame] using
      General.ballot_project_ciphertext names 0 (General.choice swap left right 0).value 0
  have hm : MinimalRecipe names.restricted (world swap).value first := by
    refine ⟨by trivial, ?_⟩
    intro r _ he
    exact ciphertext_recipe_size_ge_two (world swap).value _ _ _
      (fun v => General.frame_handle_not_ciphertext names swap left right v _ _ _) (he.symm.trans hv)
  obtain ⟨x, y, hp⟩ := ballot_tail_pair_value names swap left right 0 0 (by decide)
  have hf := minimum_successful_projection_form names swap left right names.restricted .fst (Or.inl rfl)
    (.var 1) hm hp
  exact ⟨hm, hf, fun swap' => hf.argument_pair_path names swap' left right⟩

private theorem drop_size (v : Fin 3) (k : Nat) : ((Term.var v : Recipe 3).drop k).nodeCount = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Term.drop_succ_outer]; simp only [Term.nodeCount, ih]; omega

/-- An early snd keeps a nonempty ballot tail. The final snd reaches bottom
and lies outside the successful-minimum class. Minimum size is not asserted for
arbitrary field or tail indices by this form-only control. -/
theorem tail_form_boundary (swap : Bool) :
    HonestProjectionForm 1 .snd (.var 1) ∧
    (∃ x y, ReducesModulo ((world swap).eval (.var 1)) (.binary .pair x y)) ∧
    ¬ HonestProjectionForm 1 .snd ((Term.var 1).drop 4) ∧
    EqE ((world swap).eval (.unary .snd ((Term.var 1).drop 4))) (.const .bottom) := by
  have hf : HonestProjectionForm 1 .snd (.var 1) := ⟨0, 0, by decide, rfl, Or.inr ⟨rfl, by decide⟩⟩
  refine ⟨hf, hf.argument_pair_path names swap left right, ?_, ?_⟩
  · rintro ⟨i, k, _, ha, hkind⟩
    have hsize := congrArg Term.nodeCount ha
    simp only [drop_size] at hsize
    rw [drop_size i.succ k] at hsize
    rcases hkind with h | ⟨_, hk⟩
    · cases h
    · change k + 1 < 5 at hk
      omega
  · simpa [PairObservationSPOT.tail, Term.drop] using (PairObservationSPOT.empty_tails_coincide swap).2.1

/-- The omitted-minimum mutation returns the election key from a constructed
pair, outside honest tuple data. This uses the one-candidate gate allocation. -/
theorem successful_projection_needs_minimum (swap : Bool) :
    keyWrapper.Public AtomicObservationSPOT.gateNames.restricted ∧
    EqE ((AtomicObservationSPOT.gateWorld swap).eval keyWrapper) (publicKey AtomicObservationSPOT.gateNames) ∧
    ¬ HonestProjectionForm 0 .fst (.binary .pair (.var 0) (.const .bottom)) ∧
    ¬ MinimalRecipe AtomicObservationSPOT.gateNames.restricted
      (AtomicObservationSPOT.gateWorld swap).value keyWrapper := by
  have he : EqE ((AtomicObservationSPOT.gateWorld swap).eval keyWrapper)
      ((AtomicObservationSPOT.gateWorld swap).eval (.var 0)) := (RootStep.fst _ _).sound
  refine ⟨by trivial, he, ?_, fun hm => hm.no_smaller (s := .var 0) trivial he (by decide)⟩
  rintro ⟨i, k, _, ha, _⟩
  cases k with
  | zero => cases ha
  | succ k => rw [Term.drop_succ_outer] at ha; cases ha

/-- Stuck checks with public literal arguments are exact four-node minima in
actual initial frames, rather than an uninhabited minimum-check premise. -/
theorem literal_check_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (name : Nat) (hn : name ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (checking name) := by
  have hp : (checking name).Public names.restricted := ⟨by change 40 ∉ names.restricted; decide, by change 41 ∉ names.restricted; decide, hn⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  obtain ⟨x, y, z, rfl⟩ := minimum_stuck_check_form names swap a b names.restricted r hr
    (named_second_no_match (.name 40) (.name name) 41) he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := x.nodeCount_pos
  have := y.nodeCount_pos
  have := z.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- The third argument is observable even when both checks remain stuck and
have the same key and second argument. This is the input-0 mutation witness. -/
theorem third_field_observable (swap : Bool) :
    ¬ ProofCheckMatch ((world swap).eval (.name 40)) ((world swap).eval (.name 41)) ((world swap).eval (.name 50)) ∧
    ¬ ProofCheckMatch ((world swap).eval (.name 40)) ((world swap).eval (.name 41)) ((world swap).eval (.name 60)) ∧
    ¬ EqE ((world swap).eval (checking 50)) ((world swap).eval (checking 60)) := by
  have hl := named_second_no_match (.name 40) (.name 50) 41
  have hr := named_second_no_match (.name 40) (.name 60) 41
  refine ⟨hl, hr, ?_⟩
  intro he
  have hn := (EqE.name_iff 50 60).mp ((EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hl hr).mp he).2.2
  omega

abbrev cipher (bit : Constant) : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 50) (.const bit)
abbrev proof (bit : Constant) (nonce : Nat := 50) : Ground :=
  .spk (.unary .pk (.name 40)) (.name nonce) (.const bit) (cipher bit)
abbrev checkValue (bit : Constant) : Ground :=
  .ternary .checkspk (.unary .pk (.name 40)) (cipher bit) (proof bit)

/-- Successful checks with distinct ciphertext arguments are equal through ok.
Public ok is a minimum recipe for that successful-check value, showing why the
stuck-value origin theorem retains its no-match premise. -/
theorem no_match_premises_required (swap : Bool) :
    EqE (checkValue .zero) (checkValue .one) ∧ ¬ EqE (cipher .zero) (cipher .one) ∧
    MinimalRecipe names.restricted (world swap).value (.const .ok) ∧
    EqE ((world swap).eval (.const .ok)) (checkValue .zero) ∧
    ¬ (∃ a b c : Recipe 3, (Term.const .ok : Recipe 3) = .ternary .checkspk a b c) := by
  have hz : EqE (checkValue .zero) (.const .ok) := (RootStep.check_zero _ _).sound
  have ho : EqE (checkValue .one) (.const .ok) := (RootStep.check_one _ _).sound
  refine ⟨hz.trans ho.symm, ?_, MinimalRecipe.of_nodeCount_one trivial rfl, hz.symm, ?_⟩
  · intro he
    exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp he).2.2
  · rintro ⟨a, b, c, h⟩
    cases h

abbrev probeFrame (good : Bool) : Frame ∅ 3 := ⟨fun v =>
  if v = 0 then .unary .pk (.name 40) else if v = 1 then cipher .zero
  else proof .zero (if good then 50 else 51)⟩
abbrev probe : Recipe 3 := .ternary .checkspk (.var 0) (.var 1) (.var 2)

/-- Changing a published proof can enable a check. The whole-check/ok probe
actually detects this change below the eight-node comparison bound. -/
theorem ok_probe_detects_new_match :
    ¬ EqE ((probeFrame false).eval probe) (.const .ok) ∧
    EqE ((probeFrame true).eval probe) (.const .ok) ∧
    ¬ (probeFrame false).ObservationsBelow (probeFrame true) 8 := by
  have hf : ¬ EqE ((probeFrame false).eval probe) (.const .ok) := by
    intro he
    obtain ⟨r, bit, _, hc, hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
    have hn := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.1
    have hm := ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
    have h : 51 = 50 := (EqE.name_iff _ _).mp (hn.trans hm.symm)
    omega
  have ht : EqE ((probeFrame true).eval probe) (.const .ok) := (RootStep.check_zero _ _).sound
  exact ⟨hf, ht, fun hobs => hf ((hobs probe (.const .ok) (by trivial) trivial (by decide)).mpr ht)⟩

/-- The full value-based branch is inhabited by unequal four-node minima.
One supplied stuck target has a reducible proof argument; diagonal candidates
provide the bounded premise without assuming different-vote static equivalence. -/
theorem minimum_stuck_check_step_inhabited :
    MinimalRecipe names.restricted (General.frame names false left left).value (checking 50) ∧
    MinimalRecipe names.restricted (General.frame names false left left).value (checking 60) ∧
    (checking 50).nodeCount + (checking 60).nodeCount = 8 ∧
    ¬ EqE ((General.frame names false left left).eval (checking 50))
      ((General.frame names false left left).eval (checking 60)) ∧
    (EqE ((General.frame names false left left).eval (checking 50))
        ((General.frame names false left left).eval (checking 60)) ↔
      EqE ((General.frame names true left left).eval (checking 50))
        ((General.frame names true left left).eval (checking 60))) := by
  have hl := literal_check_minimum false left left 50 (by decide)
  have hr := literal_check_minimum false left left 60 (by decide)
  let wrapped : Ground := .unary .fst (.binary .pair (.name 60) (.const .bottom))
  have hn := named_second_no_match (.name 40) (.name 50) 41
  have hn' := named_second_no_match (.name 40) wrapped 41
  have he : EqE ((General.frame names false left left).eval (checking 60))
      (.ternary .checkspk (.name 40) (.name 41) wrapped) :=
    .ternary .checkspk (.refl _) (.refl _) (RootStep.fst _ _).sound.symm
  refine ⟨hl, hr, rfl, ?_, minimum_stuck_check_equality_swap names left left (checking 50) (checking 60)
    hl hr hn hn' (.refl _) he (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he'
  have h := (EqE.name_iff 50 60).mp ((EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hn
    (named_second_no_match (.name 40) (.name 60) 41)).mp he').2.2
  omega

end ExplainableCrypto.Helios.Symbolic.MinimumDestructorSPOT
