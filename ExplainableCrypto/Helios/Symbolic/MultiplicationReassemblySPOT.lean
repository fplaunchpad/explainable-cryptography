import ExplainableCrypto.Helios.Symbolic.DecryptCheckCipherMulTransport
import ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblyExperiments

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblySPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev reveal (t : Recipe 3) : Recipe 3 := MinimumTransportSPOT.reveal t

private theorem public40 : (Term.name (V := Fin 3) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name (V := Fin 3) 41).Public names.restricted := by
  change 41 ∉ names.restricted; decide
private theorem public42 : (Term.name (V := Fin 3) 42).Public names.restricted := by
  change 42 ∉ names.restricted; decide

private theorem with_name_normal (t : Ground) (ht : Irreducible t)
    (hf : t.mulFactors = {t.baseClass}) (n : Nat) : Irreducible (.binary .mul t (.name n)) := by
  apply irreducible_of_normal_mul_factors
  · intro q hq
    exact (Multiset.mem_add.mp hq).elim (ht.normal_mul_factors q) ((name_irreducible n).normal_mul_factors q)
  · intro u hu
    obtain ⟨inputs,output,rest,h,hs,_⟩ := hu
    have hc := congrArg Multiset.card hs
    have hi := h.rank
    simp only [Term.mulFactors,hf,Multiset.card_add,Multiset.card_singleton] at hc
    have hz : rest = 0 := Multiset.card_eq_zero.mp (by omega)
    subst rest
    have hm : (Term.name (V := Empty) n).baseClass ∈ inputs := by
      have he : inputs = t.mulFactors + {(.name n : Ground).baseClass} := by simpa [Term.mulFactors] using hs.symm
      rw [he]; simp
    obtain ⟨k,r,s,m,p,rfl,_⟩ := h
    simp [ciphertextPairFactors] at hm
    rcases hm with hm | hm <;> have bad := ((baseClass_eq_iff _ _).mp hm).head_eq <;> cases bad

/-- The singleton branch reassembles a four-node wrapper into a one-node
minimum without requiring the source recipe itself to be minimum. -/
theorem singleton_wrapper_reassembly (swap : Bool) :
    let r : Recipe 3 := reveal (.name 40)
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval r) ((world swap).eval m) ∧
      EqE ((world (!swap)).eval r) ((world (!swap)).eval m) ∧
      r.nodeCount = 4 ∧ m.nodeCount = 1 := by
  have hn : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one public40 rfl
  let p := MultiplicationPartition.single (reveal (.name 40) : Recipe 3) (.name 40)
    (σ := (world swap).value) (restricted := names.restricted) ⟨public40,trivial⟩ (RootStep.fst _ _).sound rfl
  have hp := sharedMinimum_of_partition_shared_pieces names swap left right (world (!swap)) _ p
    (name_irreducible 40) (by
      intro x hx
      have he := Multiset.mem_singleton.mp hx
      subst x
      exact .of_recipe_eqE hn (RootStep.fst _ _).sound)
  obtain ⟨m,hm,he,he'⟩ := hp
  have hl := hm.least (.name 40) public40 (he.symm.trans p.value)
  have hpos := m.nodeCount_pos
  exact ⟨m,hm,he,he',rfl,by change m.nodeCount ≤ 1 at hl; omega⟩

/-- Duplicate occurrences survive reassembly. Two wrapped names shrink from
nine nodes to a three-node minimum, rather than collapsing to one name. -/
theorem duplicate_wrapper_reassembly (swap : Bool) :
    let r : Recipe 3 := .binary .mul (reveal (.name 40)) (reveal (.name 40))
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval r) ((world swap).eval m) ∧
      EqE ((world (!swap)).eval r) ((world (!swap)).eval m) ∧
      r.nodeCount = 9 ∧ m.nodeCount = 3 ∧
      ¬ EqE ((world swap).eval m) (.name 40) := by
  have hn : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one public40 rfl
  let p0 := MultiplicationPartition.single (reveal (.name 40) : Recipe 3) (.name 40)
    (σ := (world swap).value) (restricted := names.restricted) ⟨public40,trivial⟩ (RootStep.fst _ _).sound rfl
  let p := p0.mul p0
  have ht := with_name_normal (.name 40) (name_irreducible 40) rfl 40
  have hs := sharedMinimum_of_partition_shared_pieces names swap left right (world (!swap)) _ p ht (by
    intro x hx
    simp only [p,p0,MultiplicationPartition.mul,MultiplicationPartition.single,
      Multiset.mem_add,Multiset.mem_singleton,or_self] at hx
    subst x
    exact .of_recipe_eqE hn (RootStep.fst _ _).sound)
  obtain ⟨m,hm,he,he'⟩ := hs
  have heq := he.symm.trans p.value
  have htarget := minimum_mul_of_normal_groups names swap left right names.restricted (.name 40) (.name 40)
    hn hn (.refl _) (.refl _) rfl rfl ht
  have hl := hm.least (.binary .mul (.name 40) (.name 40)) ⟨public40,public40⟩ heq
  have hg := htarget.least m hm.isPublic heq.symm
  refine ⟨m,hm,he,he',rfl,by change m.nodeCount ≤ 3 at hl; change 3 ≤ m.nodeCount at hg; omega,?_⟩
  exact fun bad => mul_not_eqE_name _ _ _ (heq.symm.trans bad)

abbrev fused := MultiplicationMinimumSPOT.fused
abbrev group : Recipe 3 := .binary .mul MultiplicationMinimumSPOT.first MultiplicationMinimumSPOT.second

/-- A genuinely fused group is replaced before reassembly. The eleven-node
group-plus-name recipe has an eight-node shared global minimum. -/
theorem fused_group_reassembly (swap : Bool) :
    let r : Recipe 3 := .binary .mul group (.name 40)
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval r) ((world swap).eval m) ∧
      EqE ((world (!swap)).eval r) ((world (!swap)).eval m) ∧
      r.nodeCount = 11 ∧ m.nodeCount = 8 := by
  have h40 : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one public40 rfl
  have h41 : MinimalRecipe names.restricted (world swap).value (.name 41) := .of_nodeCount_one public41 rfl
  have h42 : MinimalRecipe names.restricted (world swap).value (.name 42) := .of_nodeCount_one public42 rfl
  have hnonce := minimum_compose_of_children names swap left right names.restricted _ _ h41 h42
  have hmin := minimum_penc_of_children names swap left right (.name 40)
    (.binary .compose (.name 41) (.name 42)) (.const .one) h40 hnonce (.of_nodeCount_one trivial rfl)
  have hraw : EqE group fused := (RootStep.homomorphic _ _ _ _ _).sound.trans
    (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
  let target : Ground := .ternary .penc (.name 40) (.binary .compose (.name 41) (.name 42)) (.const .one)
  let p := (MultiplicationPartition.single group target (σ := (world swap).value)
    (restricted := names.restricted) ⟨⟨public40,public41,trivial⟩,⟨public40,public42,trivial⟩⟩
    (hraw.subst _) rfl).mul
      (MultiplicationPartition.single (.name 40) (.name 40) public40 (.refl _) rfl)
  have ht := with_name_normal target
    ((name_irreducible 40).penc ((name_irreducible 41).compose (name_irreducible 42)) (constant_irreducible .one)) rfl 40
  have hs := sharedMinimum_of_partition_shared_pieces names swap left right (world (!swap)) _ p ht (by
    intro x hx
    simp only [p,MultiplicationPartition.mul,MultiplicationPartition.single,Multiset.mem_add,Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact .of_recipe_eqE hmin hraw
    · exact .of_minimal h40)
  obtain ⟨m,hm,he,he'⟩ := hs
  have heq := he.symm.trans p.value
  have htarget := minimum_mul_of_normal_groups names swap left right names.restricted fused (.name 40)
    hmin h40 (.refl _) (.refl _) rfl rfl ht
  have hl := hm.least (.binary .mul fused (.name 40)) ⟨hmin.isPublic,public40⟩ heq
  have hg := htarget.least m hm.isPublic heq.symm
  exact ⟨m,hm,he,he',rfl,by change m.nodeCount ≤ 8 at hl; change 8 ≤ m.nodeCount at hg; omega⟩

/-- A source-valid replacement can change a destination observation. This
refutes the one-frame mutation without denying the handle's own shared minimum. -/
theorem both_frame_equalities_required :
    EqE (MinimumTransportSPOT.source.eval (.var 0)) (MinimumTransportSPOT.source.eval (.name 70)) ∧
    ¬ EqE (MinimumTransportSPOT.destination.eval (.var 0)) (MinimumTransportSPOT.destination.eval (.name 70)) := by
  refine ⟨.refl _,?_⟩
  intro he
  have h := (EqE.name_iff 71 70).mp he
  omega

/-- No actual term can have an empty partition; there is no implicit unit
recipe for the empty branch of the multiset construction. -/
theorem empty_partition_impossible (swap : Bool) :
    ¬ ∃ r t, ∃ p : MultiplicationPartition names.restricted (world swap).value r t, p.pieces = 0 := by
  rintro ⟨r,t,p,hp⟩
  exact p.pieces_ne_zero hp

/-- The reduced interface excludes a normal name product. Its strict-piece
premise is inhabited on the diagonal and yields a shared minimum. -/
theorem non_ciphertext_product_discharged (swap : Bool) :
    let r : Recipe 3 := .binary .mul (.name 40) (.name 41)
    ¬ Frame.DecryptCheckCipherMulCase (world swap) r ∧
    Frame.SharedMinimum (world swap) (world swap) r := by
  have hn : ¬ ((world swap).eval (.binary .mul (.name 40) (.name 41))).CiphertextValue := by
    rintro ⟨k,nr,m,he⟩
    obtain ⟨_,_,_,bad,_⟩ := he.symm.penc_irreducible_shape
      (with_name_normal (.name 40) (name_irreducible 40) rfl 41)
    cases bad
  refine ⟨hn,minimum_children_non_ciphertext_mul_shared names swap left right (world swap) _ _
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl) hn ?_⟩
  intro s hp _
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) s hp
  exact ⟨m,hm,he,he⟩

/-- Whole-ciphertext fusion remains a real nonminimum case in the reduced
interface, with a nine-node product and a six-node equivalent. -/
theorem ciphertext_product_still_required (swap : Bool) :
    Frame.DecryptCheckCipherMulCase (world swap) group ∧
    ¬ MinimalRecipe names.restricted (world swap).value group := by
  have h := MultiplicationMinimumSPOT.fusion_requires_normal_endpoint swap
  exact ⟨⟨.name 40,.binary .compose (.name 41) (.name 42),.const .one,h.2.2.1⟩,h.2.2.2.1⟩

/-- The well-founded reduced criterion is inhabited for identical votes and
retains distinct public-name observations. Different-vote premises remain open. -/
theorem reduced_criterion_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.DecryptCheckCipherMulTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_cipher_mul_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblySPOT
