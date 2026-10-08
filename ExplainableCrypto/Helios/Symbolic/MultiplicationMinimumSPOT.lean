import ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumClosure
import ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev key : Recipe 3 := .unary .pk (.name 40)
abbrev keyValue : Ground := .unary .pk (.name 40)

private theorem public40 : (Term.name (V := Fin 3) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name (V := Fin 3) 41).Public names.restricted := by
  change 41 ∉ names.restricted; decide
private theorem public42 : (Term.name (V := Fin 3) 42).Public names.restricted := by
  change 42 ∉ names.restricted; decide
private theorem key_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value key :=
  minimum_pk_of_child names swap left right _ (.of_nodeCount_one public40 rfl)
private theorem key_normal : Irreducible keyValue := by
  intro t hs
  obtain ⟨u,hu,_⟩ := hs.pk_cases
  exact name_irreducible 40 u hu

private theorem product_normal {a b : Ground} (ha : Irreducible a) (hb : Irreducible b)
    (hfa : a.mulFactors = {a.baseClass}) (hfb : b.mulFactors = {b.baseClass})
    (hna : ¬ a.CiphertextValue) : Irreducible (.binary .mul a b) := by
  apply irreducible_of_normal_mul_factors
  · intro q hq
    exact (Multiset.mem_add.mp hq).elim (ha.normal_mul_factors q) (hb.normal_mul_factors q)
  · intro u hu
    obtain ⟨inputs,output,rest,h,hs,_⟩ := hu
    have hc := congrArg Multiset.card hs
    have hi := h.rank
    simp only [Term.mulFactors,hfa,hfb,Multiset.card_add,Multiset.card_singleton] at hc
    have hz : rest = 0 := Multiset.card_eq_zero.mp (by omega)
    subst rest
    have hm : a.baseClass ∈ inputs := by
      have he : inputs = {a.baseClass} + {b.baseClass} := by simpa [Term.mulFactors,hfa,hfb] using hs.symm
      rw [he]; simp
    obtain ⟨k,r,s,m,p,rfl,_⟩ := h
    simp [ciphertextPairFactors] at hm
    rcases hm with hm | hm
    · exact hna ⟨k,r,m,((baseClass_eq_iff _ _).mp hm).sound⟩
    · exact hna ⟨k,s,p,((baseClass_eq_iff _ _).mp hm).sound⟩

private theorem key_not_cipher : ¬ keyValue.CiphertextValue := by
  rintro ⟨k,r,m,he⟩
  exact pk_not_eqE_penc _ _ _ _ he

private theorem names_normal (x y : Nat) : Irreducible (.binary .mul (.name x) (.name y) : Ground) :=
  product_normal (name_irreducible x) (name_irreducible y) rfl rfl (by
    rintro ⟨k,r,m,he⟩
    obtain ⟨_,_,_,h,_⟩ := he.symm.penc_irreducible_shape (name_irreducible x)
    cases h)

/-- Repeated two-node key recipes retain two occurrences and attain a
five-node product minimum; the product cannot collapse to one key. -/
theorem non_atomic_duplicate_minimum (swap : Bool) :
    let r : Recipe 3 := .binary .mul key key
    MinimalRecipe names.restricted (world swap).value r ∧ r.nodeCount = 5 ∧
    r.mulLeaves.card = 2 ∧ ¬ EqE ((world swap).eval r) ((world swap).eval key) ∧
    Frame.SharedMinimum (world swap) (world (!swap)) r := by
  have hn := product_normal key_normal key_normal rfl rfl key_not_cipher
  have hm := minimum_mul_of_normal_groups names swap left right names.restricted key key
    (key_minimum swap) (key_minimum swap) (.refl _) (.refl _) rfl rfl hn
  exact ⟨hm,rfl,rfl,mul_not_eqE_pk _ _ _,.of_minimal hm⟩

/-- A ciphertext group beside a key remains a two-factor normal product,
and both globally minimum source pieces give a seven-node global minimum. -/
theorem ciphertext_group_beside_key (swap : Bool) :
    let c : Recipe 3 := .ternary .penc (.name 40) (.name 41) (.const .one)
    MinimalRecipe names.restricted (world swap).value (.binary .mul key c) ∧
    (Term.binary .mul key c).nodeCount = 7 := by
  have hc := minimum_penc_of_children names swap left right (.name 40) (.name 41) (.const .one)
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl) (.of_nodeCount_one trivial rfl)
  have hn := product_normal key_normal
    ((name_irreducible 40).penc (name_irreducible 41) (constant_irreducible .one)) rfl rfl key_not_cipher
  exact ⟨minimum_mul_of_normal_groups names swap left right names.restricted _ _ (key_minimum swap) hc
    (.refl _) (.refl _) rfl rfl hn,rfl⟩

abbrev first : Recipe 3 := .ternary .penc (.name 40) (.name 41) (.const .zero)
abbrev second : Recipe 3 := .ternary .penc (.name 40) (.name 42) (.const .one)
abbrev fused : Recipe 3 := .ternary .penc (.name 40) (.binary .compose (.name 41) (.name 42)) (.const .one)

/-- A normal-factor family can still fuse. Both children are minimum, but
the nine-node product has a six-node equivalent, so endpoint normality matters. -/
theorem fusion_requires_normal_endpoint (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value first ∧
    MinimalRecipe names.restricted (world swap).value second ∧
    EqE ((world swap).eval (.binary .mul first second)) ((world swap).eval fused) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .mul first second) ∧
    (Term.binary .mul first second).nodeCount = 9 ∧ fused.nodeCount = 6 ∧
    ((world swap).eval (.binary .mul first second)).NormalMulFactors ∧
    ¬ Irreducible ((world swap).eval (.binary .mul first second)) := by
  have ha := minimum_penc_of_children names swap left right (.name 40) (.name 41) (.const .zero)
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl) (.of_nodeCount_one trivial rfl)
  have hb := minimum_penc_of_children names swap left right (.name 40) (.name 42) (.const .one)
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public42 rfl) (.of_nodeCount_one trivial rfl)
  have he : EqE ((world swap).eval (.binary .mul first second)) ((world swap).eval fused) :=
    (RootStep.homomorphic _ _ _ _ _).sound.trans
      (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
  refine ⟨ha,hb,he,?_,rfl,rfl,?_,?_⟩
  · intro hm
    exact hm.no_smaller (s := fused) ⟨public40,⟨public41,public42⟩,trivial⟩ he (by decide)
  · have hfirst : Irreducible ((world swap).eval first) :=
      (name_irreducible 40).penc (name_irreducible 41) (constant_irreducible .zero)
    have hsecond : Irreducible ((world swap).eval second) :=
      (name_irreducible 40).penc (name_irreducible 42) (constant_irreducible .one)
    intro q hq
    exact (Multiset.mem_add.mp hq).elim (hfirst.normal_mul_factors q) (hsecond.normal_mul_factors q)
  · intro hn
    exact hn _ (RootStep.homomorphic _ _ _ _ _).to_modulo

/-- Minimum leaves guarantee a normal partition, but not minimum fusion
pieces. The same nonminimum nine-node product still obtains such a partition. -/
theorem partition_existence_is_not_minimality (swap : Bool) :
    (∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition names.restricted (world swap).value
      (.binary .mul first second) t)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .mul first second) := by
  have h := fusion_requires_normal_endpoint swap
  refine ⟨normal_partition_of_minimum_mul_leaves names swap left right names.restricted
    (.binary .mul first second) ⟨h.1.isPublic,h.2.1.isPublic⟩ ?_,h.2.2.2.1⟩
  intro a ha
  simp only [Term.mulLeaves,Multiset.mem_add,Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact h.1
  · exact h.2.1

/-- A projection wrapper is a public but nonminimum partition piece. The
endpoint is fully normal, yet the whole product can be shortened. -/
theorem minimum_piece_required (swap : Bool) :
    let a : Recipe 3 := .unary .fst (.binary .pair (.name 40) (.const .bottom))
    let r : Recipe 3 := .binary .mul a (.name 41)
    (∃ p : MultiplicationPartition names.restricted (world swap).value r
      (.binary .mul (.name 40) (.name 41)), p.pieces.card = 2) ∧
    Irreducible (Term.binary (V := Empty) .mul (.name 40) (.name 41)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  let p := (MultiplicationPartition.single
    (.unary .fst (.binary .pair (.name 40) (.const .bottom)) : Recipe 3) (.name 40)
    (restricted := names.restricted) (σ := (world swap).value)
    ⟨public40,trivial⟩ (RootStep.fst _ _).sound rfl).mul
      (MultiplicationPartition.single (.name 41) (.name 41) public41 (.refl _) rfl)
  refine ⟨⟨p,rfl⟩,names_normal 40 41,?_⟩
  intro hm
  exact hm.no_smaller (s := .binary .mul (.name 40) (.name 41)) ⟨public40,public41⟩
    (.binary .mul (RootStep.fst _ _).sound (.refl _)) (by decide)

def publishedFrame : Frame names.restricted 1 := ⟨fun _ => .binary .mul (.name 40) (.name 41)⟩

/-- A directly published product is a shorter handle despite minimum
literal pieces and a normal endpoint. The initial-frame scope is essential. -/
theorem initial_frame_required :
    MinimalRecipe names.restricted publishedFrame.value (.name 40) ∧
    MinimalRecipe names.restricted publishedFrame.value (.name 41) ∧
    Irreducible (Term.binary (V := Empty) .mul (.name 40) (.name 41)) ∧
    ¬ MinimalRecipe names.restricted publishedFrame.value (.binary .mul (.name 40) (.name 41)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl,names_normal 40 41,?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- Comparing a minimum partition to a competitor does not require minimum
competitor pieces: one removable wrapper gives the strict five-versus-eight bound. -/
theorem competitor_pieces_need_not_be_minimum (swap : Bool) :
    let r : Recipe 3 := .binary .mul key key
    let s : Recipe 3 := .binary .mul (.unary .fst (.binary .pair key (.const .bottom))) key
    r.nodeCount ≤ s.nodeCount ∧ r.nodeCount = 5 ∧ s.nodeCount = 8 ∧
    EqE ((world swap).eval r) ((world swap).eval s) ∧
    ¬ MinimalRecipe names.restricted (world swap).value s := by
  have hk := key_minimum swap
  let p := (MultiplicationPartition.single key keyValue hk.isPublic (σ := (world swap).value) (.refl _) rfl).mul
    (MultiplicationPartition.single key keyValue hk.isPublic (.refl _) rfl)
  let q := (MultiplicationPartition.single (.unary .fst (.binary .pair key (.const .bottom))) keyValue
    ⟨hk.isPublic,trivial⟩ (σ := (world swap).value) (RootStep.fst _ _).sound rfl).mul
    (MultiplicationPartition.single key keyValue hk.isPublic (.refl _) rfl)
  have hn := product_normal key_normal key_normal rfl rfl key_not_cipher
  have he := p.value.trans q.value.symm
  have hc := p.minimum_pieces_cost_le q hn hn (by
    intro x hx
    simp only [p,MultiplicationPartition.mul,MultiplicationPartition.single,
      Multiset.mem_add,Multiset.mem_singleton,or_self] at hx
    subst x
    exact hk) he
  refine ⟨hc,rfl,rfl,he,?_⟩
  intro hm
  exact hm.no_smaller (s := .binary .mul key key) ⟨hk.isPublic,hk.isPublic⟩ he.symm (by decide)

end ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumSPOT
