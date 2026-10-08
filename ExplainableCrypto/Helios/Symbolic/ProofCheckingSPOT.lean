import ExplainableCrypto.Helios.Symbolic.ProofCheckingLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic.ProofCheckingSPOT

abbrev key : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev nonce : Term Nat := .unary .snd (.binary .pair (.const .bottom) (.name 1))
abbrev source (bit : Constant) : Term Nat :=
  .ternary .checkspk key (bitCiphertext key nonce bit) (bitProof key nonce bit)

theorem key_step : ModuloStep key (.name 0) := (RootStep.fst (.name 0) (.const .bottom)).to_modulo
theorem nonce_step : ModuloStep nonce (.name 1) := (RootStep.snd (.const .bottom) (.name 1)).to_modulo

def keyContexts (bit : Constant) : List (Context Nat) :=
  [.ternaryFirst .checkspk .hole (bitCiphertext key nonce bit) (bitProof key nonce bit),
   .ternarySecond .checkspk key (.ternaryFirst .penc .hole nonce (.const bit)) (bitProof key nonce bit),
   .ternaryThird .checkspk key (bitCiphertext key nonce bit)
     (.spkFirst .hole nonce (.const bit) (bitCiphertext key nonce bit)),
   .ternaryThird .checkspk key (bitCiphertext key nonce bit)
     (.spkFourth key nonce (.const bit) (.ternaryFirst .penc .hole nonce (.const bit)))]

def nonceContexts (bit : Constant) : List (Context Nat) :=
  [.ternarySecond .checkspk key (.ternarySecond .penc key .hole (.const bit)) (bitProof key nonce bit),
   .ternaryThird .checkspk key (bitCiphertext key nonce bit)
     (.spkSecond key .hole (.const bit) (bitCiphertext key nonce bit)),
   .ternaryThird .checkspk key (bitCiphertext key nonce bit)
     (.spkFourth key nonce (.const bit) (.ternarySecond .penc key .hole (.const bit)))]

theorem key_context_sources (bit : Constant) : ∀ ctx ∈ keyContexts bit, ctx.fill key = source bit := by
  intro ctx hc
  simp only [keyContexts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

theorem nonce_context_sources (bit : Constant) : ∀ ctx ∈ nonceContexts bit, ctx.fill nonce = source bit := by
  intro ctx hc
  simp only [nonceContexts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

/-- Four distinct key targets and three distinct nonce targets preserve the complete occurrence matrix. -/
theorem occurrence_targets_distinct (bit : Constant) :
    (keyContexts bit).length = 4 ∧ (nonceContexts bit).length = 3 ∧
    ((keyContexts bit).map (fun c => c.fill (.name 0))).Nodup ∧
    ((nonceContexts bit).map (fun c => c.fill (.name 1))).Nodup := by
  cases bit <;> decide

theorem checking_root (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    RootModuloStep (source bit) (.const .ok) :=
  ⟨_, _, .refl _, RootStep.check_bit key nonce bit hb, .refl _⟩

/-- Every key occurrence has an actual step and still reaches the fixed ok endpoint. -/
theorem all_key_occurrences_restore (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    ∀ ctx ∈ keyContexts bit, ModuloStep (source bit) (ctx.fill (.name 0)) ∧
      ReducesModulo (ctx.fill (.name 0)) (.const .ok) := by
  intro ctx hc
  have hs : ModuloStep (source bit) (ctx.fill (.name 0)) := by
    simpa only [key_context_sources bit ctx hc] using key_step.context ctx
  exact ⟨hs, proof_check_step_reaches_ok (checking_root bit hb) hs⟩

/-- Every nonce occurrence also reaches ok, for either bit. -/
theorem all_nonce_occurrences_restore (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    ∀ ctx ∈ nonceContexts bit, ModuloStep (source bit) (ctx.fill (.name 1)) ∧
      ReducesModulo (ctx.fill (.name 1)) (.const .ok) := by
  intro ctx hc
  have hs : ModuloStep (source bit) (ctx.fill (.name 1)) := by
    simpa only [nonce_context_sources bit ctx hc] using nonce_step.context ctx
  exact ⟨hs, proof_check_step_reaches_ok (checking_root bit hb) hs⟩

abbrev lastKeyOld (bit : Constant) : Term Nat :=
  .ternary .checkspk (.name 0) (bitCiphertext (.name 0) nonce bit)
    (.spk (.name 0) nonce (.const bit) (bitCiphertext key nonce bit))
abbrev allKeysChanged (bit : Constant) : Term Nat :=
  .ternary .checkspk (.name 0) (bitCiphertext (.name 0) nonce bit) (bitProof (.name 0) nonce bit)

/-- Independent fixed route: the bound ciphertext's fourth key occurrence is load-bearing. -/
theorem last_bound_key_required (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    (rootReduce (lastKeyOld bit)).isNone = true ∧
    ModuloStep (lastKeyOld bit) (allKeysChanged bit) ∧
    ModuloStep (allKeysChanged bit) (.const .ok) := by
  refine ⟨by cases bit <;> decide, ?_, (RootStep.check_bit (.name 0) nonce bit hb).to_modulo⟩
  exact key_step.context (.ternaryThird .checkspk (.name 0) (bitCiphertext (.name 0) nonce bit)
    (.spkFourth (.name 0) nonce (.const bit) (.ternaryFirst .penc .hole nonce (.const bit))))

/-- Both literal bits instantiate unconditional local confluence, with real root steps. -/
theorem both_bits_locally_confluent : LocallyConfluentAt (source .zero) ∧
    LocallyConfluentAt (source .one) ∧ ModuloStep (source .zero) (.const .ok) ∧
    ModuloStep (source .one) (.const .ok) :=
  ⟨locally_confluent_at_matching_check (checking_root .zero (Or.inl rfl)),
    locally_confluent_at_matching_check (checking_root .one (Or.inr rfl)),
    (checking_root .zero (Or.inl rfl)).to_modulo, (checking_root .one (Or.inr rfl)).to_modulo⟩

/-- The smallest bound-ciphertext mismatch from the executable gate. -/
theorem mismatched_bound_ciphertext_no_match :
    (rootReduce (Term.ternary .checkspk (.name 0) (bitCiphertext (.name 0) (.name 0) .zero)
      (.spk (.name 0) (.name 0) (.const .zero) (bitCiphertext (.name 0) (.name 1) .zero)) : Term Nat)).isNone = true := by
  decide

/-- Full field agreement is insufficient for a non-bit vote, and zero/one proofs are distinct. -/
theorem nonbits_and_wrong_bit_no_match : (rootReduce (source .ok)).isNone = true ∧
    (rootReduce (source .bottom)).isNone = true ∧
    (rootReduce (.ternary .checkspk key (bitCiphertext key nonce .zero) (bitProof key nonce .one))).isNone = true := by
  decide

abbrev expandedZero : Term Nat := .binary .add (.const .zero) (.const .zero)
abbrev expandedBallot : Term Nat := .ternary .penc key nonce expandedZero
abbrev expandedProof : Term Nat := .spk key nonce expandedZero expandedBallot
abbrev backgroundSource : Term Nat := .ternary .checkspk key expandedBallot expandedProof
abbrev backgroundChanged : Term Nat := .ternary .checkspk (.name 0) expandedBallot expandedProof

/-- All three vote fields use expanded E0 representatives, while an external key changes. -/
theorem background_vote_representatives :
    (rootReduce backgroundSource).isNone = true ∧ ModuloStep backgroundSource (.const .ok) ∧
    ModuloStep backgroundSource backgroundChanged ∧ ReducesModulo backgroundChanged (.const .ok) := by
  have he : BaseEq expandedZero (.const .zero) := .equation .zero_zero
  have hc : BaseEq expandedBallot (bitCiphertext key nonce .zero) := .ternary .penc (.refl _) (.refl _) he
  have hp : BaseEq expandedProof (bitProof key nonce .zero) := .spk (.refl _) (.refl _) he hc
  have hr : RootModuloStep backgroundSource (.const .ok) :=
    ⟨_, _, .ternary .checkspk (.refl _) hc hp, .check_zero key nonce, .refl _⟩
  have hi : ModuloStep backgroundSource backgroundChanged :=
    key_step.context (.ternaryFirst .checkspk .hole expandedBallot expandedProof)
  exact ⟨by decide, hr.to_modulo, hi, proof_check_step_reaches_ok hr hi⟩

/-- A general proof constructor may have a reducible third component, even though
valid E8/E9 vote fields do not. This exercises the fourth-argument inversion too. -/
theorem arbitrary_proof_component_peak :
    let third : Term Nat := .unary .fst (.binary .pair (.name 2) (.name 3))
    let fourth : Term Nat := .unary .fst (.binary .pair (.name 4) (.name 5))
    let a := Term.spk key nonce third fourth
    let b := Term.spk key nonce (.name 2) fourth
    let c := Term.spk key nonce third (.name 4)
    LocallyConfluentAt a ∧ ModuloStep a b ∧ ModuloStep a c ∧
      ModuloStep b (.spk key nonce (.name 2) (.name 4)) ∧
      ModuloStep c (.spk key nonce (.name 2) (.name 4)) ∧ b ≠ c := by
  have hk : LocallyConfluentAt key := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (name_irreducible 0).locally_confluent_at (constant_irreducible .bottom).locally_confluent_at)
  have hr : LocallyConfluentAt nonce := locally_confluent_at_unary .snd _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (constant_irreducible .bottom).locally_confluent_at (name_irreducible 1).locally_confluent_at)
  have hproj (n m : Nat) : LocallyConfluentAt (Term.unary .fst (.binary .pair (.name n) (.name m)) : Term Nat) :=
    locally_confluent_at_unary .fst _ (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (name_irreducible n).locally_confluent_at (name_irreducible m).locally_confluent_at)
  have ht := (RootStep.fst (V := Nat) (.name 2) (.name 3)).to_modulo
  have hf := (RootStep.fst (V := Nat) (.name 4) (.name 5)).to_modulo
  exact ⟨locally_confluent_at_spk _ _ _ _ hk hr (hproj 2 3) (hproj 4 5),
    ht.context (.spkThird key nonce .hole (.unary .fst (.binary .pair (.name 4) (.name 5)))),
    hf.context (.spkFourth key nonce (.unary .fst (.binary .pair (.name 2) (.name 3))) .hole),
    hf.context (.spkFourth key nonce (.name 2) .hole),
    ht.context (.spkThird key nonce .hole (.name 4)), by decide⟩

end ExplainableCrypto.Helios.Symbolic.ProofCheckingSPOT
