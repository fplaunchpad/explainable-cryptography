import ExplainableCrypto.Helios.Symbolic.HonestCiphertextMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- All nonempty honest ballot tails attain exact size k+1. Ciphertext-prefix
bounds use the first honest ciphertext selector; proof suffixes use prior bounds. -/
theorem minimum_ballot_tail (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat) (hk : k < fieldCount n) :
    MinimalRecipe ns.restricted (frame ns swap left right).value ((Term.var i.succ).drop k) := by
  by_cases hproof : n+1 ≤ k
  · exact minimum_proof_tail ns hf swap left right i k hproof hk
  · have hprefix : k < n+1 := by omega
    have hp := (ProjectionChain.drop i.succ k).isPublic ns.restricted
    obtain ⟨x,y,hvalue⟩ := ballot_tail_pair_value ns swap left right i k hk
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
    rcases minimum_pair_observation_form ns swap left right ns.restricted m hm (he.symm.trans hvalue) with
      ⟨u,v,rfl⟩ | ⟨j,l,hl,rfl⟩
    · have hfield : EqE ((frame ns swap left right).eval ((Term.var i.succ).project k))
          ((frame ns swap left right).eval u) :=
        (EqE.unary .fst he).trans (RootStep.fst _ _).sound
      have hle := (minimum_ciphertext_selector ns hf swap left right i ⟨k,hprefix⟩).least u hm.isPublic.1 hfield
      exact hm.of_equivalent_size hp he (by
        simp only [Term.drop_nodeCount, Term.project_nodeCount, Term.nodeCount] at hle ⊢
        omega)
    · have hpos := ((ballot_tail_equality_iff ns hf swap left right i j k l hk hl).mp he).2
      exact hm.of_equivalent_size hp he (by simp only [Term.drop_nodeCount, Term.nodeCount]; omega)

/-- Nonempty tails use themselves; the empty tail uses literal bottom. -/
theorem ballot_tail_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat) (hk : k ≤ fieldCount n) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) ((Term.var i.succ).drop k) := by
  by_cases hnonempty : k < fieldCount n
  · exact .of_minimal (minimum_ballot_tail ns hf swap left right i k hnonempty)
  · apply proof_tail_shared_minimum ns hf swap swap' left right i k _ hk
    unfold fieldCount at *
    omega

/-- The complete local projection case: every fst/snd of a source-minimum
child has a shared source-minimum representative. All candidate counts and
valid ground representatives are covered without an observation premise. -/
theorem minimum_child_projection_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (f : Unary) (hproj : f = .fst ∨ f = .snd)
    (a : Recipe 3) (hm : MinimalRecipe ns.restricted (frame ns swap left right).value a) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.unary f a) := by
  classical
  by_cases hp : ((frame ns swap left right).eval a).PairValue
  · obtain ⟨x,y,he⟩ := hp
    rcases minimum_pair_observation_form ns swap left right ns.restricted a hm he with
      ⟨u,v,rfl⟩ | ⟨i,k,hk,rfl⟩
    · exact .projection_of_minimum_pair u v hm f hproj
    · rcases hproj with rfl | rfl
      · have hfield : k < (ballotFields ns i (choice swap left right i).value).length := by
          simpa only [ballot_fields_length] using hk
        rcases ballot_field_cases ns i (choice swap left right i).value k hfield with
          ⟨j,rfl,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
        · exact .of_minimal (minimum_ciphertext_selector ns hf swap left right i j)
        · exact .of_minimal (minimum_component_proof_selector ns hf swap left right i j)
        · exact aggregate_selector_shared_minimum ns hf swap swap' left right i
      · simpa only [Term.drop_succ_outer] using
          ballot_tail_shared_minimum ns hf swap swap' left right i (k+1) (by omega)
  · exact .of_minimal (minimum_stuck_projection_of_child ns swap left right f hproj a hm
      (fun x y he => hp ⟨x,y,he⟩))

end ExplainableCrypto.Helios.Symbolic.Historical.General

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- The remaining semantic cases after complete projection transport. -/
def NonprojectionRootCase (φ : Frame restricted n) : Recipe n → Prop
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .pair _ _ | .binary .mul _ _ | .binary .add _ _ | .binary .compose _ _ => True
  | .ternary .penc _ _ _ => True
  | _ => False

def NonprojectionRootTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → NonprojectionRootCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Projection obligations are discharged rather than assumed by the reduced
remaining-root interface. -/
theorem remaining_transport_of_nonprojection (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty)
    (h : Frame.NonprojectionRootTransport (frame ns swap left right) (frame ns swap' left right)) :
    Frame.RemainingRootTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r hp hc hm hcase
  cases r with
  | unary f a =>
    cases f with
    | fst => exact minimum_child_projection_shared ns hf swap swap' left right .fst (Or.inl rfl) a hc
    | snd => exact minimum_child_projection_shared ns hf swap swap' left right .snd (Or.inr rfl) a hc
    | pk => exact False.elim hcase
  | binary f a b => cases f <;> exact h _ hp hc hm hcase
  | ternary f a b c => cases f <;> exact h _ hp hc hm hcase
  | name | var | const | spk => exact h _ hp hc hm hcase

/-- Initial-frame static equivalence now requires only nonprojection local
transport in both directions. Those remaining premises are not asserted here. -/
theorem staticEq_of_nonprojection_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.NonprojectionRootTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.NonprojectionRootTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_remaining_root_transport ns hf left right
    (remaining_transport_of_nonprojection ns hf false true left right hforward)
    (remaining_transport_of_nonprojection ns hf true false left right hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
