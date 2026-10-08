import ExplainableCrypto.Helios.Symbolic.MinimumParentClosure

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat}

/-- Cases remaining after initial historical minimum-parent closure. Destructor
cases retain actual semantic success, including delayed and modulo-E0 matches. -/
def RootTransportCase (φ : Frame restricted n) : Recipe n → Prop
  | .unary .fst a | .unary .snd a => (φ.eval a).PairValue
  | .binary .dec a b => ∃ m, DecryptionMatch (φ.eval a) (φ.eval b) m
  | .ternary .checkspk a b c => ProofCheckMatch (φ.eval a) (φ.eval b) (φ.eval c)
  | .binary .pair _ _ | .binary .mul _ _ | .binary .add _ _ | .binary .compose _ _ => True
  | .ternary .penc _ _ _ => True
  | _ => False

/-- Only nonminimum roots with minimum children need a new shared witness. -/
def RemainingRootTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    ¬ MinimalRecipe restricted φ.value r → RootTransportCase φ r → SharedMinimum φ ψ r

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Outside the explicit root cases, minimum children force a minimum root.
This classification holds for the actual initial frame in either assignment. -/
theorem minimum_outside_root_cases (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hp : r.Public ns.restricted) (hc : Frame.MinimumChildren (frame ns swap left right) r)
    (hn : ¬ Frame.RootTransportCase (frame ns swap left right) r) :
    MinimalRecipe ns.restricted (frame ns swap left right).value r := by
  cases r with
  | name a => exact .of_nodeCount_one hp rfl
  | var v => exact .of_nodeCount_one hp rfl
  | const c => exact .of_nodeCount_one hp rfl
  | unary f a =>
    cases f with
    | pk => exact minimum_pk_of_child ns swap left right a hc
    | fst =>
      exact minimum_stuck_projection_of_child ns swap left right .fst (Or.inl rfl) a hc
        (fun x y he => hn ⟨x,y,he⟩)
    | snd =>
      exact minimum_stuck_projection_of_child ns swap left right .snd (Or.inr rfl) a hc
        (fun x y he => hn ⟨x,y,he⟩)
  | binary f a b =>
    cases f with
    | partialDecrypt => exact minimum_partial_of_children ns swap left right a b hc.1 hc.2
    | dec =>
      exact minimum_stuck_decryption_of_children ns swap left right a b hc.1 hc.2
        (fun m hm => hn ⟨m,hm⟩)
    | pair | mul | add | compose => exact False.elim (hn trivial)
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (hn trivial)
    | checkspk => exact minimum_stuck_check_of_children ns swap left right a b c hc.1 hc.2.1 hc.2.2 hn
  | spk a b c d => exact minimum_spk_of_children ns swap left right a b c d hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- Every solved root is its own shared witness in any destination. The remaining
premise covers only nonminimum roots with minimum children in the listed cases. -/
theorem local_transport_of_remaining_roots (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (ψ : Frame ns.restricted 3)
    (h : Frame.RemainingRootTransport (frame ns swap left right) ψ) :
    Frame.LocalMinimumTransport (frame ns swap left right) ψ := by
  classical
  intro r hp hc
  by_cases hm : MinimalRecipe ns.restricted (frame ns swap left right).value r
  · exact .of_minimal hm
  · apply h r hp hc hm
    by_contra hn
    exact hm (minimum_outside_root_cases ns swap left right r hp hc hn)

/-- The fresh historical privacy goal now needs transport only for the remaining
nonminimum roots in both orientations. Neither premise is silently discharged. -/
theorem staticEq_of_remaining_root_transport (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.RemainingRootTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.RemainingRootTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_local_transport_both ns hf left right
    (local_transport_of_remaining_roots ns false left right _ hforward)
    (local_transport_of_remaining_roots ns true left right _ hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
