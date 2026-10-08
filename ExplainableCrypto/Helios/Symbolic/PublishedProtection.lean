import ExplainableCrypto.Helios.Symbolic.OpaqueComposedNames
import ExplainableCrypto.Helios.Symbolic.TrusteePartialBoundary

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat} {handles n : Nat}

theorem OpaqueProtectedValue.tuple (xs : List (Term V))
    (h : ∀ x ∈ xs, OpaqueProtectedValue restricted x) :
    OpaqueProtectedValue restricted (Term.tuple xs) := by
  induction xs with
  | nil => exact .of_safe rfl
  | cons x xs ih =>
    obtain ⟨u,hu,hs⟩ := h x (by simp)
    obtain ⟨v,hv,ht⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨.binary .pair u v,.binary .pair hu hv,by simp [Term.opaqueSafe,hs,ht]⟩

theorem candidateTuple_opaque_protected (values : Fin (n+1) → Term V)
    (h : ∀ j, OpaqueProtectedValue restricted (values j)) :
    OpaqueProtectedValue restricted (candidateTuple values) := by
  apply OpaqueProtectedValue.tuple
  intro t ht
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
  exact h j

theorem Frame.OpaqueProtected.extend {φ : Frame restricted handles} (hφ : φ.OpaqueProtected)
    {value : Ground} (hv : OpaqueProtectedValue restricted value) : (φ.extend value).OpaqueProtected := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Frame.extend_last] using hv
  · simpa only [Frame.extend_old] using hφ j

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Reuse the checked initial-frame bit representatives. This accepts arbitrary
valid ground syntax, including raw-unsafe but E-equal candidate expressions. -/
theorem initial_frame_opaque_protected (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) : (frame ns swap left right).OpaqueProtected := by
  intro i
  obtain ⟨u,he,hu⟩ := frame_recipe_protected_value ns swap left right (.var i)
    (show (Term.var i).Public ns.restricted from trivial)
  exact ⟨u,he,u.nonce_safe_opaque_safe hu⟩

/-- Every trustee partial is opaque to field extraction. This name-protection
claim requires neither acceptance nor publicness of its arbitrary binding. -/
theorem partial_frame_opaque_protected (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    (partialFrame ns swap left right rs).OpaqueProtected :=
  (initial_frame_opaque_protected ns swap left right).extend
    (candidateTuple_opaque_protected _ (fun _ => OpaqueProtectedValue.of_safe rfl))

/-- Appended tally results equal a public recipe in the protected partial
frame. Public submissions suffice; no acceptance or freshness is assumed. -/
theorem final_frame_opaque_protected (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) :
    (finalFrame ns swap left right rs).OpaqueProtected :=
  (partial_frame_opaque_protected ns swap left right rs).extend
    (((partial_frame_opaque_protected ns swap left right rs).eval (resultRecipe (n := n) rs)
      (resultRecipe_public rs ns.restricted hp)).of_eq (resultRecipe_value ns swap left right rs))

/-- Quantifies over all nested recipes using the newly published partials. -/
theorem partial_frame_name_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (r : Recipe 4) (hr : r.Public ns.restricted) {name : Nat} (hn : name ∈ ns.restricted) :
    ¬ EqE ((partialFrame ns swap left right rs).eval r) (.name name) :=
  (partial_frame_opaque_protected ns swap left right rs).name_not_deducible r hr hn

/-- Actual final publication retains name secrecy for all public recipes.
This does not assert static equivalence or vote secrecy. -/
theorem final_frame_name_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (r : Recipe 5) (hr : r.Public ns.restricted) {name : Nat} (hn : name ∈ ns.restricted) :
    ¬ EqE ((finalFrame ns swap left right rs).eval r) (.name name) :=
  (final_frame_opaque_protected ns swap left right rs hp).name_not_deducible r hr hn

/-- A new constructed key cannot coincide with the old election key even
when its secret recipe uses nested published partials. -/
theorem partial_frame_constructed_key_not_election_key (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (r : Recipe 4) (hr : r.Public ns.restricted) :
    ¬ EqE ((partialFrame ns swap left right rs).eval (.unary .pk r)) (publicKey ns) := by
  intro he
  exact partial_frame_name_not_deducible ns swap left right rs r hr
    (by simp [Names.restricted]) ((EqE.pk_iff _ _).mp he)

/-- A public constructor cannot manufacture an election-secret partial from
new-handle recipes. Such a value must have a borrowed-value origin instead. -/
theorem partial_frame_constructed_partial_not_trustee_partial (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (a b : Recipe 4) (ha : a.Public ns.restricted) (binding : Ground) :
    ¬ EqE ((partialFrame ns swap left right rs).eval (.binary .partialDecrypt a b))
      (.binary .partialDecrypt (.name ns.secretKey) binding) := by
  intro he
  exact partial_frame_name_not_deducible ns swap left right rs a ha
    (by simp [Names.restricted]) ((EqE.partialDecrypt_iff _ _ _ _).mp he).1

end ExplainableCrypto.Helios.Symbolic.Historical.General
