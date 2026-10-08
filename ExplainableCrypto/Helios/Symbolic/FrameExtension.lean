import ExplainableCrypto.Helios.Symbolic.PublishedFrames

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat} {n : Nat} {V W : Type}

theorem Frame.extend_old (φ : Frame restricted handles) (value : Ground) (i : Fin handles) :
    (φ.extend value).value i.castSucc = φ.value i := by simp [Frame.extend]

theorem Frame.extend_last (φ : Frame restricted handles) (value : Ground) :
    (φ.extend value).value (Fin.last handles) = value := by simp [Frame.extend]

theorem Recipe.lift_public (r : Recipe handles) (hr : r.Public restricted) :
    r.lift.Public restricted := Term.Public.subst r _ hr (fun _ => trivial)

/-- Old recipes retain their exact values after extending the handle domain. -/
theorem Frame.eval_extend_lift (φ : Frame restricted handles) (value : Ground) (r : Recipe handles) :
    (φ.extend value).eval r.lift = φ.eval r := by
  simp only [Frame.eval,Recipe.lift,Term.subst_subst,Term.subst,Frame.extend_old]

theorem Frame.StaticEq.of_extend {φ ψ : Frame restricted handles} {a b : Ground}
    (h : (φ.extend a).StaticEq (ψ.extend b)) : φ.StaticEq ψ := by
  intro r s hr hs
  simpa only [Frame.eval_extend_lift] using h r.lift s.lift (r.lift_public hr) (s.lift_public hs)

/-- Appending E-equal values of the same public recipe adds no new equality
observations. The converse retains every old handle, so this is an iff. -/
theorem Frame.StaticEq.extend_public_iff (φ ψ : Frame restricted handles) (a b : Ground)
    (r : Recipe handles) (hr : r.Public restricted) (ha : EqE (φ.eval r) a) (hb : EqE (ψ.eval r) b) :
    (φ.extend a).StaticEq (ψ.extend b) ↔ φ.StaticEq ψ := by
  let ρ : Fin (handles+1) → Recipe handles := Fin.lastCases r Term.var
  have hp : ∀ i, (ρ i).Public restricted := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [ρ,Fin.lastCases_last] using hr
    · simp only [ρ,Fin.lastCases_castSucc,Term.Public]
  have hφ : (φ.derive ρ).StaticEq (φ.extend a) := by
    apply Frame.staticEq_of_pointwise
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Frame.derive,ρ,Fin.lastCases_last,Frame.extend_last] using ha
    · simp only [Frame.derive,ρ,Fin.lastCases_castSucc,Frame.extend_old,Frame.eval,Term.subst]
      exact .refl _
  have hψ : (ψ.derive ρ).StaticEq (ψ.extend b) := by
    apply Frame.staticEq_of_pointwise
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Frame.derive,ρ,Fin.lastCases_last,Frame.extend_last] using hb
    · simp only [Frame.derive,ρ,Fin.lastCases_castSucc,Frame.extend_old,Frame.eval,Term.subst]
      exact .refl _
  exact ⟨fun h => h.of_extend,fun h => hφ.symm.trans ((h.derive ρ hp).trans hψ)⟩

theorem candidateTuple_subst (values : Fin (n+1) → Term V) (σ : V → Term W) :
    (candidateTuple values).subst σ = candidateTuple (fun j => (values j).subst σ) := by
  simp only [candidateTuple,Term.subst_tuple,List.map_map]
  rfl

theorem candidateTuple_public (values : Fin (n+1) → Term V)
    (h : ∀ j, (values j).Public restricted) : (candidateTuple values).Public restricted := by
  apply Term.Public.tuple
  intro t ht
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
  exact h j

/-- Every candidate, including the last one, has its specified tuple slot. -/
theorem candidateTuple_project (values : Fin (n+1) → Term V) (j : Fin (n+1)) :
    EqE ((candidateTuple values).project j.val) (values j) := by
  have h := project_tuple_get ((List.finRange (n+1)).map values) j.val (by simp)
  simpa only [candidateTuple,List.getElem_map,List.getElem_finRange,Fin.cast_mk,Fin.eta] using h

theorem EqE.candidateTuple (values values' : Fin (n+1) → Term V)
    (h : ∀ j, EqE (values j) (values' j)) : EqE (candidateTuple values) (candidateTuple values') := by
  have hs (xs : List (Fin (n+1))) : EqE (Term.tuple (xs.map values)) (Term.tuple (xs.map values')) := by
    induction xs with
    | nil => exact .refl _
    | cons j xs ih => exact .binary .pair (h j) ih
  exact hs _

end ExplainableCrypto.Helios.Symbolic
