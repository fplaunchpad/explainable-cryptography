import ExplainableCrypto.Helios.Symbolic.PublicReconstruction

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat}

/-- The aggregate expression is public whenever its ballot recipe is public. -/
theorem aggregateCiphertext_public {ballot : Term V} (hb : ballot.Public restricted) (n : Nat) :
    (aggregateCiphertext n ballot).Public restricted := by
  unfold aggregateCiphertext
  have fold (xs : List (Fin n)) (acc : Term V) (ha : acc.Public restricted) :
      (xs.foldl (fun a i => .binary .mul a (ballot.project (i.val + 1))) acc).Public restricted := by
    induction xs generalizing acc with
    | nil => exact ha
    | cons i xs ih => exact ih _ ⟨ha, hb.project _⟩
  exact fold _ _ (hb.project 0)

/-- Board aggregation is the same public expression before and after evaluation. -/
theorem aggregateCiphertext_subst (n : Nat) (ballot : Term V) (σ : V → Term W) :
    (aggregateCiphertext n ballot).subst σ = aggregateCiphertext n (ballot.subst σ) := by
  simpa only [Historical.foldCandidates, aggregateCiphertext, Term.subst_project, Fin.val_succ, Fin.val_zero] using
    Historical.foldCandidates_subst σ .mul (fun j : Fin (n + 1) => ballot.project j.val)

namespace Frame.StaticEq
variable {m : Nat} {φ ψ : Frame restricted m}

theorem proofValid_iff (h : φ.StaticEq ψ) (n : Nat) (key ballot : Recipe m)
    (hk : key.Public restricted) (hb : ballot.Public restricted) :
    ProofValid n (φ.eval key) (φ.eval ballot) ↔ ProofValid n (ψ.eval key) (ψ.eval ballot) := by
  have hag := h (.ternary .checkspk key (aggregateCiphertext n ballot)
    (ballot.project (2 * (n + 1)))) (.const .ok) ⟨hk, aggregateCiphertext_public hb n, hb.project _⟩ trivial
  have hc (j : Fin (n + 1)) := h (.ternary .checkspk key (ballot.project j.val)
    (ballot.project (n + 1 + j.val))) (.const .ok) ⟨hk, hb.project _, hb.project _⟩ trivial
  simp only [Frame.eval, Term.subst, aggregateCiphertext_subst, Term.subst_project] at hag hc
  exact ⟨fun hv => ⟨hag.mp hv.1, fun j => (hc j).mp (hv.2 j)⟩,
    fun hv => ⟨hag.mpr hv.1, fun j => (hc j).mpr (hv.2 j)⟩⟩

theorem tailGuard_iff (h : φ.StaticEq ψ) (n : Nat) (ballot : Recipe m)
    (hb : ballot.Public restricted) : TailGuard n (φ.eval ballot) ↔ TailGuard n (ψ.eval ballot) := by
  have he := h (ballot.drop (fieldCount n)) (.const .bottom) (hb.drop _) trivial
  simpa only [TailGuard, Frame.eval, Term.subst_drop, Term.subst] using he

/-- Weeding compares public recipes for actual board entries in the two worlds. -/
theorem noReuse_iff (h : φ.StaticEq ψ) (n : Nat) (board : List (Recipe m)) (ballot : Recipe m)
    (hboard : ∀ r ∈ board, r.Public restricted) (hb : ballot.Public restricted) :
    NoReuse n (board.map φ.eval) (φ.eval ballot) ↔ NoReuse n (board.map ψ.eval) (ψ.eval ballot) := by
  have forward {φ ψ : Frame restricted m} (h : φ.StaticEq ψ)
      (hn : NoReuse n (board.map φ.eval) (φ.eval ballot)) :
      NoReuse n (board.map ψ.eval) (ψ.eval ballot) := by
    intro earlier hm i j he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    have hh := h (r.project i.val) (ballot.project j.val) ((hboard r hr).project _) (hb.project _)
    simp only [Frame.eval, Term.subst_project] at hh
    exact hn (φ.eval r) (List.mem_map.mpr ⟨r, hr, rfl⟩) i j (hh.mpr he)
  exact ⟨forward h, forward h.symm⟩

/-- All corrected acceptance conditions are public equality tests. The same
public board recipes must be interpreted in each world. -/
theorem accepted_iff (h : φ.StaticEq ψ) (n : Nat) (key ballot : Recipe m) (board : List (Recipe m))
    (hk : key.Public restricted) (hb : ballot.Public restricted)
    (hboard : ∀ r ∈ board, r.Public restricted) :
    Accepted n (φ.eval key) (board.map φ.eval) (φ.eval ballot) ↔
      Accepted n (ψ.eval key) (board.map ψ.eval) (ψ.eval ballot) :=
  and_congr (h.proofValid_iff n key ballot hk hb)
    (and_congr (h.tailGuard_iff n ballot hb) (h.noReuse_iff n board ballot hboard hb))

end Frame.StaticEq
end ExplainableCrypto.Helios.Symbolic
