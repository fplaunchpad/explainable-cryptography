import ExplainableCrypto.Helios.Symbolic.GroupedCiphertextEquality
import ExplainableCrypto.Helios.Symbolic.PublicReconstruction

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- An induction hypothesis on the total syntax size of a public equality test.
This is an explicit premise, not an assumed static-equivalence theorem. -/
def ObservationsBelow (φ ψ : Frame restricted handles) (bound : Nat) : Prop :=
  ∀ r s : Recipe handles, r.Public restricted → s.Public restricted →
    r.nodeCount + s.nodeCount < bound → (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s))

theorem ObservationsBelow.mono {φ ψ : Frame restricted handles} {a b : Nat}
    (h : ObservationsBelow φ ψ b) (hab : a ≤ b) : ObservationsBelow φ ψ a := by
  intro r s hr hs hsize
  exact h r s hr hs (by omega)

theorem ObservationsBelow.symm {φ ψ : Frame restricted handles} {bound : Nat}
    (h : ObservationsBelow φ ψ bound) : ObservationsBelow ψ φ bound :=
  fun r s hr hs hsize => (h r s hr hs hsize).symm

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

namespace CiphertextAssembly

/-- Coherence compares the two child key recipes at each multiplication node.
These key recipes belong to disjoint subtrees, which supplies the size bound. -/
def Coherent (φ : Frame restricted 3) : CiphertextAssembly n → Prop
  | .constructed _ _ _ | .honest _ => True
  | .mul a b => a.Coherent φ ∧ b.Coherent φ ∧ EqE (φ.eval a.keyRecipe) (φ.eval b.keyRecipe)

theorem key_agreement_congr (ns : Names n) (φ : Frame restricted 3) (t : CiphertextAssembly n)
    {k l : Ground} (hk : t.KeyAgreement ns φ k) (he : EqE k l) : t.KeyAgreement ns φ l := by
  induction t with
  | constructed => exact hk.trans he
  | honest => exact hk.trans he
  | mul a b ia ib => exact ⟨ia hk.1, ib hk.2⟩

theorem coherent_of_key_agreement (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n) (k : Ground)
    (hk : t.KeyAgreement ns (frame ns swap left right) k) : t.Coherent (frame ns swap left right) := by
  induction t with
  | constructed => trivial
  | honest => trivial
  | mul a b ia ib =>
    exact ⟨ia hk.1, ib hk.2, (a.keyRecipe_value ns swap left right k hk.1).trans
      (b.keyRecipe_value ns swap left right k hk.2).symm⟩

theorem key_agreement_of_coherent (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hc : t.Coherent (frame ns swap left right)) :
    t.KeyAgreement ns (frame ns swap left right) ((frame ns swap left right).eval t.keyRecipe) := by
  induction t with
  | constructed => exact .refl _
  | honest => exact .refl _
  | mul a b ia ib =>
    exact ⟨ia hc.1, b.key_agreement_congr ns _ (ib hc.2.1) hc.2.2.symm⟩

/-- Coherence is exactly the existence of a ciphertext value for the assembly.
The target components need not be normal and keys may agree only under E. -/
theorem coherent_iff_ciphertext_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n) :
    t.Coherent (frame ns swap left right) ↔
      ∃ k r p : Ground, EqE ((frame ns swap left right).eval t.recipe) (.ternary .penc k r p) := by
  constructor
  · intro hc
    exact ⟨_, _, _, t.grouped_value ns swap left right _ (t.key_agreement_of_coherent ns swap left right hc)⟩
  · rintro ⟨k, r, p, he⟩
    exact t.coherent_of_key_agreement ns swap left right k (t.key_agreement_of_value ns swap left right he)

/-- Every coherence comparison is smaller than the entire original assembly.
No pointwise agreement of the key values across frames is required. -/
theorem coherent_transfer (φ ψ : Frame restricted 3) (t : CiphertextAssembly n)
    (hp : t.recipe.Public restricted) (hobs : φ.ObservationsBelow ψ t.recipe.nodeCount) :
    t.Coherent φ ↔ t.Coherent ψ := by
  induction t with
  | constructed => exact Iff.rfl
  | honest => exact Iff.rfl
  | mul a b ia ib =>
    have hab : a.recipe.nodeCount ≤ (CiphertextAssembly.mul a b).recipe.nodeCount := by
      simp only [recipe, Term.nodeCount]; omega
    have hbb : b.recipe.nodeCount ≤ (CiphertextAssembly.mul a b).recipe.nodeCount := by
      simp only [recipe, Term.nodeCount]; omega
    have hkeys := hobs a.keyRecipe b.keyRecipe (a.keyRecipe_public hp.1) (b.keyRecipe_public hp.2) (by
      have ha := a.keyRecipe_smaller
      have hb := b.keyRecipe_smaller
      simp only [recipe, Term.nodeCount]
      omega)
    exact and_congr (ia hp.1 (hobs.mono hab)) (and_congr (ib hp.2 (hobs.mono hbb)) hkeys)

end CiphertextAssembly

namespace CiphertextGroup
variable {handles : Nat}

theorem Public.of_subset {small large : Finset Nat} {g : CiphertextGroup n handles}
    (h : g.Public large) (hs : small ⊆ large) : g.Public small := by
  cases g with
  | constructed r p => exact ⟨h.1.of_subset hs, h.2.of_subset hs⟩
  | honest => trivial
  | mixed r p a => exact ⟨h.1.of_subset hs, h.2.of_subset hs⟩

/-- Exact grouped observations transfer using only comparisons strictly below
the sum of the two original recipe sizes. -/
theorem observation_transfer (φ ψ : Frame restricted handles) (a b : CiphertextGroup n handles)
    (ha : a.Public restricted) (hb : b.Public restricted) {sa sb : Nat}
    (hsa : a.budget ≤ sa) (hsb : b.budget ≤ sb) (hobs : φ.ObservationsBelow ψ (sa + sb)) :
    a.Observation φ b ↔ a.Observation ψ b := by
  cases a with
  | constructed r p =>
    cases b with
    | constructed s q =>
      have hn := hobs r s ha.1 hb.1 (by simp only [budget] at hsa hsb; omega)
      have hm := hobs p q ha.2 hb.2 (by simp only [budget] at hsa hsb; omega)
      exact and_congr hn hm
    | honest => exact Iff.rfl
    | mixed => exact Iff.rfl
  | honest a => cases b <;> exact Iff.rfl
  | mixed r p a =>
    cases b with
    | constructed => exact Iff.rfl
    | honest => exact Iff.rfl
    | mixed s q b =>
      have hn := hobs r s ha.1 hb.1 (by simp only [budget] at hsa hsb; omega)
      have hp : (Term.binary .add p (.const .zero)).Public restricted := ⟨ha.2, trivial⟩
      have hq : (Term.binary .add q (.const .zero)).Public restricted := ⟨hb.2, trivial⟩
      have hm := hobs _ _ hp hq (by simp only [budget] at hsa hsb; simp only [Term.nodeCount]; omega)
      exact and_congr Iff.rfl (and_congr hn hm)

end CiphertextGroup

namespace CiphertextAssembly

/-- The complete ciphertext comparison step for arbitrary coherent assemblies.
Smaller equality observations imply key-coherence transfer as well as grouped
component transfer. Minimum syntax is never assumed to persist across worlds. -/
theorem equality_swap_of_smaller (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextAssembly n)
    (ha : a.recipe.Public ns.restricted) (hb : b.recipe.Public ns.restricted)
    (hca : a.Coherent (frame ns false left right)) (hcb : b.Coherent (frame ns false left right))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (a.recipe.nodeCount + b.recipe.nodeCount)) :
    EqE ((frame ns false left right).eval a.recipe) ((frame ns false left right).eval b.recipe) ↔
      EqE ((frame ns true left right).eval a.recipe) ((frame ns true left right).eval b.recipe) := by
  have hca' := (a.coherent_transfer _ _ ha (hobs.mono (by omega))).mp hca
  have hcb' := (b.coherent_transfer _ _ hb (hobs.mono (by omega))).mp hcb
  have hpolicy : ns.nonceNames ⊆ ns.restricted := fun _ h => Finset.mem_union_right _ h
  have hga := a.group_public ha
  have hgb := b.group_public hb
  have reduce (swap : Bool) (h₁ : a.Coherent (frame ns swap left right))
      (h₂ : b.Coherent (frame ns swap left right)) :
      EqE ((frame ns swap left right).eval a.recipe) ((frame ns swap left right).eval b.recipe) ↔
        EqE ((frame ns swap left right).eval a.keyRecipe) ((frame ns swap left right).eval b.keyRecipe) ∧
          a.group.Observation (frame ns swap left right) b.group := by
    have hv₁ := a.grouped_value ns swap left right _ (a.key_agreement_of_coherent ns swap left right h₁)
    have hv₂ := b.grouped_value ns swap left right _ (b.key_agreement_of_coherent ns swap left right h₂)
    have hc := CiphertextGroup.ciphertext_eq_iff ns hf swap left right a.group b.group
      (hga.of_subset hpolicy) (hgb.of_subset hpolicy)
      ((frame ns swap left right).eval a.keyRecipe) ((frame ns swap left right).eval b.keyRecipe)
    exact ⟨fun he => hc.mp (hv₁.symm.trans (he.trans hv₂)),
      fun he => hv₁.trans ((hc.mpr he).trans hv₂.symm)⟩
  have hk := hobs a.keyRecipe b.keyRecipe (a.keyRecipe_public ha) (b.keyRecipe_public hb) (by
    have h₁ := a.keyRecipe_smaller
    have h₂ := b.keyRecipe_smaller
    omega)
  have hg := CiphertextGroup.observation_transfer _ _ a.group b.group hga hgb
    a.group_budget b.group_budget hobs
  exact (reduce false hca hcb).trans ((and_congr hk hg).trans (reduce true hca' hcb').symm)

end CiphertextAssembly

/-- The ciphertext branch for actual minimum public recipes has no assumed
assembly or coherence certificate. Both supplied values are in the first world;
coherence and comparison transfer follow from smaller public observations. -/
theorem minimum_ciphertext_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {k u p l v q : Ground}
    (her : EqE ((frame ns false left right).eval r) (.ternary .penc k u p))
    (hes : EqE ((frame ns false left right).eval s) (.ternary .penc l v q))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨a, rfl⟩ := assembly_of_ciphertext_syntax ns false left right
    (minimum_ciphertext_syntax ns false left right ns.restricted r hr her) her
  obtain ⟨b, rfl⟩ := assembly_of_ciphertext_syntax ns false left right
    (minimum_ciphertext_syntax ns false left right ns.restricted s hs hes) hes
  exact a.equality_swap_of_smaller ns hf left right b hr.isPublic hs.isPublic
    ((a.coherent_iff_ciphertext_value ns false left right).mpr ⟨k, u, p, her⟩)
    ((b.coherent_iff_ciphertext_value ns false left right).mpr ⟨l, v, q, hes⟩) hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
