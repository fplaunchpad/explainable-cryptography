import ExplainableCrypto.Helios.Symbolic.SourceFixedLabelNames

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Move one newly forbidden literal to a fresh literal while keeping the old
policy admissible. The fresh literal is absent from the original recipe. -/
theorem Term.Public.swap_unused_policy {r : Term V} (hr : r.Public restricted)
    (n k : Nat) (hk : k ∉ insert n restricted)
    (hkr : k ∉ r.nameSupport) :
    (r.mapNames (Equiv.swap n k)).Public (insert n restricted) := by
  classical
  apply (Term.public_iff_nameSupport _ _).mpr
  intro v hv hp
  rw [Term.nameSupport_mapNames] at hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  by_cases hun : u=n
  · subst u
    exact hk (by simpa only [Equiv.swap_apply_left] using hp)
  · have huk : u ≠ k := fun h => hkr (h ▸ hu)
    rw [Equiv.swap_apply_of_ne_of_ne hun huk] at hp
    rcases Finset.mem_insert.mp hp with he | he
    · exact hun he
    · exact (Term.public_iff_nameSupport r restricted).mp hr u hu he

namespace Frame
/-- Change the allowed-literal policy index while retaining every full handle
value. Semantic preservation requires the separate unused-name lemmas. -/
def withPolicy (φ : Frame restricted handles) (policy : Finset Nat) : Frame policy handles := ⟨φ.value⟩

def nameSupport (φ : Frame restricted handles) : Finset Nat :=
  Finset.univ.biUnion (fun i => (φ.value i).nameSupport)

theorem mem_nameSupport (φ : Frame restricted handles) (n : Nat) :
    n ∈ φ.nameSupport ↔ ∃ i, n ∈ (φ.value i).nameSupport := by simp [nameSupport]

theorem withPolicy_nameSupport (φ : Frame restricted handles) (policy : Finset Nat) :
    (φ.withPolicy policy).nameSupport = φ.nameSupport := rfl

theorem StaticEq.withPolicy {φ ψ : Frame restricted handles} (h : φ.StaticEq ψ)
    (policy : Finset Nat) (hp : restricted ⊆ policy) :
    (φ.withPolicy policy).StaticEq (ψ.withPolicy policy) :=
  fun r s hr hs => h r s (hr.of_subset hp) (hs.of_subset hp)

theorem eval_mapNames_of_fixed (φ : Frame restricted handles) (r : Recipe handles)
    (f : Nat → Nat) (hf : ∀ n ∈ φ.nameSupport, f n=n) :
    φ.eval (r.mapNames f) = (φ.eval r).mapNames f := by
  have hv (i : Fin handles) : (φ.value i).mapNames f = φ.value i :=
    (φ.value i).mapNames_eq_of_fixed f (fun n hn => hf n ((mem_nameSupport φ n).mpr ⟨i,hn⟩))
  simp only [eval,Term.mapNames_subst,hv]

/-- An unused forbidden literal removes no distinguishing power: any test
mentioning it can instead use a fresh name, fixing both complete frames. -/
theorem staticEq_insert_unused_iff (φ ψ : Frame restricted handles) (n : Nat)
    (hφ : n ∉ φ.nameSupport) (hψ : n ∉ ψ.nameSupport) :
    (φ.withPolicy (insert n restricted)).StaticEq (ψ.withPolicy (insert n restricted)) ↔ φ.StaticEq ψ := by
  classical
  constructor
  · intro h r s hr hs
    let avoid := insert n (restricted ∪ (φ.nameSupport ∪ (ψ.nameSupport ∪ (r.nameSupport ∪ s.nameSupport))))
    let k := avoid.sup id + 1
    have hk : k ∉ avoid := by
      intro hm
      have hl := Finset.le_sup (f := id) hm
      change avoid.sup id + 1 ≤ avoid.sup id at hl
      omega
    have hkn : k ∉ insert n restricted := fun hm => hk (by
      rcases Finset.mem_insert.mp hm with he | hm
      · exact Finset.mem_insert.mpr (.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hm))
    have hkp : k ∉ φ.nameSupport := fun hm => hk (by simp only [avoid]; simp [hm])
    have hkq : k ∉ ψ.nameSupport := fun hm => hk (by simp only [avoid]; simp [hm])
    have hkr : k ∉ r.nameSupport := fun hm => hk (by simp only [avoid]; simp [hm])
    have hks : k ∉ s.nameSupport := fun hm => hk (by simp only [avoid]; simp [hm])
    have fixφ : ∀ u ∈ φ.nameSupport, Equiv.swap n k u = u := fun u hu =>
      Equiv.swap_apply_of_ne_of_ne (fun he => hφ (he ▸ hu)) (fun he => hkp (he ▸ hu))
    have fixψ : ∀ u ∈ ψ.nameSupport, Equiv.swap n k u = u := fun u hu =>
      Equiv.swap_apply_of_ne_of_ne (fun he => hψ (he ▸ hu)) (fun he => hkq (he ▸ hu))
    have ht := h (r.mapNames (Equiv.swap n k)) (s.mapNames (Equiv.swap n k))
      (hr.swap_unused_policy n k hkn hkr) (hs.swap_unused_policy n k hkn hks)
    change (EqE (φ.eval _) (φ.eval _) ↔ EqE (ψ.eval _) (ψ.eval _)) at ht
    simpa only [eval_mapNames_of_fixed φ _ _ fixφ,eval_mapNames_of_fixed ψ _ _ fixψ,EqE.mapNames_iff] using ht
  · exact fun h => h.withPolicy _ (Finset.subset_insert _ _)

/-- Finite padding may repeat old restricted names. Only newly forbidden
names must be absent from both complete frame supports. -/
theorem staticEq_union_unused_iff (φ ψ : Frame restricted handles) (extra : Finset Nat)
    (hφ : ∀ n ∈ extra, n ∉ restricted → n ∉ φ.nameSupport)
    (hψ : ∀ n ∈ extra, n ∉ restricted → n ∉ ψ.nameSupport) :
    (φ.withPolicy (restricted ∪ extra)).StaticEq (ψ.withPolicy (restricted ∪ extra)) ↔ φ.StaticEq ψ := by
  classical
  induction extra using Finset.induction_on with
  | empty => simp only [StaticEq,withPolicy,eval,Finset.union_empty]
  | @insert n extra hn ih =>
    have hi := ih (fun u hu => hφ u (Finset.mem_insert_of_mem hu))
      (fun u hu => hψ u (Finset.mem_insert_of_mem hu))
    by_cases hnr : n ∈ restricted
    · simpa only [StaticEq,withPolicy,eval,Finset.union_insert,Finset.insert_eq_of_mem (Finset.mem_union_left extra hnr)] using hi
    · have hs := staticEq_insert_unused_iff (φ.withPolicy (restricted ∪ extra))
        (ψ.withPolicy (restricted ∪ extra)) n
        (hφ n (Finset.mem_insert_self _ _) hnr) (hψ n (Finset.mem_insert_self _ _) hnr)
      simpa only [StaticEq,withPolicy,eval,Finset.union_insert] using hs.trans hi

end Frame
end ExplainableCrypto.Helios.Symbolic
