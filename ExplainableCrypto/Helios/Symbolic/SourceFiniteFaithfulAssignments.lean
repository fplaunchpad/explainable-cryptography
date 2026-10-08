import ExplainableCrypto.Helios.Symbolic.SourceNamedElectionVisible
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Preimage

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

/-- Injectivity on a finite set of used names, with the source sorts retained.
Equal numerals in different sorts do not constitute a collision. -/
def NameAssignment.FaithfulOn (ρ : NameAssignment) (s : Finset SourceName) : Prop :=
  ∀ ⦃a b⦄, a ∈ s → b ∈ s → a.map ρ.base ρ.channel = b.map ρ.base ρ.channel → a = b

theorem NameAssignment.FaithfulOn.mono {ρ : NameAssignment} {s t : Finset SourceName}
    (h : ρ.FaithfulOn s) (ht : t ⊆ s) : ρ.FaithfulOn t :=
  fun _ _ ha hb he => h (ht ha) (ht hb) he

/-- Mathlib extends the two finite injections to permutations. Values outside
the specified support may change in the extensions. -/
theorem NameAssignment.FaithfulOn.exists_permutations {ρ : NameAssignment} {s : Finset SourceName}
    (h : ρ.FaithfulOn s) :
    ∃ e k : Nat ≃ Nat,
      (∀ n, SourceName.base n ∈ s → e n = ρ.base n) ∧
      (∀ c, SourceName.channel c ∈ s → k c = ρ.channel c) := by
  classical
  let bs := s.preimage SourceName.base (fun _ _ _ _ he => SourceName.base.inj he)
  let cs := s.preimage SourceName.channel (fun _ _ _ _ he => SourceName.channel.inj he)
  have hb (x y : bs) (he : ρ.base x.val = ρ.base y.val) : x = y := by
    apply Subtype.ext
    exact SourceName.base.inj (h (Finset.mem_preimage.mp x.property)
      (Finset.mem_preimage.mp y.property) (congrArg SourceName.base he))
  have hc (x y : cs) (he : ρ.channel x.val = ρ.channel y.val) : x = y := by
    apply Subtype.ext
    exact SourceName.channel.inj (h (Finset.mem_preimage.mp x.property)
      (Finset.mem_preimage.mp y.property) (congrArg SourceName.channel he))
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun x : bs => x.val)
    (fun x : bs => ρ.base x.val) Subtype.val_injective hb
  obtain ⟨k,hk⟩ := Equiv.Perm.exists_extending_pair (fun x : cs => x.val)
    (fun x : cs => ρ.channel x.val) Subtype.val_injective hc
  exact ⟨e,k,fun n hn => he ⟨n,Finset.mem_preimage.mpr hn⟩,
    fun c hc => hk ⟨c,Finset.mem_preimage.mpr hc⟩⟩

theorem Extended.mapAssignments_eq_permutations (a : Extended V) (ρ : NameAssignment)
    (e k : Nat ≃ Nat)
    (hb : ∀ n, SourceName.base n ∈ a.nameSupport → e n = ρ.base n)
    (hc : ∀ c, SourceName.channel c ∈ a.nameSupport → k c = ρ.channel c) :
    a.mapNames ρ.base ρ.channel = a.mapNames e k := by
  apply a.mapAssignments_congr ρ (fun n => match n with | .base n => e n | .channel c => k c)
  intro n hn
  cases n with
  | base n => exact (hb n hn).symm
  | channel c => exact (hc c hn).symm

/-- Finite endpoint support suffices even when the derivation uses additional
names internally: genuine permutations transport the entire derivation. -/
theorem Extended.reduction_mapAssignments_iff (a b : Extended V) (ρ : NameAssignment)
    (hf : ρ.FaithfulOn (a.nameSupport ∪ b.nameSupport)) :
    Extended.Reduction (a.mapNames ρ.base ρ.channel) (b.mapNames ρ.base ρ.channel) ↔
      Extended.Reduction a b := by
  obtain ⟨e,k,hbase,hchannel⟩ := hf.exists_permutations
  have ha := a.mapAssignments_eq_permutations ρ e k
    (fun n hn => hbase n (Finset.mem_union_left _ hn))
    (fun n hn => hchannel n (Finset.mem_union_left _ hn))
  have hb := b.mapAssignments_eq_permutations ρ e k
    (fun n hn => hbase n (Finset.mem_union_right _ hn))
    (fun n hn => hchannel n (Finset.mem_union_right _ hn))
  rw [ha,hb]
  exact Extended.Reduction.mapNames_iff a b e k

theorem Extended.Reduction.interprets_faithful {a b : Extended V} (h : Reduction a b)
    (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (hf : ρ.FaithfulOn (a.nameSupport ∪ b.nameSupport))
    (ha : (a.mapNames ρ.base ρ.channel).Realizes env p) :
    ∃ q, Agent.Tau p q ∧ (b.mapNames ρ.base ρ.channel).Realizes env q :=
  ((reduction_mapAssignments_iff a b ρ hf).mpr h).realizes env ha

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
