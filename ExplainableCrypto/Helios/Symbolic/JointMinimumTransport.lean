import ExplainableCrypto.Helios.Symbolic.BoundedSharedMinima

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- Both directions of strictly smaller shared minima are available at each
local root. These are simultaneous induction hypotheses, not static equivalence. -/
def JointLocalMinimumTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    SharedMinimaBelow φ ψ r.nodeCount → SharedMinimaBelow ψ φ r.nodeCount →
    SharedMinimum φ ψ r

/-- Simultaneous strong induction minimizes children in the current source.
The rebuilt parent's size cannot exceed the original, so both strict smaller
hypotheses remain available after child replacement. -/
theorem common_minima_of_joint_local
    (hforward : JointLocalMinimumTransport φ ψ) (hreverse : JointLocalMinimumTransport ψ φ) :
    CommonMinima φ ψ ∧ CommonMinima ψ φ := by
  have all : ∀ r : Recipe n, ∀ swap : Bool, r.Public restricted →
      SharedMinimum (if swap then ψ else φ) (if swap then φ else ψ) r := by
    intro r
    induction r using (measure Term.nodeCount).wf.induction with
    | h r ih =>
      intro swap hp
      have localStep : JointLocalMinimumTransport (if swap then ψ else φ) (if swap then φ else ψ) := by
        cases swap
        · exact hforward
        · exact hreverse
      have finish (s : Recipe n) (hs : s.Public restricted) (hc : MinimumChildren (if swap then ψ else φ) s)
          (hle : s.nodeCount ≤ r.nodeCount) (he : EqE ((if swap then ψ else φ).eval r) ((if swap then ψ else φ).eval s))
          (he' : EqE ((if swap then φ else ψ).eval r) ((if swap then φ else ψ).eval s)) : SharedMinimum (if swap then ψ else φ) (if swap then φ else ψ) r := by
        apply SharedMinimum.of_shared_equivalent (localStep s hs hc ?_ ?_) he he'
        · intro t ht hlt
          exact ih t (Nat.lt_of_lt_of_le hlt hle) swap ht
        · intro t ht hlt
          cases swap
          · exact ih t (Nat.lt_of_lt_of_le hlt hle) true ht
          · exact ih t (Nat.lt_of_lt_of_le hlt hle) false ht
      cases r with
      | name a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
      | var a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
      | const a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
      | unary f a =>
        obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount; omega) swap hp
        have hla := ha.least a hp he.symm
        exact finish (.unary f a') ha.isPublic ha (by simp only [Term.nodeCount]; omega)
          (.unary f he) (.unary f he')
      | binary f a b =>
        obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount; omega) swap hp.1
        obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount; omega) swap hp.2
        have hla := ha.least a hp.1 he.symm
        have hlb := hb.least b hp.2 hf.symm
        exact finish (.binary f a' b') ⟨ha.isPublic,hb.isPublic⟩ ⟨ha,hb⟩
          (by simp only [Term.nodeCount]; omega) (.binary f he hf) (.binary f he' hf')
      | ternary f a b c =>
        obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) swap hp.1
        obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) swap hp.2.1
        obtain ⟨c',hc,hg,hg'⟩ := ih c (by change c.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) swap hp.2.2
        have hla := ha.least a hp.1 he.symm
        have hlb := hb.least b hp.2.1 hf.symm
        have hlc := hc.least c hp.2.2 hg.symm
        exact finish (.ternary f a' b' c') ⟨ha.isPublic,hb.isPublic,hc.isPublic⟩ ⟨ha,hb,hc⟩
          (by simp only [Term.nodeCount]; omega) (.ternary f he hf hg) (.ternary f he' hf' hg')
      | spk a b c d =>
        obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) swap hp.1
        obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) swap hp.2.1
        obtain ⟨c',hc,hg,hg'⟩ := ih c (by change c.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) swap hp.2.2.1
        obtain ⟨d',hd,hh,hh'⟩ := ih d (by change d.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) swap hp.2.2.2
        have hla := ha.least a hp.1 he.symm
        have hlb := hb.least b hp.2.1 hf.symm
        have hlc := hc.least c hp.2.2.1 hg.symm
        have hld := hd.least d hp.2.2.2 hh.symm
        exact finish (.spk a' b' c' d') ⟨ha.isPublic,hb.isPublic,hc.isPublic,hd.isPublic⟩ ⟨ha,hb,hc,hd⟩
          (by simp only [Term.nodeCount]; omega) (.spk he hf hg hh) (.spk he' hf' hg' hh')
  exact ⟨fun r hp => all r false hp,fun r hp => all r true hp⟩

end ExplainableCrypto.Helios.Symbolic.Frame
