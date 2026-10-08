import ExplainableCrypto.Helios.Symbolic.MultiplicationSharedReassembly

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- Local minimization may use shared minima of strictly smaller recipes.
The comparison is against the current local root's raw size. -/
def InductiveLocalMinimumTransport (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → MinimumChildren φ r →
    (∀ s, s.Public restricted → s.nodeCount < r.nodeCount → SharedMinimum φ ψ s) →
    SharedMinimum φ ψ r

/-- Strong size induction first minimizes children. Their minimum sizes do
not exceed the original child sizes, so every local strict-size premise stays
strictly below the original parent. No observation budget is assumed. -/
theorem common_minima_of_inductive_local (h : InductiveLocalMinimumTransport φ ψ) :
    CommonMinima φ ψ := by
  intro r
  induction r using (measure Term.nodeCount).wf.induction with
  | h r ih =>
    intro hp
    have finish (s : Recipe n) (hs : s.Public restricted) (hc : MinimumChildren φ s)
        (hle : s.nodeCount ≤ r.nodeCount) (he : EqE (φ.eval r) (φ.eval s))
        (he' : EqE (ψ.eval r) (ψ.eval s)) : SharedMinimum φ ψ r := by
      apply SharedMinimum.of_shared_equivalent (h s hs hc ?_) he he'
      intro t ht hlt
      exact ih t (Nat.lt_of_lt_of_le hlt hle) ht
    cases r with
    | name a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
    | var a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
    | const a => exact finish _ hp trivial (Nat.le_refl _) (.refl _) (.refl _)
    | unary f a =>
      obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount; omega) hp
      have hla := ha.least a hp he.symm
      exact finish (.unary f a') ha.isPublic ha (by simp only [Term.nodeCount]; omega)
        (.unary f he) (.unary f he')
    | binary f a b =>
      obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount; omega) hp.1
      obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount; omega) hp.2
      have hla := ha.least a hp.1 he.symm
      have hlb := hb.least b hp.2 hf.symm
      exact finish (.binary f a' b') ⟨ha.isPublic,hb.isPublic⟩ ⟨ha,hb⟩
        (by simp only [Term.nodeCount]; omega) (.binary f he hf) (.binary f he' hf')
    | ternary f a b c =>
      obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) hp.1
      obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) hp.2.1
      obtain ⟨c',hc,hg,hg'⟩ := ih c (by change c.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount; omega) hp.2.2
      have hla := ha.least a hp.1 he.symm
      have hlb := hb.least b hp.2.1 hf.symm
      have hlc := hc.least c hp.2.2 hg.symm
      exact finish (.ternary f a' b' c') ⟨ha.isPublic,hb.isPublic,hc.isPublic⟩ ⟨ha,hb,hc⟩
        (by simp only [Term.nodeCount]; omega) (.ternary f he hf hg) (.ternary f he' hf' hg')
    | spk a b c d =>
      obtain ⟨a',ha,he,he'⟩ := ih a (by change a.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) hp.1
      obtain ⟨b',hb,hf,hf'⟩ := ih b (by change b.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) hp.2.1
      obtain ⟨c',hc,hg,hg'⟩ := ih c (by change c.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) hp.2.2.1
      obtain ⟨d',hd,hh,hh'⟩ := ih d (by change d.nodeCount < 1+a.nodeCount+b.nodeCount+c.nodeCount+d.nodeCount; omega) hp.2.2.2
      have hla := ha.least a hp.1 he.symm
      have hlb := hb.least b hp.2.1 hf.symm
      have hlc := hc.least c hp.2.2.1 hg.symm
      have hld := hd.least d hp.2.2.2 hh.symm
      exact finish (.spk a' b' c' d') ⟨ha.isPublic,hb.isPublic,hc.isPublic,hd.isPublic⟩ ⟨ha,hb,hc,hd⟩
        (by simp only [Term.nodeCount]; omega) (.spk he hf hg hh) (.spk he' hf' hg' hh')

end ExplainableCrypto.Helios.Symbolic.Frame
