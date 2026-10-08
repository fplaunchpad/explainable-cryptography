import ExplainableCrypto.Helios.Symbolic.SourceFreshElectionInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Every full target realization comes from a full source realization under
the same environment and an actual Tau, up to the interpretation's existing
EvalEq on the target. Active constraints are retained in both directions. -/
theorem Reduction.realizes_backward {a b : Extended V} (h : Reduction a b)
    (env : V → Ground) {q : Agent Empty} (hb : b.Realizes env q) :
    ∃ p r, a.Realizes env p ∧ Agent.Tau p r ∧ Agent.EvalEq r q := by
  induction h generalizing q with
  | atomComm c x a b =>
    obtain ⟨r,hr,he⟩ := (Reduction.atomComm c x a b).realizes env (realizes_plain _ env)
    exact ⟨_,r,realizes_plain _ env,hr,he.symm.trans hb⟩
  | thenBranch f a b hf =>
    obtain ⟨r,hr,he⟩ := (Reduction.thenBranch f a b hf).realizes env (realizes_plain _ env)
    exact ⟨_,r,realizes_plain _ env,hr,he.symm.trans hb⟩
  | elseBranch f a b hf =>
    obtain ⟨r,hr,he⟩ := (Reduction.elseBranch f a b hf).realizes env (realizes_plain _ env)
    exact ⟨_,r,realizes_plain _ env,hr,he.symm.trans hb⟩
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    obtain ⟨p,t,hp,ht,hj⟩ := ih env hr
    exact ⟨.par p s,.par t s,realizes_par _ _ _ hp hs,ht.parLeft s,
      (hj.par (.refl s)).trans he⟩
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    obtain ⟨p,t,hp,ht,hj⟩ := ih env hs
    exact ⟨.par r p,.par r t,realizes_par _ _ _ hr hp,ht.parRight r,
      ((Agent.EvalEq.refl r).par hj).trans he⟩
  | newVar h ih =>
    obtain ⟨m,hm⟩ := hb
    obtain ⟨p,r,hp,hr,he⟩ := ih (extendEnv env m) hm
    exact ⟨p,r,⟨m,hp⟩,hr,he⟩
  | congr hs h ht ih =>
    obtain ⟨p,r,hp,hr,he⟩ := ih env ((ht.realizes env q).mpr hb)
    exact ⟨p,r,(hs.realizes env p).mpr hp,hr,he⟩

/-- An actual reduction cannot change which ground environments admit a full
realization, even through variable scopes and arbitrary structural paths. -/
theorem Reduction.has_realization_iff {a b : Extended V} (h : Reduction a b)
    (env : V → Ground) : (∃ p, a.Realizes env p) ↔ ∃ q, b.Realizes env q := by
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨q,_,hq⟩ := h.realizes env hp
    exact ⟨q,hq⟩
  · rintro ⟨q,hq⟩
    obtain ⟨p,_,hp,_,_⟩ := h.realizes_backward env hq
    exact ⟨p,hp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
