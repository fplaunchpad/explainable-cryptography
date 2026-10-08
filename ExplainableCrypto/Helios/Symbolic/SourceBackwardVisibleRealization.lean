import ExplainableCrypto.Helios.Symbolic.SourceOpeningInternalTraces

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Every full target realization of an actual free action has a full source
realization in the same environment and the same realized public label. The
actual visible target agrees modulo the interpretation's existing EvalEq. -/
theorem FreeStep.realizes_backward {a b : Extended V} {l : FreeLabel V}
    (h : FreeStep a l b) (env : V → Ground) {q : Agent Empty} (hb : b.Realizes env q) :
    ∃ p r, a.Realizes env p ∧ l.RealizedStep env p r ∧ Agent.EvalEq r q := by
  induction h generalizing q with
  | input c m body =>
    obtain ⟨r,hr,he⟩ := (FreeStep.input c m body).realizes env (realizes_plain _ env)
    exact ⟨_,r,realizes_plain _ env,hr,he.symm.trans hb⟩
  | output c x body =>
    obtain ⟨r,hr,he⟩ := (FreeStep.output c x body).realizes env (realizes_plain _ env)
    exact ⟨_,r,realizes_plain _ env,hr,he.symm.trans hb⟩
  | scopeInput h ih =>
    obtain ⟨v,hv⟩ := hb
    obtain ⟨p,r,hp,hr,he⟩ := ih (extendEnv env v) hv
    exact ⟨p,r,⟨v,hp⟩,by simpa only [FreeLabel.RealizedStep,shiftTerm_eval] using hr,he⟩
  | scopeOutput h ih =>
    obtain ⟨v,hv⟩ := hb
    obtain ⟨p,r,hp,hr,he⟩ := ih (extendEnv env v) hv
    exact ⟨p,r,⟨v,hp⟩,hr,he⟩
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    obtain ⟨p,t,hp,ht,hj⟩ := ih env hr
    exact ⟨.par p s,.par t s,realizes_par _ _ _ hp hs,ht.parLeft s,
      (hj.par (.refl _)).trans he⟩
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    obtain ⟨p,t,hp,ht,hj⟩ := ih env hs
    exact ⟨.par r p,.par r t,realizes_par _ _ _ hr hp,ht.parRight r,
      ((Agent.EvalEq.refl _).par hj).trans he⟩
  | congr hs h ht ih =>
    obtain ⟨p,r,hp,hr,he⟩ := ih env ((ht.realizes env q).mpr hb)
    exact ⟨p,r,(hs.realizes env p).mpr hp,hr,he⟩

theorem FreeStep.has_realization_iff {a b : Extended V} {l : FreeLabel V}
    (h : FreeStep a l b) (env : V → Ground) :
    (∃ p, a.Realizes env p) ↔ ∃ q, b.Realizes env q := by
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨q,_,hq⟩ := h.realizes env hp
    exact ⟨q,hq⟩
  · rintro ⟨q,hq⟩
    obtain ⟨p,_,hp,_,_⟩ := h.realizes_backward env hq
    exact ⟨p,hp⟩

/-- The fresh captured value is constrained to the complete actually emitted
message modulo E. Every old environment value is preserved, including beneath
nested variable scopes and structural paths. -/
theorem BoundOutput.realizes_backward {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (env : V → Ground) (m : Ground) {q : Agent Empty}
    (hb : b.Realizes (extendEnv env m) q) :
    ∃ p n r, a.Realizes env p ∧ EqE m n ∧ Agent.Visible p (.output c n) r ∧ Agent.EvalEq r q := by
  induction h generalizing q with
  | openAtom h =>
    obtain ⟨p,r,hp,⟨n,hn,hr⟩,he⟩ := h.realizes_backward (extendEnv env m) hb
    exact ⟨p,n,r,⟨m,hp⟩,hn,hr,he⟩
  | scope h ih =>
    obtain ⟨v,hv⟩ := hb
    rw [realizes_rename,extendEnv_swapBinders] at hv
    obtain ⟨p,n,r,hp,hn,hr,he⟩ := ih (extendEnv env v) hv
    exact ⟨p,n,r,⟨v,hp⟩,hn,hr,he⟩
  | parLeft d h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    have hs' := (realizes_rename d some (extendEnv env m) s).mp hs
    obtain ⟨p,n,t,hp,hn,ht,hj⟩ := ih env hr
    exact ⟨.par p s,n,.par t s,realizes_par _ _ _ hp hs',hn,ht.parLeft s,
      (hj.par (.refl _)).trans he⟩
  | parRight a h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := hb
    have hr' := (realizes_rename a some (extendEnv env m) r).mp hr
    obtain ⟨p,n,t,hp,hn,ht,hj⟩ := ih env hs
    exact ⟨.par r p,n,.par r t,realizes_par _ _ _ hr' hp,hn,ht.parRight r,
      ((Agent.EvalEq.refl _).par hj).trans he⟩
  | congr hs h ht ih =>
    obtain ⟨p,n,r,hp,hn,hr,he⟩ := ih env ((ht.realizes (extendEnv env m) q).mpr hb)
    exact ⟨p,n,r,(hs.realizes env p).mpr hp,hn,hr,he⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
