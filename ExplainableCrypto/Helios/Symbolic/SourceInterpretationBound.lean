import ExplainableCrypto.Helios.Symbolic.SourceInterpretationFree

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- A bound output extends the interpreted target with the actual complete
emitted message. All previous environment values are retained exactly. -/
theorem BoundOutput.realizes {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (env : V → Ground) {p : Agent Empty} (ha : a.Realizes env p) :
    ∃ m q, Agent.Visible p (.output c m) q ∧ b.Realizes (extendEnv env m) q := by
  induction h generalizing p with
  | openAtom h =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨m,q,hm,hq,he⟩ := h.output_realizes (extendEnv env v) hv
    exact ⟨m,q,hq,he.extend_congr hm⟩
  | scope h ih =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨m,q,hq,he⟩ := ih (extendEnv env v) hv
    refine ⟨m,q,hq,v,?_⟩
    rw [realizes_rename,extendEnv_swapBinders]
    exact he
  | parLeft d h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨m,r',hq,hr'⟩ := ih env hr
    obtain ⟨l',q,hq',hl,he'⟩ := he.visible_transport (hq.parLeft s)
    cases hl with
    | output _ hm =>
      refine ⟨_,q,hq',(realizes_par _ _ _ (hr'.extend_congr hm) ?_).congr he'⟩
      exact (realizes_rename d some _ s).mpr hs
  | parRight a h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨m,s',hq,hs'⟩ := ih env hs
    obtain ⟨l',q,hq',hl,he'⟩ := he.visible_transport (hq.parRight r)
    cases hl with
    | output _ hm =>
      refine ⟨_,q,hq',(realizes_par _ _ _ ?_ (hs'.extend_congr hm)).congr he'⟩
      exact (realizes_rename a some _ r).mpr hr
  | congr hs h ht ih =>
    obtain ⟨m,q,hq,he⟩ := ih env ((hs.realizes env p).mp ha)
    exact ⟨m,q,hq,(ht.realizes (extendEnv env m) q).mp he⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
