import ExplainableCrypto.Helios.Symbolic.SourceNamedBoundPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Bound-output factorization retains its channel while choosing one distinct
prefix away from that channel and every requested external name. -/
theorem BoundOutput.fresh_prenex {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (a' : Extended V) (b' : Extended (Option V)),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.BoundOutput a' c b' ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ insert (SourceName.channel c) avoid := by
  obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := h.prenex
  obtain ⟨ns',e,k,ha',hb',hn',hd,_,_,hfix⟩ := exists_common_fresh_prefix ns (.embed a') (.embed b')
    (insert (SourceName.channel c) avoid)
  have hc : k c = c := SourceName.channel.inj (hfix (.channel c) (Finset.mem_insert_self _ _)
    (fun hns => hn (.channel c) hns rfl))
  have hr' := hr.mapNames e k
  rw [hc] at hr'
  exact ⟨ns',_,_,ha.trans ha',hb.trans hb',hr',hd,hn'⟩

/-- The actual emitted complete message extends any supplied realization of
the factored source. Transfer from other canonical representatives is separate. -/
theorem BoundOutput.prenex_interpreted {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) :
    ∃ (ns : List SourceName) (a' : Extended V) (b' : Extended (Option V)),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.BoundOutput a' c b' ∧
      (∀ n ∈ ns, n ≠ SourceName.channel c) ∧
      ∀ (env : V → Ground) (p : Agent Empty), a'.Realizes env p →
        ∃ m q, Agent.Visible p (.output c m) q ∧ b'.Realizes (extendEnv env m) q := by
  obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := h.prenex
  exact ⟨ns,a',b',ha,hb,hr,hn,fun env _ hp => hr.realizes env hp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
