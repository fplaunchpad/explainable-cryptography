import ExplainableCrypto.Helios.Symbolic.SourceEquationalVisible

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V W : Type}

/-- Parallel structure followed by full-E congruence. Commuting squares make
this composite an equivalence, without adding operational rules. -/
def EvalEq (p q : Agent V) : Prop := ∃ r, ParEq p r ∧ EquivE r q

theorem EvalEq.of_parEq {p q : Agent V} (h : ParEq p q) : EvalEq p q :=
  ⟨q,h,.refl q⟩

theorem EvalEq.of_equivE {p q : Agent V} (h : EquivE p q) : EvalEq p q :=
  ⟨p,.refl p,h⟩

theorem EvalEq.refl (p : Agent V) : EvalEq p p := .of_equivE (.refl p)

theorem EvalEq.symm {p q : Agent V} (h : EvalEq p q) : EvalEq q p := by
  obtain ⟨r,hp,he⟩ := h
  obtain ⟨p',hq,he'⟩ := hp.symm.equivE_transport he
  exact ⟨p',hq,he'.symm⟩

theorem EvalEq.trans {p q r : Agent V} (h : EvalEq p q) (h' : EvalEq q r) : EvalEq p r := by
  obtain ⟨a,hp,he⟩ := h
  obtain ⟨b,hq,he'⟩ := h'
  obtain ⟨b',ha,hb⟩ := hq.equivE_transport he.symm
  exact ⟨b',hp.trans ha,hb.symm.trans he'⟩

theorem EvalEq.par {p p' q q' : Agent V} (hp : EvalEq p p') (hq : EvalEq q q') :
    EvalEq (.par p q) (.par p' q') := by
  obtain ⟨a,ha,he⟩ := hp
  obtain ⟨b,hb,he'⟩ := hq
  exact ⟨.par a b,.par ha hb,.par he he'⟩

theorem EvalEq.subst {p q : Agent V} (h : EvalEq p q) (σ : V → Term W) :
    EvalEq (p.subst σ) (q.subst σ) := by
  obtain ⟨r,hp,he⟩ := h
  exact ⟨r.subst σ,hp.subst σ,he.subst σ⟩

theorem EvalEq.tau_transport {p q p' : Agent Empty} (h : EvalEq p q) (hp : Tau p p') :
    ∃ q', Tau q q' ∧ EvalEq p' q' := by
  obtain ⟨a,ha,he⟩ := h
  obtain ⟨q',hq,he'⟩ := (hp.congr ha.symm (.refl _)).equivE_transport he
  exact ⟨q',hq,.of_equivE he'⟩

theorem EvalEq.visible_transport {p q p' : Agent Empty} {l : PayloadEvent}
    (h : EvalEq p q) (hp : Visible p l p') :
    ∃ l' q', Visible q l' q' ∧ PayloadEvent.EquivE l l' ∧ EvalEq p' q' := by
  obtain ⟨a,ha,he⟩ := h
  obtain ⟨l',q',hq,hl,he'⟩ := (hp.congr ha.symm (.refl _)).equivE_transport he
  exact ⟨l',q',hq,hl,.of_equivE he'⟩

theorem EvalEq.input_transport {p q p' : Agent Empty} {c : Nat} {m n : Ground}
    (h : EvalEq p q) (hp : Visible p (.input c m) p') (hm : EqE m n) :
    ∃ q', Visible q (.input c n) q' ∧ EvalEq p' q' := by
  obtain ⟨a,ha,he⟩ := h
  obtain ⟨q',hq,he'⟩ := (hp.congr ha.symm (.refl _)).input_equivE_transport he hm
  exact ⟨q',hq,.of_equivE he'⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
