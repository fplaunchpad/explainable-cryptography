import ExplainableCrypto.Helios.Symbolic.SourceEquationalParallel
import ExplainableCrypto.Helios.Symbolic.SourceVisibleReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Payload-event congruence retains direction and channel and records the
complete ground message equation. These are not public bound-handle labels. -/
inductive PayloadEvent.EquivE : PayloadEvent → PayloadEvent → Prop where
  | input (c : Nat) {m n : Ground} : EqE m n → EquivE (.input c m) (.input c n)
  | output (c : Nat) {m n : Ground} : EqE m n → EquivE (.output c m) (.output c n)

theorem PayloadEvent.EquivE.refl (l : PayloadEvent) : EquivE l l := by
  cases l with
  | input c m => exact .input c (.refl m)
  | output c m => exact .output c (.refl m)

theorem PayloadEvent.EquivE.symm {l l' : PayloadEvent} (h : EquivE l l') : EquivE l' l := by
  cases h with
  | input c h => exact .input c h.symm
  | output c h => exact .output c h.symm

theorem PayloadEvent.EquivE.trans {l l' l'' : PayloadEvent}
    (h : EquivE l l') (h' : EquivE l' l'') : EquivE l l'' := by
  cases h with
  | input c h => cases h' with | input _ h' => exact .input c (h.trans h')
  | output c h => cases h' with | output _ h' => exact .output c (h.trans h')

theorem PayloadEvent.EquivE.channel {l l' : PayloadEvent} (h : EquivE l l') :
    l.channel = l'.channel := by cases h <;> rfl

theorem CoreVisible.equivE_transport {p q p' : Agent Empty} {l : PayloadEvent}
    (h : CoreVisible p l q) (he : EquivE p p') :
    ∃ l' q', CoreVisible p' l' q' ∧ PayloadEvent.EquivE l l' ∧ EquivE q q' := by
  induction h generalizing p' with
  | input c m body =>
    cases he with
    | input _ hb => exact ⟨_,_,.input c m _,.refl _,hb.bind (.refl m)⟩
  | output c m p =>
    cases he with
    | output _ hm hp => exact ⟨_,_,.output _ _ _,.output c hm,hp⟩
  | parLeft r h ih =>
    cases he with
    | par hp hr =>
      obtain ⟨l',q',hq,hl,he⟩ := ih hp
      exact ⟨_,_,.parLeft _ hq,hl,.par he hr⟩
  | parRight r h ih =>
    cases he with
    | par hr hp =>
      obtain ⟨l',q',hq,hl,he⟩ := ih hp
      exact ⟨_,_,.parRight _ hq,hl,.par hr he⟩

theorem Visible.equivE_transport {p q p' : Agent Empty} {l : PayloadEvent}
    (h : Visible p l q) (he : EquivE p p') :
    ∃ l' q', Visible p' l' q' ∧ PayloadEvent.EquivE l l' ∧ EquivE q q' := by
  obtain ⟨a,b,ha,hc,hb⟩ := h
  obtain ⟨a',ha',hea⟩ := ha.equivE_transport he
  obtain ⟨l',b',hc',hl,heb⟩ := hc.equivE_transport hea
  obtain ⟨q',hb',heq⟩ := hb.equivE_transport heb
  exact ⟨l',q',⟨a',b',ha',hc',hb'⟩,hl,heq⟩

/-- Inputs can match a prescribed E-equivalent message, in particular the
identical received term. The receiver's entire continuation is related. -/
theorem CoreVisible.input_equivE_transport {p q p' : Agent Empty} {c : Nat} {m n : Ground}
    (h : CoreVisible p (.input c m) q) (he : EquivE p p') (hm : EqE m n) :
    ∃ q', CoreVisible p' (.input c n) q' ∧ EquivE q q' := by
  generalize hl : PayloadEvent.input c m = l at h
  induction h generalizing c m n p' with
  | input c' m' body =>
    cases hl
    cases he with
    | input _ hb => exact ⟨_,.input _ _ _,hb.bind hm⟩
  | output => cases hl
  | parLeft r h ih =>
    cases he with
    | par hp hr =>
      obtain ⟨q',hq,he⟩ := ih hp hm hl
      exact ⟨_,.parLeft _ hq,.par he hr⟩
  | parRight r h ih =>
    cases he with
    | par hr hp =>
      obtain ⟨q',hq,he⟩ := ih hp hm hl
      exact ⟨_,.parRight _ hq,.par hr he⟩

theorem Visible.input_equivE_transport {p q p' : Agent Empty} {c : Nat} {m n : Ground}
    (h : Visible p (.input c m) q) (he : EquivE p p') (hm : EqE m n) :
    ∃ q', Visible p' (.input c n) q' ∧ EquivE q q' := by
  obtain ⟨a,b,ha,hc,hb⟩ := h
  obtain ⟨a',ha',hea⟩ := ha.equivE_transport he
  obtain ⟨b',hc',heb⟩ := hc.input_equivE_transport hea hm
  obtain ⟨q',hb',heq⟩ := hb.equivE_transport heb
  exact ⟨q',⟨a',b',ha',hc',hb'⟩,heq⟩

theorem Visible.input_exact_transport {p q p' : Agent Empty} {c : Nat} {m : Ground}
    (h : Visible p (.input c m) q) (he : EquivE p p') :
    ∃ q', Visible p' (.input c m) q' ∧ EquivE q q' :=
  h.input_equivE_transport he (.refl m)

theorem EquivE.input_enabled_iff {p q : Agent Empty} (h : EquivE p q) (c : Nat) (m : Ground) :
    (∃ p', Visible p (.input c m) p') ↔ ∃ q', Visible q (.input c m) q' := by
  constructor
  · rintro ⟨p',hp⟩
    obtain ⟨q',hq,_⟩ := hp.input_exact_transport h
    exact ⟨q',hq⟩
  · rintro ⟨q',hq⟩
    obtain ⟨p',hp,_⟩ := hq.input_exact_transport h.symm
    exact ⟨p',hp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
