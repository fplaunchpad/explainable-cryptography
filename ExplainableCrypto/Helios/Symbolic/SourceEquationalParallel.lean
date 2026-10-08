import ExplainableCrypto.Helios.Symbolic.SourceEquationalProcesses
import ExplainableCrypto.Helios.Symbolic.SourceParallelReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V : Type}

/-- Equational replacement commutes with the parallel structural laws in both
directions. Keeping both squares in the induction handles structural symmetry. -/
theorem ParEq.equivE_squares {p q : Agent V} (h : ParEq p q) :
    (∀ {p'}, EquivE p p' → ∃ q', ParEq p' q' ∧ EquivE q q') ∧
    (∀ {q'}, EquivE q q' → ∃ p', ParEq q' p' ∧ EquivE p p') := by
  induction h with
  | refl p => exact ⟨fun h => ⟨_,.refl _,h⟩,fun h => ⟨_,.refl _,h⟩⟩
  | symm h ih => exact ⟨ih.2,ih.1⟩
  | trans h h' ih ih' =>
    constructor
    · intro p' he
      obtain ⟨q',hp,hq⟩ := ih.1 he
      obtain ⟨r',hq',hr⟩ := ih'.1 hq
      exact ⟨r',hp.trans hq',hr⟩
    · intro r' he
      obtain ⟨q',hr,hq⟩ := ih'.2 he
      obtain ⟨p',hq',hp⟩ := ih.2 hq
      exact ⟨p',hr.trans hq',hp⟩
  | zero p =>
    constructor
    · intro p' he
      cases he with
      | par hp hn => cases hn; exact ⟨_,.zero _,hp⟩
    · intro p' he
      exact ⟨.par p' .nil,(ParEq.zero p').symm,.par he .nil⟩
  | assoc p q r =>
    constructor
    · intro p' he
      cases he with
      | par hpq hr => cases hpq with | par hp hq => exact ⟨_,.assoc _ _ _,.par hp (.par hq hr)⟩
    · intro p' he
      cases he with
      | par hp hqr => cases hqr with | par hq hr => exact ⟨_,(ParEq.assoc _ _ _).symm,.par (.par hp hq) hr⟩
  | comm p q =>
    constructor <;> intro p' he <;> cases he with
    | par hp hq => exact ⟨_,.comm _ _,.par hq hp⟩
  | par h h' ih ih' =>
    constructor
    · intro p' he
      cases he with
      | par hp hq =>
        obtain ⟨r,hr,he⟩ := ih.1 hp
        obtain ⟨s,hs,he'⟩ := ih'.1 hq
        exact ⟨.par r s,.par hr hs,.par he he'⟩
    · intro p' he
      cases he with
      | par hp hq =>
        obtain ⟨r,hr,he⟩ := ih.2 hp
        obtain ⟨s,hs,he'⟩ := ih'.2 hq
        exact ⟨.par r s,.par hr hs,.par he he'⟩

theorem ParEq.equivE_transport {p q p' : Agent V} (h : ParEq p q) (he : EquivE p p') :
    ∃ q', ParEq p' q' ∧ EquivE q q' := h.equivE_squares.1 he

/-- Matching core reductions use the same channel and branch decision.
Communication transports the entire bound receiver using the message equation. -/
theorem CoreStep.equivE_transport {p q p' : Agent Empty}
    (h : CoreStep p q) (he : EquivE p p') : ∃ q', CoreStep p' q' ∧ EquivE q q' := by
  induction h generalizing p' with
  | comm c m p q =>
    cases he with
    | par ho hi =>
      cases ho with
      | output _ hm hp =>
        cases hi with
        | input _ hq => exact ⟨_,.comm _ _ _ _,.par hp (hq.bind hm)⟩
  | thenBranch f p q hf =>
    cases he with
    | branch hg hp hq => exact ⟨_,.thenBranch _ _ _ ((hg.holds _).mp hf),hp⟩
  | elseBranch f p q hf =>
    cases he with
    | branch hg hp hq => exact ⟨_,.elseBranch _ _ _ (fun hh => hf ((hg.holds _).mpr hh)),hq⟩
  | parLeft r h ih =>
    cases he with
    | par hp hr =>
      obtain ⟨q',hq,he⟩ := ih hp
      exact ⟨_,.parLeft _ hq,.par he hr⟩
  | parRight r h ih =>
    cases he with
    | par hr hp =>
      obtain ⟨q',hq,he⟩ := ih hp
      exact ⟨_,.parRight _ hq,.par hr he⟩

theorem Tau.equivE_transport {p q p' : Agent Empty}
    (h : Tau p q) (he : EquivE p p') : ∃ q', Tau p' q' ∧ EquivE q q' := by
  obtain ⟨a,b,ha,hc,hb⟩ := h
  obtain ⟨a',ha',hea⟩ := ha.equivE_transport he
  obtain ⟨b',hc',heb⟩ := hc.equivE_transport hea
  obtain ⟨q',hb',heq⟩ := hb.equivE_transport heb
  exact ⟨q',⟨a',b',ha',hc',hb'⟩,heq⟩

theorem EquivE.tau_enabled_iff {p q : Agent Empty} (h : EquivE p q) :
    (∃ p', Tau p p') ↔ ∃ q', Tau q q' := by
  constructor
  · rintro ⟨p',hp⟩
    obtain ⟨q',hq,_⟩ := hp.equivE_transport h
    exact ⟨q',hq⟩
  · rintro ⟨q',hq⟩
    obtain ⟨p',hp,_⟩ := hq.equivE_transport h.symm
    exact ⟨p',hp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
