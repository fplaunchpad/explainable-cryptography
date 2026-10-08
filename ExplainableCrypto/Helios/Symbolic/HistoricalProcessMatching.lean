import ExplainableCrypto.Helios.Symbolic.HistoricalProcessInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Process
variable {n : Nat}

/-- Acceptance and rejection transfer for every public pending input, even
when the adversary chooses it after observing the preceding execution. -/
theorem accepts_swap (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3)
    (hp : ∀ s ∈ rs, s.Public ns.restricted) (hr : r.Public ns.restricted) :
    accepts ns swap left right rs r ↔ accepts ns swap' left right rs r := by
  have hb : ∀ s ∈ honestBoardRecipes++rs, s.Public ns.restricted := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · simp only [honestBoardRecipes,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl <;> trivial
    · exact hp s hs
  have h := initial_accepted_iff ns hf left right r (honestBoardRecipes++rs) hr hb
  cases swap <;> cases swap'
  · rfl
  · exact h
  · exact h.symm
  · rfl

/-- Every single internal or visible transition has a same-label, same-control
counterpart. All input/publicness and acceptance hypotheses are retained. -/
theorem Step.swap {ns : Names n} (hf : ns.Fresh) {swap : Bool} (swap' : Bool)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p q : Phase} {a : Action}
    (h : Step ns swap left right extra p a q)
    (hp : ∀ r ∈ p.history, r.Public ns.restricted) (hr : p.pendingPublic ns.restricted) :
    Step ns swap' left right extra p a q := by
  cases h with
  | receiveFirst => exact .receiveFirst
  | publishFirst => exact .publishFirst
  | receiveSecond => exact .receiveSecond
  | publishSecond => exact .publishSecond
  | input hroom hpub => exact .input hroom hpub
  | accept ha => exact .accept ((accepts_swap ns hf swap swap' left right _ _ hp hr).mp ha)
  | reject ha => exact .reject (fun hb => ha ((accepts_swap ns hf swap swap' left right _ _ hp hr).mpr hb))
  | sendTally => exact .sendTally
  | receivePartial => exact .receivePartial
  | publishPartial => exact .publishPartial
  | publishResult => exact .publishResult

/-- No fixed strategy or successful-input sequence is assumed. Reachability
quantifies over arbitrary finite choices of public attacker recipes. -/
theorem Reachable.swap {ns : Names n} (hf : ns.Fresh) {swap : Bool} (swap' : Bool)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Phase}
    (h : Reachable ns swap left right extra p) : Reachable ns swap' left right extra p := by
  induction h with
  | refl => exact .refl
  | tail path hs ih =>
    obtain ⟨a,ha⟩ := hs
    have hw := (show Reachable ns swap left right extra _ from path).wellFormed
    exact ih.tail ⟨a,ha.swap hf swap' hw.publicHistory hw.pendingPublic⟩

/-- Equality of enabled labelled/internal transitions at every reachable stage. -/
theorem reachable_step_iff {ns : Names n} (hf : ns.Fresh) {swap : Bool} (swap' : Bool)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Phase}
    (h : Reachable ns swap left right extra p) (a : Action) (q : Phase) :
    Step ns swap left right extra p a q ↔ Step ns swap' left right extra p a q :=
  ⟨fun hs => hs.swap hf swap' h.wellFormed.publicHistory h.wellFormed.pendingPublic,
    fun hs => hs.swap hf swap h.wellFormed.publicHistory h.wellFormed.pendingPublic⟩

/-- All intermediate observations use the actual currently published domain.
B7 supplies its one/two/three-handle prefixes; B8 supplies partials and results. -/
theorem wellFormed_view_staticEq {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Phase}
    (h : WellFormed ns false left right extra p) :
    Frame.StaticEq (view ns false left right p) (view ns true left right p) := by
  have hi := initial_frame_staticEq ns hf left right
  cases p with
  | start | firstReceived => exact hi.derive _ (fun _ => trivial)
  | firstPublished | secondReceived => exact hi.derive _ (fun _ => trivial)
  | resultReady rs => exact accepted_partial_staticEq ns hf left right rs h.publicHistory h.accepted
  | done rs => exact accepted_final_staticEq ns hf left right rs h.publicHistory h.accepted
  | _ => exact hi

theorem reachable_view_staticEq {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Phase}
    (h : Reachable ns false left right extra p) :
    Frame.StaticEq (view ns false left right p) (view ns true left right p) :=
  wellFormed_view_staticEq hf h.wellFormed

/-- The three obligations at a reached stage are simultaneous: all equality
observations agree, and both directions match any tau or visible action while
preserving the reachable-state invariant. This is for the normalized stage LTS;
the source-calculus operational correspondence remains a separate obligation. -/
theorem reachable_stage_matching {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Phase}
    (h : Reachable ns false left right extra p) :
    Frame.StaticEq (view ns false left right p) (view ns true left right p) ∧
    (∀ a q, Step ns false left right extra p a q →
      Step ns true left right extra p a q ∧ Reachable ns false left right extra q) ∧
    (∀ a q, Step ns true left right extra p a q →
      Step ns false left right extra p a q ∧ Reachable ns false left right extra q) := by
  refine ⟨reachable_view_staticEq hf h,?_,?_⟩
  · intro a q hs
    exact ⟨(reachable_step_iff hf true h a q).mp hs,h.tail ⟨a,hs⟩⟩
  · intro a q hs
    have hh := (reachable_step_iff hf true h a q).mpr hs
    exact ⟨hh,h.tail ⟨a,hh⟩⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Process
