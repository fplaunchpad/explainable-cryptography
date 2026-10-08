import ExplainableCrypto.Helios.Symbolic.HistoricalProcessSyntax

namespace ExplainableCrypto.Helios.Symbolic
namespace Frame
variable {restricted : Finset Nat} {handles : Nat}

theorem acceptsSequence_append_iff (φ : Frame restricted handles) (n : Nat)
    (key : Recipe handles) (board xs ys : List (Recipe handles)) :
    φ.AcceptsSequence n key board (xs++ys) ↔
      φ.AcceptsSequence n key board xs ∧ φ.AcceptsSequence n key (board++xs) ys := by
  induction xs generalizing board with
  | nil => simp [AcceptsSequence]
  | cons x xs ih => simp only [List.cons_append,AcceptsSequence,ih,List.append_assoc,
      List.nil_append,and_assoc]

end Frame
namespace Historical.General.Process
variable {n : Nat}

def Phase.pendingPublic (restricted : Finset Nat) : Phase → Prop
  | .check _ r => r.Public restricted
  | _ => True

def Phase.inRange (extra : Nat) : Phase → Prop
  | .input rs | .check rs _ | .rejected rs => rs.length < extra
  | .sendTally rs | .trusteeReply rs | .partialReady rs | .resultReady rs | .done rs => rs.length=extra
  | _ => True

/-- Reachability evidence carries the real accepted prefix, public input scope,
and remaining voter count. It is proved from transitions, not an initial-state
assumption that every attacker input succeeds. -/
structure WellFormed (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (p : Phase) : Prop where
  publicHistory : ∀ r ∈ p.history, r.Public ns.restricted
  pendingPublic : p.pendingPublic ns.restricted
  accepted : (frame ns swap left right).AcceptsSequence n (.var 0) honestBoardRecipes p.history
  inRange : p.inRange extra

theorem afterAccepted_history (extra : Nat) (rs : List (Recipe 3)) :
    (afterAccepted extra rs).history=rs := by
  unfold afterAccepted
  split <;> rfl

theorem afterAccepted_wellFormed (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (rs : List (Recipe 3)) (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns swap left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hl : rs.length ≤ extra) : WellFormed ns swap left right extra (afterAccepted extra rs) := by
  unfold afterAccepted
  split
  · exact ⟨hp,True.intro,ha,by assumption⟩
  · exact ⟨hp,True.intro,ha,by dsimp [Phase.inRange]; omega⟩

theorem start_wellFormed (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) : WellFormed ns swap left right extra .start :=
  ⟨by simp [Phase.history],True.intro,True.intro,True.intro⟩

theorem Step.wellFormed {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra : Nat} {p q : Phase} {a : Action} (h : Step ns swap left right extra p a q)
    (hp : WellFormed ns swap left right extra p) : WellFormed ns swap left right extra q := by
  cases h with
  | receiveFirst | publishFirst | receiveSecond => exact ⟨hp.publicHistory,hp.pendingPublic,hp.accepted,hp.inRange⟩
  | publishSecond => exact afterAccepted_wellFormed ns swap left right extra [] hp.publicHistory hp.accepted (by simp)
  | input hroom hr => exact ⟨hp.publicHistory,hr,hp.accepted,hroom⟩
  | accept ha =>
    apply afterAccepted_wellFormed
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hp.publicHistory s hs
      · cases List.mem_singleton.mp hs
        exact hp.pendingPublic
    · apply (Frame.acceptsSequence_append_iff _ _ _ _ _ _).mpr
      exact ⟨hp.accepted,ha,True.intro⟩
    · have hr := hp.inRange
      simp only [Phase.inRange] at hr
      simp only [List.length_append,List.length_singleton]
      omega
  | reject _ => exact ⟨hp.publicHistory,True.intro,hp.accepted,hp.inRange⟩
  | sendTally | receivePartial | publishPartial | publishResult => exact ⟨hp.publicHistory,hp.pendingPublic,hp.accepted,hp.inRange⟩

theorem Reachable.wellFormed {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra : Nat} {p : Phase} (h : Reachable ns swap left right extra p) :
    WellFormed ns swap left right extra p := by
  induction h with
  | refl => exact start_wellFormed ns swap left right extra
  | tail _ hs ih => obtain ⟨a,ha⟩ := hs; exact ha.wellFormed ih

/-- Every reached final transcript accounts for exactly all extra eligible voters. -/
theorem reachable_done_history {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra : Nat} {rs : List (Recipe 3)} (h : Reachable ns swap left right extra (.done rs)) :
    rs.length=extra ∧ (∀ r ∈ rs, r.Public ns.restricted) ∧
      (frame ns swap left right).AcceptsSequence n (.var 0) honestBoardRecipes rs :=
  ⟨h.wellFormed.inRange,h.wellFormed.publicHistory,h.wellFormed.accepted⟩

/-- Rejection really stops the protocol, including private progress and output. -/
theorem rejected_no_step (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (rs : List (Recipe 3)) (a : Action) (q : Phase) :
    ¬ Step ns swap left right extra (.rejected rs) a q := by
  intro h
  cases h

theorem done_no_step (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (rs : List (Recipe 3)) (a : Action) (q : Phase) :
    ¬ Step ns swap left right extra (.done rs) a q := by
  intro h
  cases h

/-- The next output handle is fresh and extends the actual observed domain. -/
theorem Step.output_domain {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra : Nat} {p q : Phase} {handle : Nat} (h : Step ns swap left right extra p (.output handle) q) :
    handle=p.handles ∧ q.handles=p.handles+1 := by
  cases h with
  | publishSecond =>
    refine ⟨rfl,?_⟩
    unfold afterAccepted
    split <;> rfl
  | _ => exact ⟨rfl,rfl⟩

/-- Collection uses exactly the three already published handles and the next
eligible public voter channel. Publicness is enforced even for rejected inputs. -/
theorem Step.input_scope {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra : Nat} {p q : Phase} {voter : Nat} {r : Recipe 3}
    (h : Step ns swap left right extra p (.input voter r) q) :
    p.handles=3 ∧ r.Public ns.restricted ∧ voter=p.history.length+2 ∧ voter<extra+2 := by
  cases h with
  | input hroom hr => exact ⟨rfl,hr,rfl,Nat.add_lt_add_right hroom 2⟩

end Historical.General.Process
end ExplainableCrypto.Helios.Symbolic
