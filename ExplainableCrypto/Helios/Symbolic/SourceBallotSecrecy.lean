import ExplainableCrypto.Helios.Symbolic.SourceElectionRelation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Finite internal closure of the original source reduction. -/
def WeakReduction (a b : Named V) : Prop := Relation.ReflTransGen Reduction a b

/-- The literal original free label between two finite internal sequences. -/
def WeakFreeStep (a : Named V) (l : Extended.FreeLabel V) (b : Named V) : Prop :=
  ∃ a' b', WeakReduction a a' ∧ FreeStep a' l b' ∧ WeakReduction b' b

/-- Original fresh output between internal sequences. None is the bound fresh
variable, and Some retains every old public handle in the complete target. -/
def WeakBoundOutput (a : Named V) (c : Nat) (b : Named (Option V)) : Prop :=
  ∃ a' b', WeakReduction a a' ∧ BoundOutput a' c b' ∧ WeakReduction b' b

/-- Historical Definition 2 on the documented finite static-channel source
syntax. All observations are full presented-frame static equivalence. The bound
output target's exact Option domain is enumerated by outputHandle on both sides.
Free labels are required to be in the complete source domain; no finite recipe
family, stage transition or equal-tally surrogate occurs in this definition. -/
structure IsWeakLabelledBisimulation
    (R : {h : Nat} → Named (Fin h) → Named (Fin h) → Prop) : Prop where
  symmetric : ∀ {h} {a b : Named (Fin h)}, R a b → R b a
  closed : ∀ {h} {a b : Named (Fin h)}, R a b → a.Closed ∧ b.Closed
  observations : ∀ {h} {a b : Named (Fin h)}, R a b → StaticEq a b
  internal : ∀ {h} {a b a' : Named (Fin h)}, R a b → Reduction a a' →
    ∃ b', WeakReduction b b' ∧ R a' b'
  free : ∀ {h} {a b a' : Named (Fin h)} {l : Extended.FreeLabel (Fin h)},
    R a b → a.LabelScoped l → FreeStep a l a' → ∃ b', WeakFreeStep b l b' ∧ R a' b'
  bound : ∀ {h} {a b : Named (Fin h)} {a' : Named (Option (Fin h))} {c : Nat},
    R a b → BoundOutput a c a' → ∃ b', WeakBoundOutput b c b' ∧
      R (a'.rename Extended.outputHandle) (b'.rename Extended.outputHandle)

/-- Membership in some source weak labelled bisimulation; equivalently the
union of all such relations, as in historical Definition 2. -/
def WeakLabelledBisimilar {h : Nat} (a b : Named (Fin h)) : Prop :=
  ∃ R : {j : Nat} → Named (Fin j) → Named (Fin j) → Prop,
    IsWeakLabelledBisimulation R ∧ R a b

theorem WeakLabelledBisimilar.symm {h : Nat} {a b : Named (Fin h)}
    (h : WeakLabelledBisimilar a b) : WeakLabelledBisimilar b a := by
  obtain ⟨R,hr,hab⟩ := h
  exact ⟨R,hr,hr.symmetric hab⟩

theorem WeakLabelledBisimilar.staticEq {h : Nat} {a b : Named (Fin h)}
    (h : WeakLabelledBisimilar a b) : StaticEq a b := by
  obtain ⟨_,hr,hab⟩ := h
  exact hr.observations hab

/-- The existential union is itself a weak labelled bisimulation. Thus its
public relation satisfies the historical largest-relation formulation. -/
theorem weakLabelledBisimilar_isWeakLabelledBisimulation :
    IsWeakLabelledBisimulation (fun {h} => @WeakLabelledBisimilar h) := by
  constructor
  · exact fun h => h.symm
  · rintro h a b ⟨R,hr,hab⟩
    exact hr.closed hab
  · exact fun h => h.staticEq
  · rintro h a b a' ⟨R,hr,hab⟩ ha
    obtain ⟨b',hb,ht⟩ := hr.internal hab ha
    exact ⟨b',hb,R,hr,ht⟩
  · rintro h a b a' l ⟨R,hr,hab⟩ hl ha
    obtain ⟨b',hb,ht⟩ := hr.free hab hl ha
    exact ⟨b',hb,R,hr,ht⟩
  · rintro h a b a' c ⟨R,hr,hab⟩ ha
    obtain ⟨b',hb,ht⟩ := hr.bound hab ha
    exact ⟨b',hb,R,hr,ht⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The completed reachable source relation discharges every weak-bisimulation
clause. Actual matching is strong enough to use one internal step and zero
surrounding silent steps for each public action. -/
theorem source_reachable_weak_bisimulation (origin : Bool → Named (Fin 1))
    (ns : Names n) (hf : ns.Fresh) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) :
    Named.IsWeakLabelledBisimulation (SourceElectionRelation origin ns left right extra ch) := by
  refine ⟨fun h => h.symm,?_,fun h => h.staticEq hf,?_,?_,?_⟩
  · intro h a b hab
    have hw := (hab.staticEq hf).wellFormed
    exact ⟨hw.1.2,hw.2.2⟩
  · intro h a b a' hab ha
    obtain ⟨b',hb,hr⟩ := hab.internal hf hc ha
    exact ⟨b',Relation.ReflTransGen.refl.tail hb,hr⟩
  · intro h a b a' l hab _ ha
    obtain ⟨b',hb,hr⟩ := hab.free hf hc ha
    exact ⟨b',⟨b,b',.refl,hb,.refl⟩,hr⟩
  · intro h a b a' c hab ha
    obtain ⟨b',hb,hr⟩ := hab.bound hf hc ha
    exact ⟨b',⟨b,b',.refl,hb,.refl⟩,hr⟩

/-- Parametrized symbolic ballot secrecy for the actual repaired historical
scoped elections. Names n has n+1 candidates; extra adds arbitrary finitely many
administration inputs to the two honest voters. Candidate validity is carried
by CandidateSubstitution. All full-E observations and source actions occur in
WeakLabelledBisimilar; no correspondence or static-equivalence premise remains. -/
theorem scopedVoterElection_ballot_secrecy (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh) :
    Named.WeakLabelledBisimilar (scopedVoterElection ns false left right extra ch)
      (scopedVoterElection ns true left right extra ch) :=
  ⟨SourceElectionRelation (fun s => scopedVoterElection ns s left right extra ch) ns left right extra ch,
    source_reachable_weak_bisimulation _ ns hf left right extra ch hc,
    SourceElectionRelation.initial ns hf false true left right hl hr extra ch⟩

/-- The same source witness also relates the structurally normalized initial
elections. This is a consequence of the actual scoped proof. -/
theorem source_election_weak_bisimilar (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh) :
    Named.WeakLabelledBisimilar
      (Named.restrictedState ch.privateChannels (sourceState ns false left right extra ch .start))
      (Named.restrictedState ch.privateChannels (sourceState ns true left right extra ch .start)) :=
  ⟨SourceElectionRelation (fun s => scopedVoterElection ns s left right extra ch) ns left right extra ch,
    source_reachable_weak_bisimulation _ ns hf left right extra ch hc,
    (SourceElectionRelation.initial ns hf false true left right hl hr extra ch).structural
      (scopedVoterElection_normalizes ns hf false left right hl hr extra ch)
      (scopedVoterElection_normalizes ns hf true left right hl hr extra ch)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
