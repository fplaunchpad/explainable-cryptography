import ExplainableCrypto.Helios.Symbolic.SourceElectionParameters

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The initial exported key domain is independent of both candidate-variable
families. Its payload is the actual administration's public key. -/
def openElectionKeyFrame (ns : Names n) : Extended (ElectionParameter n) :=
  .par (.active (.inl 0) (.unary .pk (.name ns.secretKey))) (.plain .nil)

def openElectionBody (ns : Names n) (extra : Nat) (ch : Channels) : Named (ElectionParameter n) :=
  .par ((voterInElectionTemplate ns 0).compile (ch.voter 0))
    (.par ((voterInElectionTemplate ns 1).compile (ch.voter 1))
      ((voterAdministration ns extra ch).rename Empty.elim))

/-- A single open election, independent of the two supplied candidate vectors.
The administration and per-voter nonce scopes are already explicit in its AST. -/
noncomputable def openElectionTemplate (ns : Names n) (extra : Nat) (ch : Channels) : Named (ElectionParameter n) :=
  Named.restrictNames (administrationNameList ns ch)
    (.par (.embed (openElectionKeyFrame ns)) (openElectionBody ns extra ch))

theorem openElectionKeyFrame_instantiates (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) :
    Extended.Instantiates (electionCandidateSubst swap left right) (openElectionKeyFrame ns)
      (Extended.activeFrame (sourceView ns swap left right .start) : Extended (Fin 1)) := by
  change Extended.Instantiates _ _ (.par (.active (0 : Fin 1) (.unary .pk (.name ns.secretKey))) (.plain .nil))
  exact .par (.active (electionCandidateSubst swap left right)
    (.inl (0 : Fin 1) : ElectionParameter n) (0 : Fin 1) _ rfl) (.plain _ .nil)

theorem openElectionBody_instantiates (ns : Names n) (left right : CandidateSubstitution n Empty)
    (hp : ElectionParametersFresh ns left right) (swap : Bool) (extra : Nat) (ch : Channels) :
    Named.Instantiates (electionCandidateSubst swap left right) (openElectionBody ns extra ch)
      ((scopedElectionBody ns swap left right extra ch).rename (Empty.elim : Empty → Fin 1)) :=
  .par (voterInElectionTemplate_instantiates ns left right hp swap 0 (ch.voter 0))
    (.par (voterInElectionTemplate_instantiates ns left right hp swap 1 (ch.voter 1))
      (voterAdministration_instantiates ns extra ch swap left right))

/-- Application to the whole named initial election checks every outer scope,
retains the public-key active domain, and produces the exact scoped source state. -/
theorem openElectionTemplate_instantiates (ns : Names n) (left right : CandidateSubstitution n Empty)
    (hp : ElectionParametersFresh ns left right) (swap : Bool) (extra : Nat) (ch : Channels) :
    Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch)
      (scopedVoterElection ns swap left right extra ch) := by
  apply (Named.Instantiates.par (.embed (openElectionKeyFrame_instantiates ns swap left right))
    (openElectionBody_instantiates ns left right hp swap extra ch)).restrictNames (administrationNameList ns ch)
  intro u hu v
  cases u with
  | channel c => simp
  | base m =>
    have hm : m ∈ ns.restricted := Finset.mem_union_left _
      ((Named.base_mem_restrictionNames m ch.privateChannels {ns.secretKey,ns.auxiliary}).mp hu)
    simpa using electionCandidateSubst_name_fresh ns left right hp swap m hm v

/-- Any result certified by actual template instantiation has the complete
source structural path. No independently supplied unrelated process can pass. -/
theorem instantiatedElection_normalizes (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a) :
    Named.Structural a
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) := by
  rw [ha.unique (openElectionTemplate_instantiates ns left right hp swap extra ch)]
  obtain ⟨hl,hr⟩ := noncesFreshFor_of_avoids ns left.value right.value hp
  exact scopedVoterElection_normalizes ns hf swap left right hl hr extra ch

/-- One common fresh allocation certifies actual whole-election application
for both worlds and every finite administration size/channel allocation. -/
theorem exists_open_election_application (left right : CandidateSubstitution n Empty) :
    ∃ ns : Names n, ns.Fresh ∧ ElectionParametersFresh ns left right ∧ ∀ extra ch swap,
      Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch)
        (scopedVoterElection ns swap left right extra ch) ∧
      Named.Structural (scopedVoterElection ns swap left right extra ch)
        (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) := by
  obtain ⟨ns,hf,hl,hr,hp⟩ := exists_parameter_fresh_election left.value right.value
  exact ⟨ns,hf,hp,fun extra ch swap => ⟨openElectionTemplate_instantiates ns left right hp swap extra ch,
    scopedVoterElection_normalizes ns hf swap left right hl hr extra ch⟩⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
