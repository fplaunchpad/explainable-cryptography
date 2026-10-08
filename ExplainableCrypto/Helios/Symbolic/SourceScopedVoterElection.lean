import ExplainableCrypto.Helios.Symbolic.SourceNamePrefixPolicies
import ExplainableCrypto.Helios.Symbolic.SourceCanonicalPolicyPadding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem NoncesFreshFor.choice (ns : Names n) (left right : CandidateSubstitution n Empty)
    (hl : NoncesFreshFor ns left.value) (hr : NoncesFreshFor ns right.value) (swap : Bool) (i : Fin 2) :
    NoncesFreshFor ns (choice swap left right i).value := by
  unfold General.choice
  split <;> cases swap <;> assumption

def scopedElectionBody (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) : Named Empty :=
  scopedVotersWith ns (choice swap left right 0).value (choice swap left right 1).value
    (ch.voter 0) (ch.voter 1) (voterAdministration ns extra ch)

theorem scopedElectionBody_normalizes (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    Named.Structural (scopedElectionBody ns swap left right extra ch)
      (Named.restrictNames (voterNonceList ns 0 ++ voterNonceList ns 1)
        (.embed (.plain (electionBody ns swap left right extra ch)))) := by
  have h := scopedVotersWith_normalizes ns hf _ _ (NoncesFreshFor.choice ns left right hl hr swap 0)
    (NoncesFreshFor.choice ns left right hl hr swap 1) (ch.voter 0) (ch.voter 1) _ (voterAdministration_nonce_fresh ns hf extra ch)
  apply h.trans
  have collapse (p q : Agent Empty) : Named.Structural
      (.par (.embed (.plain p)) (.embed (.plain q))) (.embed (.plain (.par p q))) :=
    (Named.Structural.embedPar _ _).symm.trans (Named.Structural.embed (Extended.Structural.plainPar _ _).symm)
  exact ((Named.Structural.parRight _ (collapse _ _)).trans (collapse _ _)).restrictNames _

/-- The administration initially binds only its own base names and private
channels. Each voter introduces its own nonces inside its computation. -/
noncomputable def administrationNameList (ns : Names n) (ch : Channels) : List SourceName :=
  Named.restrictionNames ch.privateChannels {ns.secretKey,ns.auxiliary}

noncomputable def scopedVoterElection (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) : Named (Fin 1) :=
  Named.restrictNames (administrationNameList ns ch)
    (.par (.embed (Extended.activeFrame (sourceView ns swap left right .start)))
      ((scopedElectionBody ns swap left right extra ch).rename Empty.elim))

/-- The explicit administration and voter restrictions bind exactly the full
existing policy, including the auxiliary base name and private channels. -/
theorem administration_nonce_policy (ns : Names n) (ch : Channels) :
    (administrationNameList ns ch ++ voterNonceList ns 0 ++ voterNonceList ns 1).toFinset =
      (Named.restrictionNames ch.privateChannels ns.restricted).toFinset := by
  have hn (m : Nat) : (m ∈ (List.finRange (n+1)).map (ns.nonce 0) ∨
      m ∈ (List.finRange (n+1)).map (ns.nonce 1)) ↔ m ∈ ns.nonceNames := by
    simp only [List.mem_map,List.mem_finRange,true_and,Names.nonceNames,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨j,rfl⟩ | ⟨j,rfl⟩)
      · exact ⟨(0,j),rfl⟩
      · exact ⟨(1,j),rfl⟩
    · rintro ⟨⟨i,j⟩,rfl⟩
      fin_cases i
      · exact Or.inl ⟨j,rfl⟩
      · exact Or.inr ⟨j,rfl⟩
  ext u
  cases u with
  | base m =>
    simpa [administrationNameList,Named.restrictionNames,voterNonceList,Names.restricted,
      List.mem_map,List.mem_finRange,or_assoc] using or_congr (Iff.rfl :
        (m=ns.secretKey ∨ m=ns.auxiliary) ↔ (m=ns.secretKey ∨ m=ns.auxiliary)) (hn m)
  | channel c => simp [administrationNameList,Named.restrictionNames,voterNonceList]

theorem initialFrame_nonce_fresh (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) :
    ∀ u ∈ voterNonceList ns 0 ++ voterNonceList ns 1,
      u ∉ (Named.embed (Extended.activeFrame (sourceView ns swap left right .start))).freeNames := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  all_goals obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
  all_goals
    rw [Named.freeNames,Extended.activeFrame_base_fresh_iff]
    intro hm
    obtain ⟨i,hi⟩ := (Frame.mem_nameSupport _ _).mp hm
    change Fin 1 at i
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    change _ ∈ ({ns.secretKey} : Finset Nat) at hi
    exact (hf.2.2 _ j).1 (Finset.mem_singleton.mp hi)

/-- Complete initial-election correspondence with the paper's interleaved
voter nonce scopes, actual key frame and actual finite board/trustee context. -/
theorem scopedVoterElection_normalizes (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    Named.Structural (scopedVoterElection ns swap left right extra ch)
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) := by
  let a := Named.embed (Extended.activeFrame (sourceView ns swap left right .start))
  let p := electionBody ns swap left right extra ch
  let nonceList := voterNonceList ns 0 ++ voterNonceList ns 1
  have hb := (scopedElectionBody_normalizes ns hf swap left right hl hr extra ch).rename
    (Empty.elim : Empty → Fin 1) (fun v => v.elim)
  have he : (fun v : Empty => Term.var (Empty.elim v : Fin 1)) = Empty.elim := by funext v; exact v.elim
  have hb' : Named.Structural ((scopedElectionBody ns swap left right extra ch).rename (Empty.elim : Empty → Fin 1))
      (Named.restrictNames nonceList (.embed (.plain (Extended.groundAgent p)))) := by
    simpa only [nonceList,p,Named.restrictNames_rename,Named.rename,Extended.rename,Extended.groundAgent,he] using hb
  apply ((Named.Structural.parRight a hb').restrictNames (administrationNameList ns ch)).trans
  apply ((Named.Structural.par_restrictNames_right a _ nonceList
    (initialFrame_nonce_fresh ns hf swap left right)).restrictNames (administrationNameList ns ch)).trans
  have merge : Named.Structural (.par a (.embed (.plain (Extended.groundAgent p))))
      (.embed (Extended.frameProcess (sourceView ns swap left right .start) p)) :=
    (Named.Structural.embedPar _ _).symm
  apply ((merge.restrictNames nonceList).restrictNames (administrationNameList ns ch)).trans
  have hp := Named.Structural.restrictNames_of_toFinset_eq
    (administrationNameList ns ch ++ voterNonceList ns 0 ++ voterNonceList ns 1)
    (Named.restrictionNames ch.privateChannels ns.restricted) (administration_nonce_policy ns ch)
    (.embed (Extended.frameProcess (sourceView ns swap left right .start) p))
  simpa only [Process.Phase.handles,Named.restrictNames_append,List.append_assoc,nonceList,Named.restrictedState,sourceState,residual,p] using hp

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
