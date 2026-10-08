import ExplainableCrypto.Helios.Symbolic.SourceVoterComputation
import ExplainableCrypto.Helios.Symbolic.SourceNamedElectionStatic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Both honest voter computations are explicit active-let blocks. The finite
board and trustee are unchanged. Base names have already been allocated. -/
def computedElectionBody (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) : Extended Empty :=
  .par ((voterProgram ns 0 (choice swap left right 0).value).compile (ch.voter 0))
    (.par ((voterProgram ns 1 (choice swap left right 1).value).compile (ch.voter 1))
      (.plain (.par (boardStart n extra ch (publicKey ns)) (trusteeAgent (n := n) ch (.name ns.secretKey)))))

theorem computedElectionBody_normalizes (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Extended.Structural (computedElectionBody ns swap left right extra ch)
      (.plain (electionBody ns swap left right extra ch)) := by
  apply (Extended.Structural.parLeft _ (voterProgram_normalizes ns 0 _ (ch.voter 0))).trans
  apply (Extended.Structural.parRight _ (Extended.Structural.parLeft _
    (voterProgram_normalizes ns 1 _ (ch.voter 1)))).trans
  exact (Extended.Structural.parRight _ (Extended.Structural.plainPar _ _).symm).trans
    (Extended.Structural.plainPar _ _).symm

/-- The original full outer policy and exported public-key frame surround the
explicit computation blocks. This is the allocated-name source representation;
Figure 4's interleaved nonce-scope placement is a separate correspondence step. -/
noncomputable def computedVoterElection (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) : Named (Fin 1) :=
  Named.restrictNames (Named.restrictionNames ch.privateChannels ns.restricted)
    (.embed (.par (Extended.activeFrame (sourceView ns swap left right .start))
      ((computedElectionBody ns swap left right extra ch).rename Empty.elim)))

theorem computedVoterElection_normalizes (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Named.Structural (computedVoterElection ns swap left right extra ch)
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) := by
  have h := (computedElectionBody_normalizes ns swap left right extra ch).rename
    (Empty.elim : Empty → Fin 1) (fun x => x.elim)
  have he : (fun v : Empty => Term.var (Empty.elim v : Fin 1)) = Empty.elim := by
    funext v; exact v.elim
  simpa only [Process.Phase.handles,computedVoterElection,Named.restrictedState,sourceState,residual,Extended.frameProcess,
    Extended.rename,Extended.groundAgent,he] using
    (Named.Structural.embed (Extended.Structural.parRight
      (Extended.activeFrame (sourceView ns swap left right .start)) h)).restrictNames
        (Named.restrictionNames ch.privateChannels ns.restricted)

/-- Expansion introduces no extra or missing internal action, even when the
actual action uses arbitrary source structural representatives. -/
theorem computedVoterElection_reduction_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (b : Named (Fin 1)) :
    Named.Reduction (computedVoterElection ns swap left right extra ch) b ↔
      Named.Reduction (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) b := by
  have h := computedVoterElection_normalizes ns swap left right extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem computedVoterElection_free_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (l : Extended.FreeLabel (Fin 1)) (b : Named (Fin 1)) :
    Named.FreeStep (computedVoterElection ns swap left right extra ch) l b ↔
      Named.FreeStep (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) l b := by
  have h := computedVoterElection_normalizes ns swap left right extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem computedVoterElection_bound_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (channel : Nat) (b : Named (Option (Fin 1))) :
    Named.BoundOutput (computedVoterElection ns swap left right extra ch) channel b ↔
      Named.BoundOutput (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) channel b := by
  have h := computedVoterElection_normalizes ns swap left right extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

/-- The initial static clause includes the complete explicit voter code. This
is not the still-open source weak-labelled-bisimilarity/secrecy conclusion. -/
theorem computedVoterElection_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Named.StaticEq (computedVoterElection ns false left right extra ch)
      (computedVoterElection ns true left right extra ch) :=
  Named.reachable_structural_source_staticEq hf (.refl) ch
    (computedVoterElection_normalizes ns false left right extra ch).symm
    (computedVoterElection_normalizes ns true left right extra ch).symm

theorem computedVoterElection_represents (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    (computedVoterElection ns swap left right extra ch).RepresentsFrame ch.privateChannels
      (sourceView ns swap left right .start) :=
  (Named.restrictedState_represents (sourceState ns swap left right extra ch .start)).structural
    (computedVoterElection_normalizes ns swap left right extra ch).symm

theorem computedVoterElection_wellFormed (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    (computedVoterElection ns swap left right extra ch).WellFormed :=
  (computedVoterElection_represents ns swap left right extra ch).wellFormed

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
