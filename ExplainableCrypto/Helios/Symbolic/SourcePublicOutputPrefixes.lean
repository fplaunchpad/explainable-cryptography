import ExplainableCrypto.Helios.Symbolic.SourcePublicationSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- A public active output is exactly one of the four publication prefixes,
with a unique complete continuation. Private outputs cannot satisfy the policy. -/
theorem residual_public_output_prefix (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (m : Ground) (body : Agent Empty) (hc : c ∉ ch.privateChannels)
    (hm : Agent.output c m body ∈ (residual ns swap left right extra ch phase).threads) :
    ∃ handle next, Publication ns swap left right extra phase handle m next ∧ c=ch.broadcast ∧
      ∀ body', Agent.output c m body' ∈ (residual ns swap left right extra ch phase).threads → body'=body := by
  have h₀ : c ≠ ch.voter 0 := by intro he; apply hc; rw [he]; simp [Channels.privateChannels]
  have h₁ : c ≠ ch.voter 1 := by intro he; apply hc; rw [he]; simp [Channels.privateChannels]
  have ht : c ≠ ch.trustee := by intro he; apply hc; rw [he]; exact Channels.trustee_private ch
  cases phase with
  | start => simp [residual,electionBody,boardStart,trusteeAgent,Agent.threads,Agent.threadList,h₀,h₁] at hm
  | firstReceived =>
    simp [residual,trusteeAgent,Agent.threads,Agent.threadList,h₁] at hm
    obtain ⟨rfl,rfl,rfl⟩ := hm
    refine ⟨1,.firstPublished,.first,rfl,?_⟩
    intro body' hm'
    simpa [residual,trusteeAgent,Agent.threads,Agent.threadList,h₁] using hm'
  | firstPublished => simp [residual,boardSecond,trusteeAgent,Agent.threads,Agent.threadList,h₁] at hm
  | secondReceived =>
    simp [residual,trusteeAgent,Agent.threads,Agent.threadList] at hm
    obtain ⟨rfl,rfl,rfl⟩ := hm
    refine ⟨2,Process.afterAccepted extra [],.second,rfl,?_⟩
    intro body' hm'
    simpa [residual,trusteeAgent,Agent.threads,Agent.threadList] using hm'
  | input rs =>
    have he : extra-rs.length=(extra-rs.length-1)+1 := by
      change rs.length < extra at hr
      omega
    dsimp only [residual] at hm
    rw [he,collectBallots] at hm
    simp [trusteeAgent,Agent.threads,Agent.threadList] at hm
  | check rs r => simp [residual,trusteeAgent,Agent.threads,Agent.threadList] at hm
  | rejected rs => simp [residual,trusteeAgent,Agent.threads,Agent.threadList] at hm
  | sendTally rs => simp [residual,boardFinish,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | trusteeReply rs => simp [residual,Agent.threads,Agent.threadList,ht] at hm
  | partialReady rs =>
    simp [residual,Agent.threads,Agent.threadList] at hm
    obtain ⟨rfl,rfl,rfl⟩ := hm
    refine ⟨3,.resultReady rs,.partials,rfl,?_⟩
    intro body' hm'
    simpa [residual,Agent.threads,Agent.threadList] using hm'
  | resultReady rs =>
    simp [residual,Agent.threads,Agent.threadList] at hm
    obtain ⟨rfl,rfl,rfl⟩ := hm
    refine ⟨4,.done rs,.results,rfl,?_⟩
    intro body' hm'
    simpa [residual,Agent.threads,Agent.threadList] using hm'
  | done rs => simp [residual,Agent.threads,Agent.threadList] at hm

/-- Exact public-output correspondence, including full payload and arbitrary
parallel-equivalent targets. No output is inferred merely from a matching tally. -/
theorem residual_public_output_iff (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (m : Ground) (q : Agent Empty) (hc : c ∉ ch.privateChannels) :
    Agent.Visible (residual ns swap left right extra ch phase) (.output c m) q ↔
      ∃ handle next, Publication ns swap left right extra phase handle m next ∧
        c=ch.broadcast ∧ Agent.ParEq q (residual ns swap left right extra ch next) := by
  constructor
  · intro h
    obtain ⟨body,hm⟩ := h.output_prefix
    obtain ⟨handle,next,hpub,rfl,hu⟩ := residual_public_output_prefix ns swap left right extra ch phase hr c m body hc hm
    refine ⟨handle,next,hpub,rfl,?_⟩
    apply Agent.visible_output_deterministic h (hpub.visible ch)
    intro a b ha hb
    exact (hu a ha).trans (hu b hb).symm
  · rintro ⟨handle,next,hpub,rfl,he⟩
    exact Agent.Visible.congr (.refl _) (hpub.visible ch) he.symm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
