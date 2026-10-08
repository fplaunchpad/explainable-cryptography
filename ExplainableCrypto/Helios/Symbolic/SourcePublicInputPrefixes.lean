import ExplainableCrypto.Helios.Symbolic.SourcePublicOutputPrefixes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The only public input prefix is the next extra voter, with its complete
pending guard continuation. The private trustee and honest inputs are excluded. -/
theorem residual_public_input_prefix (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (body : Agent (Option Empty)) (hc : c ∉ ch.privateChannels)
    (hm : Agent.input c body ∈ (residual ns swap left right extra ch phase).threads) :
    ∃ rs, phase = .input rs ∧ c = ch.voter (rs.length+2) ∧
      ∀ body', Agent.input c body' ∈ (residual ns swap left right extra ch phase).threads → body'=body := by
  have h₀ : c ≠ ch.voter 0 := by intro he; apply hc; rw [he]; simp [Channels.privateChannels]
  have h₁ : c ≠ ch.voter 1 := by intro he; apply hc; rw [he]; simp [Channels.privateChannels]
  have ht : c ≠ ch.trustee := by intro he; apply hc; rw [he]; exact Channels.trustee_private ch
  cases phase with
  | start => simp [residual,electionBody,boardStart,trusteeAgent,Agent.threads,Agent.threadList,h₀,ht] at hm
  | firstReceived => simp [residual,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | firstPublished => simp [residual,boardSecond,trusteeAgent,Agent.threads,Agent.threadList,h₁,ht] at hm
  | secondReceived => simp [residual,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | input rs =>
    have he : extra-rs.length=(extra-rs.length-1)+1 := by
      change rs.length < extra at hr
      omega
    dsimp only [residual] at hm
    rw [he,collectBallots] at hm
    simp [trusteeAgent,Agent.threads,Agent.threadList,ht,receivedBallots] at hm
    obtain ⟨rfl,rfl⟩ := hm
    refine ⟨rs,rfl,rfl,?_⟩
    intro body' hm'
    dsimp only [residual] at hm'
    rw [he,collectBallots] at hm'
    simpa [trusteeAgent,Agent.threads,Agent.threadList,ht,receivedBallots] using hm'
  | check rs r => simp [residual,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | rejected rs => simp [residual,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | sendTally rs => simp [residual,boardFinish,trusteeAgent,Agent.threads,Agent.threadList,ht] at hm
  | trusteeReply rs => simp [residual,Agent.threads,Agent.threadList,ht] at hm
  | partialReady rs => simp [residual,Agent.threads,Agent.threadList] at hm
  | resultReady rs => simp [residual,Agent.threads,Agent.threadList] at hm
  | done rs => simp [residual,Agent.threads,Agent.threadList] at hm

/-- Recipe evaluation happens at input; acceptance remains a subsequent silent
step. Every possible target retains precisely the same parallel context. -/
theorem residual_public_input_iff (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (r : Recipe 3) (q : Agent Empty) (hc : c ∉ ch.privateChannels) :
    Agent.Visible (residual ns swap left right extra ch phase)
      (.input c ((frame ns swap left right).eval r)) q ↔
      ∃ rs, phase = .input rs ∧ c = ch.voter (rs.length+2) ∧
        Agent.ParEq q (residual ns swap left right extra ch (.check rs r)) := by
  constructor
  · intro h
    obtain ⟨body,hm⟩ := h.input_prefix
    obtain ⟨rs,rfl,rfl,hu⟩ := residual_public_input_prefix ns swap left right extra ch phase hr c body hc hm
    refine ⟨rs,rfl,rfl,?_⟩
    apply Agent.visible_input_deterministic h (residual_visible_input ns swap left right extra ch rs r hr)
    intro a b ha hb
    exact (hu a ha).trans (hu b hb).symm
  · rintro ⟨rs,rfl,rfl,he⟩
    exact Agent.Visible.congr (.refl _) (residual_visible_input ns swap left right extra ch rs r hr) he.symm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
