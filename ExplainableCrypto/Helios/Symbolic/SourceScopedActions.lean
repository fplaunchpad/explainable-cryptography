import ExplainableCrypto.Helios.Symbolic.SourceScopedSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {restricted hidden : Finset Nat} {handles : Nat}

theorem Channels.broadcast_public {ch : Channels} (hc : ch.Fresh) : ch.broadcast ∉ ch.privateChannels := by
  simp only [Channels.privateChannels,Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨hc.broadcast_voter 0,hc.broadcast_voter 1,hc.broadcast_trustee⟩

theorem Channels.trustee_private (ch : Channels) : ch.trustee ∈ ch.privateChannels := by
  simp [Channels.privateChannels]

theorem Channels.honest_private (ch : Channels) (i : Fin 2) : ch.voter i.val ∈ ch.privateChannels := by
  fin_cases i <;> simp [Channels.privateChannels]

theorem Channels.voter_public_iff {ch : Channels} (hc : ch.Fresh) (i : Nat) :
    ch.voter i ∉ ch.privateChannels ↔ 2 ≤ i := by
  constructor
  · intro h
    by_contra hi
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl | rfl <;> apply h <;> simp [Channels.privateChannels]
  · intro hi h
    simp only [Channels.privateChannels,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h | h | h
    · have he := hc.voters h
      omega
    · have he := hc.voters h
      omega
    · exact hc.trustee_voter i h.symm

/-- Inversion preserves the existing frame exactly on internal steps. -/
theorem scoped_tau_iff (p q : ScopedState restricted handles) :
    ScopedStep hidden restricted p .tau q ↔ p.frame=q.frame ∧ Agent.Tau p.body q.body := by
  constructor
  · intro h
    cases h with
    | tau _ h => exact ⟨rfl,h⟩
  · rcases p with ⟨φ,p⟩
    rcases q with ⟨ψ,q⟩
    rintro ⟨he,h⟩
    cases he
    exact .tau _ h

theorem scoped_input_iff (p q : ScopedState restricted handles) (c : Nat) (r : Recipe handles) :
    ScopedStep hidden restricted p (.input c r) q ↔
      c ∉ hidden ∧ r.Public restricted ∧ p.frame=q.frame ∧
        Agent.Visible p.body (.input c (p.frame.eval r)) q.body := by
  constructor
  · intro h
    cases h with
    | input _ _ _ hc hr h => exact ⟨hc,hr,rfl,h⟩
  · rcases p with ⟨φ,p⟩
    rcases q with ⟨ψ,q⟩
    rintro ⟨hc,hr,he,h⟩
    cases he
    exact .input _ _ _ hc hr h

theorem scoped_output_iff (p : ScopedState restricted handles) (q : ScopedState restricted (handles+1)) (c : Nat) :
    ScopedStep hidden restricted p (.output c) q ↔
      c ∉ hidden ∧ ∃ m : Ground, q.frame=p.frame.extend m ∧ Agent.Visible p.body (.output c m) q.body := by
  constructor
  · intro h
    cases h with
    | output _ _ m hc h => exact ⟨hc,m,rfl,h⟩
  · rcases p with ⟨φ,p⟩
    rcases q with ⟨ψ,q⟩
    rintro ⟨hc,m,he,h⟩
    cases he
    exact .output _ _ _ hc h

theorem scoped_private_input_blocked (p q : ScopedState restricted handles) (c : Nat)
    (r : Recipe handles) (hc : c ∈ hidden) : ¬ ScopedStep hidden restricted p (.input c r) q := by
  intro h
  exact ((scoped_input_iff _ _ _ _).mp h).1 hc

theorem scoped_private_output_blocked (p : ScopedState restricted handles)
    (q : ScopedState restricted (handles+1)) (c : Nat) (hc : c ∈ hidden) :
    ¬ ScopedStep hidden restricted p (.output c) q := by
  intro h
  exact ((scoped_output_iff _ _ _).mp h).1 hc

/-- No old handle is the newly exported variable. This is enforced by the
indexed output event and does not depend on the payload value being distinct. -/
theorem output_handle_fresh (i : Fin handles) : (Fin.last handles) ≠ i.castSucc := by
  intro h
  have he := congrArg Fin.val h
  have hi := i.isLt
  simp only [Fin.val_last,Fin.val_castSucc] at he
  omega

/-- All previous public computations keep exactly their original values. -/
theorem scoped_output_preserves_old {p : ScopedState restricted handles}
    {q : ScopedState restricted (handles+1)} {c : Nat} (h : ScopedStep hidden restricted p (.output c) q)
    (r : Recipe handles) : q.frame.eval r.lift = p.frame.eval r := by
  obtain ⟨_,m,he,_⟩ := (scoped_output_iff _ _ _).mp h
  rw [he]
  exact Frame.eval_extend_lift _ _ _

/-- The fresh handle exposes the complete emitted value, including fields
containing restricted names. No redaction or equality of tally alone is assumed. -/
theorem scoped_output_new_value {p : ScopedState restricted handles}
    {q : ScopedState restricted (handles+1)} {c : Nat} (h : ScopedStep hidden restricted p (.output c) q) :
    ∃ m : Ground, q.frame.value (Fin.last handles)=m ∧ Agent.Visible p.body (.output c m) q.body := by
  obtain ⟨_,m,he,hm⟩ := (scoped_output_iff _ _ _).mp h
  exact ⟨m,by rw [he]; exact Frame.extend_last _ _,hm⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
