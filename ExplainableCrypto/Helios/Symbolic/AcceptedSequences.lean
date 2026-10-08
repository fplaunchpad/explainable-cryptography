import ExplainableCrypto.Helios.Symbolic.ElectionTally

namespace ExplainableCrypto.Helios.Symbolic.Frame.StaticEq
variable {restricted : Finset Nat} {handles : Nat} {φ ψ : Frame restricted handles}

/-- Sequential acceptance remains a public observation, including the board
extension after every successful submission. -/
theorem acceptsSequence_iff (h : φ.StaticEq ψ) (n : Nat) (key : Recipe handles)
    (hk : key.Public restricted) (board submissions : List (Recipe handles))
    (hb : ∀ r ∈ board, r.Public restricted) (hs : ∀ r ∈ submissions, r.Public restricted) :
    φ.AcceptsSequence n key board submissions ↔ ψ.AcceptsSequence n key board submissions := by
  induction submissions generalizing board with
  | nil => rfl
  | cons r rs ih =>
    have hr := hs r (by simp)
    have ht : ∀ s ∈ rs, s.Public restricted := fun s h => hs s (by simp [h])
    have hb' : ∀ s ∈ board++[r], s.Public restricted := by
      intro s hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hb s hmem
      · simp only [List.mem_singleton] at hmem
        subst s
        exact hr
    exact and_congr (h.accepted_iff n key r board hk hr hb) (ih (board++[r]) hb' ht)

end ExplainableCrypto.Helios.Symbolic.Frame.StaticEq

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem initial_accepted_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (board : List (Recipe 3))
    (hr : r.Public ns.restricted) (hb : ∀ s ∈ board, s.Public ns.restricted) :
    Accepted n (publicKey ns) (board.map (frame ns false left right).eval) ((frame ns false left right).eval r) ↔
    Accepted n (publicKey ns) (board.map (frame ns true left right).eval) ((frame ns true left right).eval r) :=
  (initial_frame_staticEq ns hf left right).accepted_iff n (.var 0) r board trivial hr hb

theorem initial_acceptsSequence_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (board submissions : List (Recipe 3))
    (hb : ∀ r ∈ board, r.Public ns.restricted) (hs : ∀ r ∈ submissions, r.Public ns.restricted) :
    (frame ns false left right).AcceptsSequence n (.var 0) board submissions ↔
    (frame ns true left right).AcceptsSequence n (.var 0) board submissions :=
  (initial_frame_staticEq ns hf left right).acceptsSequence_iff n (.var 0) trivial board submissions hb hs

/-- Common data for one accepted adversarial ballot. Nonce recipes are shared;
their evaluated values need not coincide across the voting worlds. -/
structure SharedBallotData (ns : Names n) where
  nonces : Fin (n+1) → Recipe 3
  bits : Fin (n+1) → Constant
  isBit : ∀ j, bits j = .zero ∨ bits j = .one
  valid : CandidateValues (V := Fin 3) (fun j => .const (bits j))
  publicNonce : ∀ j, (nonces j).Public ns.restricted

def SharedBallotData.Explains (ns : Names n) (left right : CandidateSubstitution n Empty)
    (recipe : Recipe 3) (d : SharedBallotData ns) : Prop :=
  ∀ (swap : Bool) (j : Fin (n+1)),
    EqE (((frame ns swap left right).eval recipe).project j.val)
      (.ternary .penc (publicKey ns) ((frame ns swap left right).eval (d.nonces j)) (.const (d.bits j)))

/-- The initial theorem discharges the static-equivalence premise of shared
component reconstruction for an accepted ballot after both honest entries. -/
theorem initial_accepted_common_data (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (hr : r.Public ns.restricted)
    (board : List (Recipe 3))
    (ha : Accepted n (publicKey ns) (board.map (frame ns false left right).eval) ((frame ns false left right).eval r))
    (hb : ∀ i : Fin 2, (Term.var i.succ : Recipe 3) ∈ board) :
    ∃ d : SharedBallotData ns, d.Explains ns left right r := by
  have hboard : ∀ i : Fin 2, ballot ns i (choice false left right i).value ∈
      board.map (frame ns false left right).eval := by
    intro i
    have h : (frame ns false left right).eval (.var i.succ) ∈
        board.map (frame ns false left right).eval := List.mem_map.mpr ⟨.var i.succ,hb i,rfl⟩
    simpa only [Frame.eval,Term.subst,frame_voter_handle] using h
  obtain ⟨nonces,bits,hbit,hvalid,hpub,he⟩ := accepted_ballot_common_components ns left right
    (initial_frame_staticEq ns hf left right) r hr _ ha hboard
  exact ⟨⟨nonces,bits,hbit,hvalid,hpub⟩,he⟩

/-- Each accepted submission gets one common valid vector, with the list
alignment and actual evaluation of every ciphertext component explicit. -/
theorem accepted_sequence_common_data (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (board submissions : List (Recipe 3))
    (hb : ∀ i : Fin 2, (Term.var i.succ : Recipe 3) ∈ board)
    (hp : ∀ r ∈ submissions, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) board submissions) :
    ∃ ds : List (SharedBallotData ns),
      List.Forall₂ (fun r d => d.Explains ns left right r) submissions ds := by
  induction submissions generalizing board with
  | nil => exact ⟨[],.nil⟩
  | cons r rs ih =>
    obtain ⟨d,hd⟩ := initial_accepted_common_data ns hf left right r (hp r (by simp)) board ha.1 hb
    obtain ⟨ds,hds⟩ := ih (board++[r]) (fun i => List.mem_append_left _ (hb i))
      (fun s h => hp s (by simp [h])) ha.2
    exact ⟨d::ds,.cons hd hds⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
