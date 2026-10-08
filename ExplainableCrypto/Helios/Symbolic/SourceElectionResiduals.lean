import ExplainableCrypto.Helios.Symbolic.SourceParallelReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Received extra ballot values, in their actual public-frame environment. -/
def receivedBallots (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) : List Ground := rs.map (frame ns swap left right).eval

/-- Literal finite process residuals for all twelve stage forms. The rejected
residual keeps the still-waiting private trustee; null is used only after its
reply has completed. Visible and restriction rules remain separate obligations. -/
def residual (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) : Process.Phase → Agent Empty :=
  let first := ballot ns 0 (choice swap left right 0).value
  let second := ballot ns 1 (choice swap left right 1).value
  let trustee := trusteeAgent (n := n) ch (.name ns.secretKey)
  let collect := fun remaining rs => collectBallots n ch remaining (publicKey ns) first second
    (receivedBallots ns swap left right rs)
  fun phase => match phase with
  | .start => electionBody ns swap left right extra ch
  | .firstReceived => .par (.output (ch.voter 1) second .nil)
      (.par (.output ch.broadcast first (boardSecond n extra ch (publicKey ns) first)) trustee)
  | .firstPublished => .par (.output (ch.voter 1) second .nil)
      (.par (boardSecond n extra ch (publicKey ns) first) trustee)
  | .secondReceived => .par (.output ch.broadcast second (collect extra [])) trustee
  | .input rs => .par (collect (extra-rs.length) rs) trustee
  | .check rs r => .par
      (.branch (electionGuard n (publicKey ns)
        (first :: second :: receivedBallots ns swap left right rs) ((frame ns swap left right).eval r))
        (collect (extra-(rs.length+1)) (rs++[r])) .nil) trustee
  | .rejected _ => trustee
  | .sendTally rs => .par (boardFinish (n := n) ch first second (receivedBallots ns swap left right rs)) trustee
  | .trusteeReply rs => .par (.input ch.trustee (publishBody (n := n) ch (sourceTallies ns swap left right rs)))
      (.output ch.trustee (sourcePartials ns swap left right rs) .nil)
  | .partialReady rs => .output ch.broadcast (sourcePartials ns swap left right rs)
      (.output ch.broadcast (sourceResults ns swap left right rs) .nil)
  | .resultReady rs => .output ch.broadcast (sourceResults ns swap left right rs) .nil
  | .done _ => .nil

theorem receivedBallots_append (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (r : Recipe 3) :
    receivedBallots ns swap left right (rs++[r]) =
      receivedBallots ns swap left right rs ++ [(frame ns swap left right).eval r] := by
  simp only [receivedBallots,List.map_append,List.map_singleton]

/-- The source board values include both honest fields and every received input. -/
theorem source_board_values (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) :
    (honestBoardRecipes++rs).map (frame ns swap left right).eval =
      ballot ns 0 (choice swap left right 0).value ::
        ballot ns 1 (choice swap left right 1).value :: receivedBallots ns swap left right rs := by
  have h₀ : (frame ns swap left right).value 1 = ballot ns 0 (choice swap left right 0).value :=
    frame_voter_handle ns swap left right 0
  have h₁ : (frame ns swap left right).value 2 = ballot ns 1 (choice swap left right 1).value :=
    frame_voter_handle ns swap left right 1
  simp only [honestBoardRecipes,List.cons_append,List.nil_append,List.map_cons,
    receivedBallots,Frame.eval,Term.subst,h₀,h₁]

theorem source_accepts_iff (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (r : Recipe 3) :
    Process.accepts ns swap left right rs r ↔
      Accepted n (publicKey ns)
        (ballot ns 0 (choice swap left right 0).value ::
          ballot ns 1 (choice swap left right 1).value :: receivedBallots ns swap left right rs)
        ((frame ns swap left right).eval r) := by
  unfold Process.accepts
  rw [source_board_values]

/-- Uniform syntax at the next input/tally boundary, including zero extra voters.
This is valid even for overlong histories because truncated subtraction is zero. -/
theorem residual_afterAccepted (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    residual ns swap left right extra ch (Process.afterAccepted extra rs) =
      .par (collectBallots n ch (extra-rs.length) (publicKey ns)
        (ballot ns 0 (choice swap left right 0).value) (ballot ns 1 (choice swap left right 1).value)
        (receivedBallots ns swap left right rs)) (trusteeAgent (n := n) ch (.name ns.secretKey)) := by
  unfold Process.afterAccepted
  split
  · rfl
  · rename_i h
    have he : extra-rs.length=0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    simp only [residual,he,collectBallots]
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
