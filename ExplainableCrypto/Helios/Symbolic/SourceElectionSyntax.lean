import ExplainableCrypto.Helios.Symbolic.SourceElectionGuard
import ExplainableCrypto.Helios.Symbolic.SourcePayloadAgreement

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

/-- Static channel names are separate from base-message names. The two honest
voter channels and the trustee channel will be restricted by the source bridge. -/
structure Channels where
  broadcast : Nat
  trustee : Nat
  voter : Nat → Nat

/-- A reusable canonical allocation; the source semantics must still enforce
restriction rather than infer privacy merely from these distinct numbers. -/
def Channels.canonical : Channels := ⟨0,1,fun i => i+2⟩

def shiftTerm (t : Term V) : Term (Option V) := t.subst (fun v => .var (some v))

/-- After receiving partials, publish that tuple and then the ordered results. -/
def publishBody (ch : Channels) (tallies : Term V) : Agent (Option V) :=
  .output ch.broadcast (.var none) (.output ch.broadcast (resultBody (n := n) tallies) .nil)

/-- The source private tally send and reply input; no public tally ciphertext
output or extra attacker-ballot output is inserted. -/
def boardFinish (ch : Channels) (first second : Term V) (others : List (Term V)) : Agent V :=
  let tallies := tallyMessage (n := n) first second others
  .output ch.trustee tallies (.input ch.trustee (publishBody (n := n) ch tallies))

/-- Remaining public voters, in source order. Every input is followed by its
actual finite guard. Failure selects null, and the last success starts tallying. -/
def collectBallots (n : Nat) (ch : Channels) :
    Nat → {V : Type} → Term V → Term V → Term V → List (Term V) → Agent V
  | 0, _, _, first, second, others => boardFinish (n := n) ch first second others
  | remaining+1, _, key, first, second, others =>
      .input (ch.voter (others.length+2))
        (.branch
          (electionGuard n (shiftTerm key)
            (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
          (collectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
            (others.map shiftTerm ++ [.var none]))
          .nil)

/-- After the first honest ballot has been made public, receive the second. -/
def boardSecond (n extra : Nat) (ch : Channels) (key first : Term V) : Agent V :=
  .input (ch.voter 1) (.output ch.broadcast (.var none)
    (collectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) []))

/-- The complete finite source board body, with the two honest inputs and
public relays before any adversarial voter is read. -/
def boardStart (n extra : Nat) (ch : Channels) (key : Term V) : Agent V :=
  .input (ch.voter 0) (.output ch.broadcast (.var none)
    (boardSecond n extra ch (shiftTerm key) (.var none)))

def trusteeAgent (ch : Channels) (secret : Term V) : Agent V :=
  .input ch.trustee (.output ch.trustee (trusteeBody (n := n) secret) .nil)

/-- The finite election body after fresh base/channel names have been allocated.
Restriction, voter-let expansion, the exported public-key substitution and
structural correspondence are not established by this definition alone. -/
def electionBody (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) : Agent Empty :=
  .par (.output (ch.voter 0) (ballot ns 0 (choice swap left right 0).value) .nil)
    (.par (.output (ch.voter 1) (ballot ns 1 (choice swap left right 1).value) .nil)
      (.par (boardStart n extra ch (publicKey ns)) (trusteeAgent (n := n) ch (.name ns.secretKey))))
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
