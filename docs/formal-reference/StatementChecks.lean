import ExplainableCrypto.Helios.Computational.ElectionSecurityFamily
import ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecy
import ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecySPOT
import ExplainableCrypto.Helios.Symbolic.AcceptedSequences

/-! Typed concordance checks for selected displays in main.tex.
These verify restated Lean interfaces, not the LaTeX transcription itself.
They add no axiom, new protocol rule or assumed correspondence. -/
namespace ExplainableCrypto.Helios.Symbolic.FormalReference
open Historical Historical.General Historical.General.Source

theorem acceptance_display {V : Type} (n : Nat) (key b : Term V)
    (board : List (Term V)) :
    Accepted n key board b ↔
      ProofValid n key b ∧
      EqE (b.drop (2 * (n + 1) + 1)) (.const .bottom) ∧
      ∀ a ∈ board, ∀ i j : Fin (n + 1),
        ¬ EqE (a.project i.val) (b.project j.val) := Iff.rfl

theorem observations_display {restricted : Finset Nat} {h : Nat}
    (φ ψ : Frame restricted h) :
    φ.StaticEq ψ ↔ ∀ r s : Recipe h, r.Public restricted → s.Public restricted →
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) := Iff.rfl

theorem secrecy_display {n : Nat} (ns : Names n) (hf : ns.Fresh)
    (leftCandidates rightCandidates : CandidateSubstitution n Empty)
    (hl : NoncesFreshFor ns leftCandidates.value) (hr : NoncesFreshFor ns rightCandidates.value)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) :
    Named.WeakLabelledBisimilar
      (scopedVoterElection ns false leftCandidates rightCandidates extra ch)
      (scopedVoterElection ns true leftCandidates rightCandidates extra ch) :=
  scopedVoterElection_ballot_secrecy ns hf leftCandidates rightCandidates hl hr extra ch hc

-- The two action clauses most easily lost by a prose compression.
theorem internal_clause {R : {h : Nat} → Named (Fin h) → Named (Fin h) → Prop}
    (hR : Named.IsWeakLabelledBisimulation R) {h : Nat} {a b a' : Named (Fin h)}
    (hab : R a b) (ha : Named.Reduction a a') :
    ∃ b', Named.WeakReduction b b' ∧ R a' b' := hR.internal hab ha

theorem bound_clause {R : {h : Nat} → Named (Fin h) → Named (Fin h) → Prop}
    (hR : Named.IsWeakLabelledBisimulation R) {h : Nat} {a b : Named (Fin h)}
    {a' : Named (Option (Fin h))} {c : Nat}
    (hab : R a b) (ha : Named.BoundOutput a c a') :
    ∃ b', Named.WeakBoundOutput b c b' ∧
      R (a'.rename Extended.outputHandle) (b'.rename Extended.outputHandle) :=
  hR.bound hab ha

#print axioms acceptance_display
#print axioms observations_display
#print axioms secrecy_display
#print axioms internal_clause
#print axioms bound_clause
end ExplainableCrypto.Helios.Symbolic.FormalReference


namespace ExplainableCrypto.Helios.Computational.FormalReference
open OracleComp OracleSpec ElectionOracle ReductionEfficiency
open ElectionSecurityFamily

variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]

/-- The challenge bit is uniform, and the returned bit means a correct guess.
The same oracle computation runs preparation before sampling the challenge. -/
theorem game_display (A : Family q G) (n : Nat) :
    preparedGame (A.fingerprint n) (A.generator n) (A.prepare n) (A.adversary n) =
      (do
        let initial ← A.prepare n
        let vote ← liftProb (uniformSample Bool)
        let guess ← world (A.fingerprint n) (A.generator n) (A.adversary n initial) vote
        pure (decide (guess = vote))) := by
  simp only [preparedGame, game]

/-- The displayed bias uses the unclocked attack and the empty shared cache. -/
theorem bias_display (A : Family q G) (n : Nat) :
    A.bias n = |(Pr[fun out => out.1 = true | ElectionOracle.run
      (preparedGame (A.fingerprint n) (A.generator n) (A.prepare n) (A.adversary n)) ∅]).toReal - 1/2| := rfl

/-- All four theorem hypotheses are retained; Family carries the representation,
query bounds, output growth, private encodings and generator conditions. -/
theorem computational_secrecy_display (A : Family q G)
    (hsize : negligible (fun n => noncePointBound (ZMod (q n))))
    (hmain : MainReductionEfficient A.prepared A.representation)
    (hreject : RejectionReductionEfficient A.prepared A.representation)
    (hddh : DDHAssumption (q := q) A.representation A.generator) :
    negligible (fun n => ENNReal.ofReal (A.bias n)) :=
  A.ballot_secrecy hsize hmain hreject hddh

#print axioms game_display
#print axioms bias_display
#print axioms computational_secrecy_display
end ExplainableCrypto.Helios.Computational.FormalReference
