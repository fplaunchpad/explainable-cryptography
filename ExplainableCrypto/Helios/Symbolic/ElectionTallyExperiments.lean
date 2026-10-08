import ExplainableCrypto.Helios.Symbolic.ElectionTally
import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ElectionTallyExperiments
open ExplainableCrypto.Testing Historical General

def publicBallot (nonce : Nat) (bit : Constant) : Recipe 3 :=
  constructorBallot (.var 0) (fun _ : Fin 1 => .name nonce) (fun _ => .const bit)
    (fun _ : Fin 2 => .spk (.var 0) (.name nonce) (.const bit)
      (.ternary .penc (.var 0) (.name nonce) (.const bit)))

private def accepts (key : Ground) (board : List Ground) (b : Ground) : Bool :=
  normalizeRaw (.ternary .checkspk key (b.project 0) (b.project 1)) == .const .ok &&
  normalizeRaw (.ternary .checkspk key (b.project 0) (b.project 2)) == .const .ok &&
  normalizeRaw (b.drop 3) == .const .bottom &&
  board.all (fun earlier => normalizeRaw (earlier.project 0) != normalizeRaw (b.project 0))

private def run (key : Ground) (board : List Ground) : List Ground → Bool
  | [] => true
  | b::bs => accepts key board b && run key (board++[b]) bs

private def bit (n : Nat) : Constant := if n%2=0 then .zero else .one
private def candidate (n : Nat) : CandidateSubstitution 0 Empty :=
  if n%2=0 then (BitCandidate.abstain 0).substitution else (BitCandidate.selected (0 : Fin 1)).substitution

def replayAccepted (_ : Nat) : Bool :=
  let φ := frame ProofObservationSPOT.oneNames false (candidate 0) (candidate 1)
  let b := φ.eval (publicBallot 40 .one)
  run (publicKey ProofObservationSPOT.oneNames) (honestBoardRecipes.map φ.eval) [b,b]

def check (seed : Nat) : Bool :=
  let indices := List.range (seed%6)
  let rs := indices.map (fun i => publicBallot (40+i) (bit (seed/(i+1))))
  let expected := seed%2 + (seed/2)%2 + (indices.map (fun i => (seed/(i+1))%2)).sum
  [false,true].all (fun swap =>
    let φ := frame ProofObservationSPOT.oneNames swap (candidate seed) (candidate (seed/2))
    run (publicKey ProofObservationSPOT.oneNames) (honestBoardRecipes.map φ.eval) (rs.map φ.eval) &&
    decide ((normalizeRaw (tallyResult ProofObservationSPOT.oneNames swap
      (candidate seed) (candidate (seed/2)) rs 0)).addSyntaxSummary = AddSummary.number expected))

def emptyCountIsOne (_ : Nat) : Bool :=
  decide ((normalizeRaw (tallyResult ProofObservationSPOT.oneNames false
    (candidate 0) (candidate 0) [] 0)).addSyntaxSummary = AddSummary.number 1)

#eval campaign "sequential acceptance ignores replay (negative control)" (∀ n : Nat, replayAccepted n = true) 1 true
#eval campaign "empty abstaining tally invents one (negative control)" (∀ n : Nat, emptyCountIsOne n = true) 1 true
#eval campaign "tally decryption ignores binding (negative control)" (∀ n : Nat, DecryptionProbeExperiments.omitBinding n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "fresh sequential submissions yield the independently counted tally"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "election tally backstop failed")
  IO.println "election tally backstop: 2048 inputs, zero through five submissions, both assignments and abstention"

end ExplainableCrypto.Helios.Symbolic.ElectionTallyExperiments
