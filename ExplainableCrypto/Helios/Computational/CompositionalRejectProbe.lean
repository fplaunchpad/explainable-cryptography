import ExplainableCrypto.Helios.Computational.ElectionSecrecyFairBits
import VCVio.CryptoFoundations.Asymptotics.OracleClosure

/-! Exact rejection and first-callback closure targets. These are source
identities and explicit obligations, not efficiency proofs for the reduction. -/
namespace ExplainableCrypto.Helios.Computational.CompositionalRejectProbe
open OracleComp OracleSpec ElectionOracle ElectionCache
open PFunctor PFunctor.DynSystem.DynComputation OracleComp.Complexity

variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]
variable (D : ElectionSecrecyPrototype.PreparedFamily (fun n => ZMod (q n)) G)

abbrev Challenge (n : Nat) := G n × G n × G n × G n

noncomputable def rejectFamily (n : Nat) (x : Challenge (G := G) n) : ProbComp Bool :=
  ElectionSecrecyFairBits.reject D n x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Security parameter, every query and result are packed by the pinned facade. -/
noncomputable def packedReject := SecurityFamily.packProgram (rejectFamily D)

theorem reject_source (n : Nat) (x : Challenge (G := G) n) :
    rejectFamily D n x =
      simulateQ uniformSampleImpl (runFairBitUniform n
        ((fun out => decide (out.1.1.before.honestDecisions ≠
          (Decision.accepted, Decision.accepted))) <$>
          runBallotOracle (ElectionDDHSource.prefixSource (D.fingerprint n)
            x.1 x.2.1 x.2.2.1 x.2.2.2 (D.prepare n) (D.adversary n)) ∅)) := rfl

/-- First handler application inside the first actual prefix callback. -/
def firstLower (n : Nat) (cache : Cache (ZMod (q n)) (G n)) :=
  (ElectionReplaySource.lower (D.prepare n)).run cache

def packedFirstLower := SecurityFamily.packProgram (firstLower D)

theorem firstLower_source (n : Nat) (cache : Cache (ZMod (q n)) (G n)) :
    firstLower D n cache =
      (simulateQ ElectionReplaySource.impl (D.prepare n)).run cache := rfl

/-- Actual first replay entry uses the empty cache, not arbitrary function caches. -/
def firstEmptyLower (n : Nat) (_ : Unit) := firstLower D n ∅

def packedFirstEmptyLower := SecurityFamily.packProgram (firstEmptyLower D)

theorem firstEmptyLower_source (n : Nat) :
    firstEmptyLower D n () =
      (simulateQ ElectionReplaySource.impl (D.prepare n)).run ∅ := rfl

/-- The same callback inside both programmed and live random-oracle handlers. -/
def firstRaw (n : Nat) (g : G n) :=
  ElectionProgrammedSource.evaluate
    (ElectionProgrammedSource.raw g 0 (D.prepare n)) .empty ∅

def packedFirstRaw := SecurityFamily.packProgram (firstRaw D)

theorem firstRaw_source (n : Nat) (g : G n) :
    firstRaw D n g =
      runBallotOracle
        (do
          let out ← (simulateQ (ballotProgrammedImpl g 0)
            (liftComp ((simulateQ ElectionReplaySource.impl (D.prepare n)).run ∅)
              (BallotProofOracleSpec (ZMod (q n)) (G n)))).run
                (ElectionProgrammedSource.State.empty.ballot)
          pure (out.1.1, ElectionProgrammedSource.rebuild out.1.2 out.2)) ∅ := rfl

section Targets
variable {C : StepClass.{0,0}} [C.HasProd] [C.HasSum] [C.HasOption]
  (Q : QuantitativeStepClass.{0,0,0} C)

def rejectPPT
    (bd : Boundary C (SecurityFamily.Spec (fun _ => unifSpec)).toPFunctor
      (SecurityFamily.Input (Challenge (G := G))) (SecurityFamily.Output (fun _ => Bool)))
    (contract : OracleContract Q bd.interface Unit) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (packedReject D)

def firstLowerPPT
    (bd : Boundary C (SecurityFamily.Spec
      (fun n => BallotOracleSpec (ZMod (q n)) (G n))).toPFunctor
      (SecurityFamily.Input (fun n => Cache (ZMod (q n)) (G n)))
      (SecurityFamily.Output (fun n => D.Init n × Cache (ZMod (q n)) (G n))))
    (contract : OracleContract Q bd.interface Unit) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (packedFirstLower D)

def firstEmptyLowerPPT
    (bd : Boundary C (SecurityFamily.Spec
      (fun n => BallotOracleSpec (ZMod (q n)) (G n))).toPFunctor
      (SecurityFamily.Input (fun _ => Unit))
      (SecurityFamily.Output (fun n => D.Init n × Cache (ZMod (q n)) (G n))))
    (contract : OracleContract Q bd.interface Unit) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (packedFirstEmptyLower D)

def firstRawPPT
    (bd : Boundary C (SecurityFamily.Spec (fun _ => unifSpec)).toPFunctor
      (SecurityFamily.Input G)
      (SecurityFamily.Output (fun n =>
        (D.Init n × ElectionProgrammedSource.State (ZMod (q n)) (G n)) ×
          BallotOracleCache (ZMod (q n)) (G n))))
    (contract : OracleContract Q bd.interface Unit) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (packedFirstRaw D)

/-- The actual first seam requires a complete composite witness. Primitive
handler code alone does not provide its machine, implements or runBound fields. -/
theorem firstLowerPPT_iff
    (bd : Boundary C (SecurityFamily.Spec
      (fun n => BallotOracleSpec (ZMod (q n)) (G n))).toPFunctor
      (SecurityFamily.Input (fun n => Cache (ZMod (q n)) (G n)))
      (SecurityFamily.Output (fun n => D.Init n × Cache (ZMod (q n)) (G n))))
    (contract : OracleContract Q bd.interface Unit) :
    firstLowerPPT D Q bd contract ↔
      Nonempty (StrictPPTWitness Q bd contract
        (fun input => (packedFirstLower D input).toFreeM)) := Iff.rfl
end Targets

section AvailableHandlerLaw
variable {C : StepClass.{0,0}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0,0,0} C} {p r : PFunctor.{0,0}}
  [DecidableEq r.A] {outer : InterfaceBoundary C p} {inner : InterfaceBoundary C r}
  {outerContract : OracleContract Q outer Unit} {innerContract : OracleContract Q inner Unit}
  {handler : ∀ position : p.A, FreeM r (p.B position)}

/-- Pinned closure proves packed-handler efficiency and closed-consumer leaf
conformance. The conclusion deliberately does not assert closed-consumer PPT. -/
theorem available_handler_law
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    {A : Type} (consumer : FreeM p A) (accept : A → Prop)
    (model : innerContract.Model)
    (h : consumer.LeavesSatisfyUnder
      (certificate.modelMap model).resourceModel.allows accept) :
    IsOraclePPTBy Q (handlerBoundary outer inner) innerContract (packHandler handler) ∧
      (closeHandler handler consumer).LeavesSatisfyUnder model.resourceModel.allows accept :=
  ⟨certificate.isOraclePPTBy, certificate.closeLeavesSatisfyUnder model accept consumer h⟩
end AvailableHandlerLaw

section AuxiliaryControls
variable {F H : Type} [DecidableEq H] [SampleableType F]

/-- A reached occupied cache returns its retained answer with no new query. -/
theorem auxiliary_hit (key : Key H) (answer : F) :
    ElectionReplaySource.auxiliary key ((∅ : Cache F H).cacheQuery key answer) =
      pure (answer, (∅ : Cache F H).cacheQuery key answer) := by
  simp [ElectionReplaySource.auxiliary]

/-- An empty cache executes the original field sampler and inserts its answer. -/
theorem auxiliary_empty (key : Key H) :
    ElectionReplaySource.auxiliary key (∅ : Cache F H) = (do
      let answer ← liftComp (uniformSample F) (BallotOracleSpec F H)
      pure (answer, (∅ : Cache F H).cacheQuery key answer)) := rfl

/-- Two actual requests for the same key share one original sampler query tree. -/
theorem auxiliary_repeated (key : Key H) :
    (do
      let first ← ElectionReplaySource.auxiliary key (∅ : Cache F H)
      let second ← ElectionReplaySource.auxiliary key first.2
      pure ((first.1, second.1), second.2)) = (do
      let answer ← liftComp (uniformSample F) (BallotOracleSpec F H)
      pure ((answer, answer), (∅ : Cache F H).cacheQuery key answer)) := by
  rw [auxiliary_empty]
  simp only [bind_assoc, pure_bind, auxiliary_hit]
end AuxiliaryControls

#print axioms auxiliary_hit
#print axioms auxiliary_empty
#print axioms auxiliary_repeated
#print axioms reject_source
#print axioms firstLower_source
#print axioms firstEmptyLower_source
#print axioms firstRaw_source
#print axioms firstLowerPPT_iff
#print axioms available_handler_law
end ExplainableCrypto.Helios.Computational.CompositionalRejectProbe
