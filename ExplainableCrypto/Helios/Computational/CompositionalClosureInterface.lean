import VCVio.CryptoFoundations.Asymptotics.OracleClosure

/-! Exact pinned facade boundary. This file reproduces implemented semantic
closure and certificate-bearing bind, and gives the type of the still-unproved
handler substitution obligation. Merely defining that type is not its proof. -/
namespace ExplainableCrypto.Helios.Computational.CompositionalClosureInterface
open PFunctor OracleComp.Complexity PFunctor.DynSystem.DynComputation
universe u v w x y
variable {p q : PFunctor.{u,u}} {C : StepClass.{u,v}}
  [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u,v,w} C}
  [DecidableEq q.A]
  {input output : Type u} {bd : Boundary C p input output}
  {inner : InterfaceBoundary C q}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q bd.interface outerLabel}
  {innerContract : OracleContract Q inner innerLabel}
  {handler : ∀ position : p.A, FreeM q (p.B position)}

/-- Existing semantic closure consumes the selected compatible outer model;
it concludes a leaf property, not an executable substituted witness. -/
theorem checked_leaf_closure
    (cert : HandlerCertificate bd.interface inner outerContract innerContract handler)
    (model : innerContract.Model) (program : FreeM p output) (accept : output → Prop)
    (hprogram : program.LeavesSatisfyUnder
      (cert.modelMap model).resourceModel.allows accept) :
    (closeHandler handler program).LeavesSatisfyUnder model.resourceModel.allows accept :=
  cert.closeLeavesSatisfyUnder model accept program hprogram

/-- The handler certificate actually contains one uniform packed dispatcher. -/
theorem checked_handler_ppt
    (cert : HandlerCertificate bd.interface inner outerContract innerContract handler) :
    IsOraclePPTBy Q (handlerBoundary bd.interface inner) innerContract (packHandler handler) :=
  cert.isOraclePPTBy

variable [DecidableEq p.A]

/-- Exact candidate interface, deliberately NOT asserted/proved here. Even this
form may need a resource-polynomial relation between the two model moduli plus
actual composed-machine cost bounds. The existing semantic modelMap alone is
not such a polynomial transformation. -/
def QuantitativeSubstitutionObligation
    (_cert : HandlerCertificate bd.interface inner outerContract innerContract handler)
    (program : input → FreeM p output)
    (_consumer : StrictPPTWitness Q bd outerContract program) : Prop :=
  Nonempty (StrictPPTWitness Q (bd.withInterface inner.pos inner.idx) innerContract
    (fun value => closeHandler handler (program value)))

section Sequential
variable [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive]
  {final : Type u} {finalRep : C.Str final}
  {program : input → FreeM p output} {next : output → FreeM p final}

/-- The existing positive control: bind succeeds when the actual handoff and
structural machine-cost obligations are supplied explicitly. -/
def checked_bind
    (first : StrictPPTWitness Q bd outerContract program)
    (second : StrictPPTWitness Q (bd.mid finalRep) outerContract next)
    (handoff : PolynomialSeqCompHandoffBound first.realization second.realization outerContract
      second.runBound)
    (cost : PolynomialSeqCompCostCertificate first.realization second.realization outerContract) :
    StrictPPTWitness Q (bd.withOut finalRep) outerContract
      (fun value => FreeM.bind (program value) next) :=
  (BindCertificate.mk handoff cost).strictPPTWitness
end Sequential

#print axioms checked_leaf_closure
#print axioms checked_handler_ppt
#print axioms checked_bind
end ExplainableCrypto.Helios.Computational.CompositionalClosureInterface
