import ExplainableCrypto.Helios.Computational.BallotProof
import Mathlib.Algebra.Field.ZMod
import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity

namespace ExplainableCrypto.Helios.Computational.CompositionalEncrypt
open PFunctor PFunctor.DynSystem.DynComputation
open OracleComp.Complexity

variable {C : StepClass.{0,0}} (Q : QuantitativeStepClass.{0,0,0} C)
variable (model : Q.PolynomialModel)
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

abbrev Input (F G : Type) := Nat × ((G × G) × (F × F))
abbrev Output (G : Type) := Nat × Ciphertext G

def program (x : Input F G) : Output G :=
  (x.1, encryptWith x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2)

def inputRep (nr : C.Str Nat) (fr : C.Str F) (gr : C.Str G) : C.Str (Input F G) :=
  model.kernel.cProd.prod nr (model.kernel.cProd.prod
    (model.kernel.cProd.prod gr gr) (model.kernel.cProd.prod fr fr))
def outputRep (nr : C.Str Nat) (gr : C.Str G) : C.Str (Output G) :=
  model.kernel.cProd.prod nr (model.kernel.cProd.prod gr gr)

/-- One uniform implementation retains the ordinary parameter input. This
preliminary theorem uses fixed carriers; dependent family packing is separate. -/
def realizer (nr : C.Str Nat) (fr : C.Str F) (gr : C.Str G)
    (power : Q.PolyRealizer (model.kernel.cProd.prod fr gr) gr (fun x => x.1 • x.2))
    (add : Q.PolyRealizer (model.kernel.cProd.prod gr gr) gr (fun x => x.1 + x.2)) :
    Q.PolyRealizer (inputRep Q model nr fr gr) (outputRep Q model nr gr) program := by
  letI := model.category
  let pair : {A B : Type} → C.Str A → C.Str B → C.Str (A × B) :=
    fun a b => model.kernel.cProd.prod a b
  let gg := pair gr gr
  let ff := pair fr fr
  let args := pair gg ff
  let payload := model.structural.snd nr args
  let groups := model.comp payload (model.structural.fst gg ff)
  let scalars := model.comp payload (model.structural.snd gg ff)
  let g := model.comp groups (model.structural.fst gr gr)
  let pk := model.comp groups (model.structural.snd gr gr)
  let r := model.comp scalars (model.structural.fst fr fr)
  let m := model.comp scalars (model.structural.snd fr fr)
  let first := model.comp (model.structural.pair r g) power
  let mg := model.comp (model.structural.pair m g) power
  let rpk := model.comp (model.structural.pair r pk) power
  let second := model.comp (model.structural.pair mg rpk) add
  exact model.structural.pair (model.structural.fst nr args)
    (model.structural.pair first second)

def boundary {p : PFunctor.{0,0}} (iface : InterfaceBoundary C p)
    (nr : C.Str Nat) (fr : C.Str F) (gr : C.Str G) :
    Boundary C p (Input F G) (Output G) :=
  ⟨inputRep Q model nr fr gr,outputRep Q model nr gr,iface.pos,iface.idx⟩

/-- Existing pure-resource construction lifts the derived realizer to VCVio's
strict backend-relative PPT predicate. No ciphertext efficiency is assumed. -/
theorem ppt {p : PFunctor.{0,0}} [DecidableEq p.A]
    (iface : InterfaceBoundary C p) (nr : C.Str Nat) (fr : C.Str F) (gr : C.Str G)
    (power : Q.PolyRealizer (model.kernel.cProd.prod fr gr) gr (fun x => x.1 • x.2))
    (add : Q.PolyRealizer (model.kernel.cProd.prod gr gr) gr (fun x => x.1 + x.2)) :
    letI := model.kernel.cProd
    letI := model.kernel.cSum
    letI := model.kernel.cOption
    ∀ (contract : OracleContract Q iface Unit),
      IsOraclePPTBy Q (boundary Q model iface nr fr gr) contract
        (fun x => FreeM.pure (program x)) := by
  let := model.kernel.cProd
  let := model.kernel.cSum
  let := model.kernel.cOption
  intro contract
  exact PureCertificate.isOraclePPTBy
    (PureCertificate.ofPolyRealizer (bd := boundary Q model iface nr fr gr)
      model (realizer Q model nr fr gr power add)) contract

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Literal independent fixture in additive Z/11Z: 3*2=6 and 1*2+3*4=3. -/
theorem fixture : program ((7,((2,4),(3,1))) : Input (ZMod 11) (ZMod 11)) = (7,(6,3)) := by
  decide

theorem changed_second_coordinate :
    program ((7,((2,4),(3,1))) : Input (ZMod 11) (ZMod 11)) ≠ (7,(6,2)) := by
  decide

#print axioms realizer
#print axioms ppt
#print axioms fixture
#print axioms changed_second_coordinate
end ExplainableCrypto.Helios.Computational.CompositionalEncrypt
