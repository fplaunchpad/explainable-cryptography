import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open OracleComp BitOracleMachine

/-- Exact operand shape at the reached transcript boundary. The eleven other
private/public words are retained literally; no statement reconstruction is
assumed by the eventual caller theorem. -/
def inputWords (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) : Fin 23 → List Bool :=
  ![frame 0,[],q.bits,[],[],[],p.bits,frame 1,[],[],frame 2,
    uniformNatEncode e,uniformNatEncode z0,frame 3,frame 4,frame 5,
    g.bits,alpha.bits,frame 6,frame 7,frame 8,frame 9,frame 10]

/-- Bound proved in PrimeSimCommitMachineRun: complement, two powers, one product,
actual transfers, prefix parsing, guards and final cleanup. -/
def clock (p q : Nat) : Nat := ScalarComplementMachine.clock q +
  2*BinaryModPower.clock p q.size+BinaryModMultiply.clock p p.size+
  22*p.size+13*q.size+54

def cost (p q : Nat) : Nat := 32*clock p q

def answer (p q g alpha e z0 : Nat) : Nat :=
  ((g^z0%p)*(alpha^(q-e)%p))%p

/-- The retained-frame presentation is derived from the actual complete
four-draw result, including its zero scalar prefixes and preserved context. -/
theorem inputWords_source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out
    inputWords p q (primeGroupCoordinate g).val
      (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
      out.2.2.1.val out.2.2.2.1.val
      ![old.stk 0,old.stk 7,old.stk 10,old.stk 13,old.stk 14,old.stk 15,
        old.stk 18,old.stk 19,old.stk 20,old.stk 21,old.stk 22] = old.stk := by
  dsimp only
  funext k
  fin_cases k <;> rfl

#print axioms inputWords_source
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
