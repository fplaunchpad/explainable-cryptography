import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachineRun
import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open PrimeProgrammedStateSource
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result (PrimeSimKeyCaller.sourceResult slack g pk vote (saved s live) out).stk
    (shadow s) ((ballotCacheBitCodec p q).encode live) [s.bad] (history s)

/-- All parser premises follow from the actual predecessor result, including
canonical nested framing, singleton flag and reusable empty work. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost (PrimeHonestInputMachine.input g pk slack vote (saved s live)).length,
      BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote (saved s live)).length)
        (start (PrimeSimKeyCaller.sourceResult slack g pk vote (saved s live) out).stk) =
      pure (sourceResult slack g pk vote s live out,charge) := by
  have he := charged (uniformNatEncode p)
    ((ballotCiphertextBitCodec p q).encode (g,pk)) (SamplerOperands.input slack q [])
    [vote] (shadow s) ((ballotCacheBitCodec p q).encode live) (history s) s.bad
    (PrimeSimKeyCaller.sourceResult slack g pk vote (saved s live) out).stk
    (by rw [source_context]; rfl) (source_work slack g pk vote s live out)
  simpa only [source_context,sourceResult] using he

#print axioms charged_source
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
