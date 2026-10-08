import ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport
import ExplainableCrypto.Helios.Computational.PrimeNonceSampling

/-! The historical pair caller uses two actual sampler invocations. Its retained
record and first answer occupy the sampler's saved ports; copies and reentry
cleanup are executed by the scoped transport, not by host configuration updates. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 2*PrimeNoncePairTransport.size+143
instance : NeZero size := ⟨by unfold size; omega⟩
def entryLabel (l : Fin PrimeNoncePairTransport.size) : Fin size := ⟨1+l.val,by unfold size; omega⟩
def firstLabel (l : Fin 71) : Fin size := ⟨1+PrimeNoncePairTransport.size+l.val,by unfold size; omega⟩
def betweenLabel (l : Fin PrimeNoncePairTransport.size) : Fin size := ⟨72+PrimeNoncePairTransport.size+l.val,by unfold size; omega⟩
def secondLabel (l : Fin 71) : Fin size := ⟨72+2*PrimeNoncePairTransport.size+l.val,by unfold size; omega⟩

def code (l : Fin size) : Command 11 size 3 :=
  if l = 0 then .compute
    (.branch (fun v => v == 2)
      (.goto (fun _ => betweenLabel PrimeNoncePairTransport.betweenEntry))
      (.load (fun _ => 1) .halt))
  else if h : l.val < 1+PrimeNoncePairTransport.size then
    BitOracleReturnLink.command entryLabel (some (firstLabel 0))
      (PrimeNoncePairTransport.code ⟨l.val-1,by simp only [PrimeNoncePairTransport.size] at *; omega⟩)
  else if h : l.val < 72+PrimeNoncePairTransport.size then
    BitOracleReturnLink.command firstLabel (some 0) (PrimeNonceMachine.sampleCode ⟨l.val-(1+PrimeNoncePairTransport.size),by omega⟩)
  else if h : l.val < 72+2*PrimeNoncePairTransport.size then
    BitOracleReturnLink.command betweenLabel (some (secondLabel 0))
      (PrimeNoncePairTransport.code ⟨l.val-(72+PrimeNoncePairTransport.size),by omega⟩)
  else BitOracleReturnLink.command secondLabel none
    (PrimeNonceMachine.sampleCode ⟨l.val-(72+2*PrimeNoncePairTransport.size),by have := l.isLt; unfold size at this; omega⟩)

def start (record context : List Bool) : Config 11 size 3 :=
  BitOracleReturnLink.embed entryLabel (some (firstLabel 0))
    (PrimeNoncePairTransport.entryStart record [] context)

def result (record first second modulus context : List Bool) : Config 11 size 3 :=
  ⟨none,2,![[],modulus,[],[],[],second,[],[],record,first,context]⟩

/-- A public upper bound on the first encoded nonce's length. -/
def nonceWidth (q : Nat) : Nat := 2*(q-1).size+1

/-- The controller clock will be derived from actual transport and both samplers. -/
def betweenBound (slack q : Nat) : Nat :=
  PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits
    (List.replicate (nonceWidth q) false)
def betweenCostBound (slack q : Nat) : Nat :=
  PrimeNoncePairTransport.betweenCost (SamplerOperands.input slack q []) (q-1).bits
    (List.replicate (nonceWidth q) false)
def clock (slack q : Nat) : Nat :=
  PrimeNoncePairTransport.entryClock (SamplerOperands.input slack q [])+
    (PrimeNonceMachine.sampleClock slack q+(1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q))
def cost (slack q : Nat) : Nat :=
  PrimeNoncePairTransport.entryCost (SamplerOperands.input slack q [])+
    (PrimeNonceMachine.sampleCost slack q+(3+betweenCostBound slack q+PrimeNonceMachine.sampleCost slack q))

end ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
