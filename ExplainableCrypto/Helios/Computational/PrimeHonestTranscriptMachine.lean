import ExplainableCrypto.Helios.Computational.CacheHashMachine
import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachineSource

/-! First full-field challenge of the actual programmed honest-proof handler.
The previous statement and both nonce prefixes remain resident and unchanged. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

def sampleLayout : Fin 12 ⊕ Fin 11 ≃ Fin 23 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [1,2,3,4,5,7,8,9,0,17,14,19,6,10,11,12,13,15,16,18,20,21,22]
    (by decide +kernel) (by decide +kernel))
def samplerCode : Code 23 47 3 := BitOracleStackFrame.code sampleLayout CacheHashMachine.sampleCode

def sampleLabel (l : Fin 47) : Fin 48 := ⟨1+l.val,by omega⟩
def code (l : Fin 48) : Command 23 48 3 :=
  if l = 0 then .compute
    (.branch (fun v => v == 2)
      (.load (fun _ => 0) (.goto (fun _ => sampleLabel 0)))
      (.load (fun _ => 1) .halt))
  else BitOracleReturnLink.command sampleLabel none
    (samplerCode ⟨l.val-1,by omega⟩)

abbrev Config := BitOracleMachine.Config 23 48 3

def frame (nonce first second samplerMod modulus g pk : List Bool) (vote : Bool) (extra : Fin 3 → List Bool) : Fin 11 → List Bool :=
  ![modulus,extra 0,extra 1,extra 2,nonce,pk,g,[vote],first,second,samplerMod]

def start (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) : Config :=
  ⟨some 0,2,![beta,[],[],[],[],[],modulus,[],[],[],extra 0,extra 1,extra 2,nonce,context,pk,g,alpha,[vote],record,first,second,samplerMod]⟩

def result (challenge scalarMod alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) : Config :=
  ⟨none,2,![beta,[],scalarMod,[],[],[],modulus,challenge,[],[],extra 0,extra 1,extra 2,nonce,context,pk,g,alpha,[vote],record,first,second,samplerMod]⟩

def clock (slack q : Nat) : Nat := 1+CacheHashMachine.sampleClock slack q
def cost (slack q : Nat) : Nat := 3+CacheHashMachine.sampleCost slack q

end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine

namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

theorem sample_code (l : Fin 47) : code (sampleLabel l) =
    BitOracleReturnLink.command sampleLabel none (samplerCode l) := by
  fin_cases l <;> rfl

/-- Actual success guard and reset enter the reused resident-copy sampler,
with all statement, nonce and saved-transcript words in its exact frame. -/
theorem entry_step (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    step code (start alpha beta nonce record first second samplerMod context modulus g pk vote extra) =
      pure (BitOracleReturnLink.embed sampleLabel none
        (BitOracleStackFrame.embed sampleLayout
          (CacheHashMachine.sampleStart record beta alpha context)
          (frame nonce first second samplerMod modulus g pk vote extra)),3) := by
  change (pure ((⟨_,_,_⟩ : Config),3) : OracleComp spec (Config × Nat)) = pure (_,3)
  apply congrArg (fun cfg : Config => (pure (cfg,3) : OracleComp spec (Config × Nat)))
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

/-- The existing full sampler result adds only its modulus and scalar prefix;
all original statement, nonce and prior-transcript words are retained. -/
theorem sample_result (challenge scalarMod alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    BitOracleReturnLink.embed sampleLabel none
      (BitOracleStackFrame.embed sampleLayout
        (CacheHashMachine.sampleResult challenge scalarMod beta alpha context record)
        (frame nonce first second samplerMod modulus g pk vote extra)) =
      result challenge scalarMod alpha beta nonce record first second samplerMod context modulus g pk vote extra := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

#print axioms sample_code
#print axioms entry_step
#print axioms sample_result
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
