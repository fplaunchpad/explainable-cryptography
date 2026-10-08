import ExplainableCrypto.Helios.Computational.CacheRequestInputRun
import ExplainableCrypto.Helios.Computational.CacheHashDispatchBounds

/-! One serialized input, guarded parsing, and one complete cache request.
The fixed program uses the existing loader and dispatcher without changing
their field grammar, private workspace, or oracle instructions. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestMachine
open Turing.TM2 OracleComp BitOracleMachine

def size : Nat := 50+CacheHashDispatch.size
instance : NeZero size := ⟨by unfold size; omega⟩

def inputLabel (l : Fin 49) : Fin size := ⟨l.val,by unfold size; omega⟩
def requestLabel (l : Fin CacheHashDispatch.size) : Fin size := ⟨50+l.val,by unfold size; omega⟩
def gateLabel : Fin size := ⟨49,by unfold size; omega⟩

/-- Rejected framing halts; only successful parsing enters the request. -/
def gate : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2)
    (.load (fun _ => 0) (.goto (fun _ => requestLabel 0)))
    (.load (fun _ => 0) .halt)

def code (l : Fin size) : Command 12 size 3 :=
  if h : l.val < 49 then
    BitOracleReturnLink.command inputLabel (some gateLabel) (CacheRequestInput.code ⟨l.val,h⟩)
  else if hgate : l.val = 49 then .compute gate
  else BitOracleReturnLink.command requestLabel none
    (CacheHashDispatch.code ⟨l.val-50,by have := l.isLt; unfold size at this; omega⟩)

def start (raw : List Bool) : Config 12 size 3 :=
  BitOracleReturnLink.embed inputLabel (some gateLabel) (CacheRequestInput.start raw)

theorem input_code (l : Fin 49) : code (inputLabel l) =
    BitOracleReturnLink.command inputLabel (some gateLabel) (CacheRequestInput.code l) := by
  have h : (inputLabel l).val < 49 := l.isLt
  rw [code,dif_pos h]
  rfl

theorem request_code (l : Fin CacheHashDispatch.size) : code (requestLabel l) =
    BitOracleReturnLink.command requestLabel none (CacheHashDispatch.code l) := by
  have hn : ¬ (requestLabel l).val < 49 := by dsimp [requestLabel]; omega
  have hg : (requestLabel l).val ≠ 49 := by dsimp [requestLabel]; omega
  rw [code,dif_neg hn,dif_neg hg]
  congr 2
  apply Fin.ext
  dsimp [requestLabel]
  omega

theorem enter_request (key cache log record : List Bool) :
    BitOracleMachine.step code
      (BitOracleReturnLink.embed inputLabel (some gateLabel) (CacheRequestInput.ready key cache log record)) =
    pure (BitOracleReturnLink.embed requestLabel none (CacheHashDispatch.start key cache log record),3) := by
  rfl

end ExplainableCrypto.Helios.Computational.CacheRequestMachine
