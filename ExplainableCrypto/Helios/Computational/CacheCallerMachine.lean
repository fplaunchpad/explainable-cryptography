import ExplainableCrypto.Helios.Computational.CacheHashDispatchSource
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! Resident caller entry and return. The retained cache is moved to probe work;
old answer bits are cleared; the original dispatcher returns through a guard.
An extra saved-data port is framed across the whole execution. Source operand
production and continuation decoding are separate obligations. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerMachine
open Turing.TM2 OracleComp BitOracleMachine

def size : Nat := 5+CacheHashDispatch.size
instance : NeZero size := ⟨by unfold size; omega⟩

def copyLabel (label : Fin 2) : Fin size := ⟨3+label.val,by unfold size; omega⟩
def requestLabel (label : Fin CacheHashDispatch.size) : Fin size := ⟨5+label.val,by unfold size; omega⟩
def returnLabel : Fin size := 2

def enter (next : Fin size) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))

def clear (port : Fin 12) (again next : Fin size) :
    Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .pop port (fun _ b => CoinWordLoader.encode b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))

def returnGate : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2) (.load (fun _ => 2) .halt) (.load (fun _ => 0) .halt)

def control (label : Fin 3) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  ![clear 7 0 (copyLabel 0),clear 9 1 (requestLabel 0),returnGate] label

def localCode (label : Fin size) : Command 12 size 3 :=
  if h : label.val < 3 then .compute (control ⟨label.val,h⟩)
  else if h : label.val < 5 then
    BitOracleReturnLink.command copyLabel (some 1)
      (.compute (CacheHashDispatch.copyCode 1 ⟨label.val-3,by omega⟩))
  else BitOracleReturnLink.command requestLabel (some returnLabel)
    (CacheHashDispatch.code ⟨label.val-5,by have hl := label.isLt; unfold size at hl; omega⟩)

/-- Concrete caller storage adds exactly one unbounded saved word to the twelve
existing request ports. The number of ports/labels is parameter independent. -/
def layout : Fin 12 ⊕ Fin 1 ≃ Fin 13 := finSumFinEquiv

def code : Code 13 size 3 := BitOracleStackFrame.code layout localCode

def localStart (key cache log record previous : List Bool) : Config 12 size 3 :=
  ⟨some 0,0,![[],[],[],[],[],[],[],previous,key,cache,log,record]⟩

def start (key cache log record previous saved : List Bool) : Config 13 size 3 :=
  BitOracleStackFrame.embed layout (localStart key cache log record previous) (fun _ => saved)

def ready (key cache log record saved : List Bool) : Config 13 size 3 :=
  BitOracleStackFrame.embed layout
    (BitOracleReturnLink.embed requestLabel (some returnLabel) (CacheHashDispatch.start key cache log record))
    (fun _ => saved)

def result (cfg : Config 12 CacheHashDispatch.size 3) (saved : List Bool) : Config 13 size 3 :=
  BitOracleStackFrame.embed layout (BitOracleReturnLink.embed requestLabel none cfg) (fun _ => saved)

def loadClock (cache previous : List Bool) : Nat := previous.length+1+(2*cache.length+2)+(cache.length+1)
def loadCost (cache previous : List Bool) : Nat :=
  4*(previous.length+1)+5*(2*cache.length+2)+4*(cache.length+1)

def clock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) (previous : List Bool) : Nat :=
  loadClock ((ballotCacheBitCodec p q).encode cache) previous+
    (CacheHashDispatch.requestClock cache key log slack+1)

def cost {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) (previous : List Bool) : Nat :=
  loadCost ((ballotCacheBitCodec p q).encode cache) previous+
    (CacheHashDispatch.requestCost cache key log slack+3)

end ExplainableCrypto.Helios.Computational.CacheCallerMachine
