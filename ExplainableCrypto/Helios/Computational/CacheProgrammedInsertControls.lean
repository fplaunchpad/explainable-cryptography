import ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachineRun

namespace ExplainableCrypto.Helios.Computational.CacheProgrammedInsertControls
open CacheProgrammedInsertMachine Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
private def coord (n : Nat) (h : (n : ZMod 3)^2 = 1) : PrimeGroup 3 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (n : ZMod 3) h)
private def key : BallotForkPoint (PrimeGroup 3 2) :=
  (⟨coord 2 (by decide),coord 1 (by decide),coord 2 (by decide),coord 1 (by decide)⟩,
   (coord 1 (by decide),coord 2 (by decide)),(coord 2 (by decide),coord 1 (by decide)))
private def otherKey : BallotForkPoint (PrimeGroup 3 2) :=
  ({key.1 with generator := key.1.publicKey,publicKey := key.1.generator},key.2)
private def one : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2) :=
  (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2)).insert key 1
private def two : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2) :=
  ((∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2)).insert otherKey 0).insert key 1
private def view (cfg : CacheProgrammedInsertMachine.Config) :=
  (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)

/-- Independent literal complete12-port result for fresh false. -/
theorem fresh_false :
    view (tick^[clock (insertionFuel (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2))) (canonicalInputBound (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2)) key 0 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2))) ((primeScalarBitCodec 2).encode 0)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] false)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[false],[false],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,false,false,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms fresh_false

/-- Independent literal complete12-port result for fresh true. -/
theorem fresh_true :
    view (tick^[clock (insertionFuel (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2))) (canonicalInputBound (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2)) key 0 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode (∅ : BallotFiniteCache (ZMod 2) (PrimeGroup 3 2))) ((primeScalarBitCodec 2).encode 0)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] true)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[true],[false],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,false,false,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms fresh_true

/-- Independent literal complete12-port result for occupied false. -/
theorem occupied_false :
    view (tick^[clock (insertionFuel one) (canonicalInputBound one key 0 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode one) ((primeScalarBitCodec 2).encode 0)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] false)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[true],[false],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,false,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms occupied_false

/-- Independent literal complete12-port result for occupied true. -/
theorem occupied_true :
    view (tick^[clock (insertionFuel one) (canonicalInputBound one key 0 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode one) ((primeScalarBitCodec 2).encode 0)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] true)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[true],[false],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,false,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms occupied_true

/-- Independent literal complete12-port result for occupied agreeing. -/
theorem occupied_agreeing :
    view (tick^[clock (insertionFuel one) (canonicalInputBound one key 1 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode one) ((primeScalarBitCodec 2).encode 1)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] false)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[true],[true,false,true],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,true,true,true,true,true,true,false,true,false,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms occupied_agreeing

/-- Independent literal complete12-port result for occupied retained tail. -/
theorem occupied_retained_tail :
    view (tick^[clock (insertionFuel two) (canonicalInputBound two key 0 [true,false,true,true,false] [false,true,true,true,false,true])]
      (start ((ballotCacheBitCodec 3 2).encode two) ((primeScalarBitCodec 2).encode 0)
        ((ballotKeyBitCodec 3 2).encode key) [true,false,true,true,false] [false,true,true,true,false,true] false)) =
    (none,2,List.ofFn (![[],[],[],[],[],[],[true],[false],[true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true],[true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,true,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,false,false,false,true,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,true,false,false,true,true,false,true,true,true,true,true,false,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,false,true,false],[true,false,true,true,false],[false,true,true,true,false,true]] : Fin 12 → List Bool)) := by
  rw [padded_run]
  decide +kernel
#print axioms occupied_retained_tail

/-- Skipping the actual counter clear preserves the occupied positive counter. -/
private def skipCounter (l : Fin size) :=
  if l=3 then Stmt.load (fun _ : Fin 3 => 0) (.goto (fun _ => (4 : Fin size))) else program l
private def residue : CacheProgrammedInsertMachine.Config :=
  ⟨some 3,0,![[],[],[],[],[true],[false],[true],[true,false],[false,true],[true,true],[true,false,true],[false,true,false]]⟩
theorem skipped_counter_retained :
    ((TM2ReturnLink.tick skipCounter) residue).stk 4 = [true] := rfl
/-- The unchanged clear consumes that same positive counter in one actual step. -/
theorem original_counter_consumed : (tick residue).stk 4 = [] := rfl
/-- An occupied answer equal to the proposed answer is still a collision. -/
theorem agreeing_key_collision :
    (programmedCache one key (1 : ZMod 2)) = one ∧
    (false || !(one.lookup key).isNone) = true := by
  have hit : one.lookup key = some (1 : ZMod 2) := by decide +kernel
  simp only [programmedCache,hit,reduceCtorEq,↓reduceIte,Option.isNone_some,Bool.not_false,Bool.false_or]
  trivial
#print axioms skipped_counter_retained
#print axioms original_counter_consumed
#print axioms agreeing_key_collision
end ExplainableCrypto.Helios.Computational.CacheProgrammedInsertControls
