import ExplainableCrypto.Helios.Computational.PreparedScalarMachine

/-! Independent operand, carry, malformed-input and complete-sampler controls. -/
namespace ExplainableCrypto.Helios.Computational.SamplerOperandsControls
open OracleComp OracleSpec SamplerOperands

private def frame : Frame := ![[true,false],[false],[true,true]]

/-- Literal modulus eleven and slack two produce six tokens, preserving suffix/frame. -/
theorem direct_control :
    ∃ used ≤ 30, tick^[used] (start false (input 2 11 [false,true]) frame) =
      state none [false,true] [true,true,false,true] (List.replicate 6 true) [] [] frame none := by
  exact run 2 11 (by decide) [false,true] frame

/-- Upper bound seven carries to range eight, increasing the required binary width. -/
theorem carry_control :
    ∃ used ≤ 34, tick^[used] (start true (input 1 7 [true,false]) frame) =
      state none [true,false] [false,false,false,true] (List.replicate 5 true) [] [] frame none := by
  exact uniform_run 1 7 [true,false] frame

/-- The smallest uniform request has one possible answer and one width token. -/
theorem unit_control :
    ∃ used ≤ 12, tick^[used] (start true [false,false] frame) =
      state none [] [true] [true] [] [] frame none := by
  exact uniform_run 0 0 [] frame

/-- The same natural zero at direct-modulus entry rejects, with frame intact. -/
theorem zero_control :
    ∃ used ≤ 6, tick^[used] (start false [false,false] frame) =
      state none [] [] [] [] [] frame (some false) := by
  exact zero_rejected 0 [] frame

private def snapshot (cfg : Config) := (cfg.l,cfg.var,List.ofFn cfg.stk)

/-- Missing payload and missing slack delimiter both fail by executed transitions. -/
theorem malformed_control :
    snapshot (tick^[5] (start false [false,true,false] frame)) =
      (none,some false,[[],[],[],[],[],[true,false],[false],[true,true]]) ∧
    snapshot (tick^[3] (start true [true,true] frame)) =
      (none,some false,[[],[],[true,true],[],[],[true,false],[false],[true,true]]) := by
  decide +kernel

private def handler : QueryImpl BitOracleMachine.spec (StateT (List Bool) Id) := fun t =>
  match t with
  | .coin => fun tape => (tape.headD false,tape.tail)
  | .hash word => pure word

private def observe (fuel : Nat) (mode : Bool) (word tape : List Bool) :=
  (simulateQ handler ((fun out => (out.1.l,out.1.var,out.1.stk 1,out.1.stk 5)) <$>
    BitOracleMachine.run PreparedScalarMachine.code fuel (PreparedScalarMachine.startWord mode word))).run tape

/-- Preparation is in the same actual run as four coins, division and prefix writing. -/
theorem sampled_control :
    observe (PreparedScalarMachine.clock false 0 11) false (input 0 11 [])
      [false,true,true,false,true,false] =
      ((none,2,[true,true,false,true],[true,true,true,false,false,true,true]),[true,false]) := by
  unfold observe
  obtain ⟨charge,_,hr⟩ := PreparedScalarMachine.run_source false 0 11 (by decide)
  rw [hr]
  rfl

/-- Invalid zero and a valid prefix with an extra trailing bit cannot consume a coin. -/
theorem gate_control :
    (observe 20 false [false,false] [true,false]).2 = [true,false] ∧
    (observe 20 false [false,false] [true,false]).1.2.1 = 1 ∧
    (observe 30 true [false,false,true] [false,true]).2 = [false,true] ∧
    (observe 30 true [false,false,true] [false,true]).1.2.1 = 1 := by
  decide +kernel

/-- The physical unit-range run starts with blank work storage, returns zero,
and retains its one coin query even though that answer cannot affect the value. -/
theorem physical_control :
    let B := PreparedScalarMachine.cost false 0 1
    let T := BitOracleTapeCap.unitCost (4+B)*B*
      BitOraclePrimitiveLoop.globalFactor PreparedScalarMachine.code
    ∃ startup ≤ 24,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter 0)
        (BitOracleInitialInput.run PreparedScalarMachine.code 4
          (some (PreparedScalarMachine.entry false)) 0 (startup+T)
          (BitOracleInitialInput.initial [false,true,false,true])) =
      (fun _ => some (PreparedScalarMachine.result [false] [true])) <$>
        (liftM ((BitOracleLoopBounded.spec 0).query .coin)) := by
  dsimp only
  obtain ⟨startup,hs,he⟩ := PreparedScalarMachine.physical_run false 0 1 0 (by decide)
  obtain ⟨charge,_,hr⟩ := PreparedScalarMachine.run_source false 0 1 (by decide)
  refine ⟨startup,hs,?_⟩
  trans (fun out => some out.1) <$> simulateQ (BitOracleLoopBounded.adapter 0)
    (BitOracleMachine.run PreparedScalarMachine.code (PreparedScalarMachine.clock false 0 1)
      (PreparedScalarMachine.startWord false (input 0 1 [])))
  · exact he
  rw [hr]
  change (fun out => some out.1) <$>
    simulateQ (BitOracleLoopBounded.adapter 0)
      ((fun bits => (PreparedScalarMachine.result (uniformNatEncode (bitsValue bits % 1)) [true],charge bits)) <$>
        CoinWordLoader.word 1) = _
  simp [CoinWordLoader.word,BitOracleLoopBounded.adapter,Functor.map_map]
  congr 1
  funext a
  rw [Nat.mod_one]
  rfl

end ExplainableCrypto.Helios.Computational.SamplerOperandsControls
