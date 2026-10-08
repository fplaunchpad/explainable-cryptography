import ExplainableCrypto.Helios.Computational.NativeWordCompiler
import ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe
import ExplainableCrypto.Helios.Computational.NativeAdaptiveSegments
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

/-! Combined mechanically generated adaptive execution. The target is exclusively
NativeWordCompiler.code NativeAdaptiveProbe.code; no handwritten target is used. -/
namespace ExplainableCrypto.Helios.Computational.NativeAdaptiveRun
open Turing OracleComp OracleSpec
open NativeWordCompiler
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private theorem empty_update (ws : Fin 6 → List Bool) (h : ws 4 = []) :
    Function.update ws (4 : Fin 6) [] = ws := by
  rw [← h]
  exact Function.update_eq_self _ _

private theorem oracle_prepare {l : Nat} (native : NativeOracleTape.Code l)
    (q next : Fin l) (kind : OracleTapeDispatch.Kind) (v : Fin 27)
    (hc : native q (heads v) = .oracle kind next)
    (ws : Fin 6 → List Bool) (ha : ws 4 = []) :
    BitOracleMachine.step (code native) ⟨some (commandLabel q v),v,ws⟩ =
      pure (⟨some (eventLabel q v),0,ws⟩,3) := by
  simp [BitOracleMachine.step,code_command,command,hc,TM2.stepAux,ha,
    head0,cellCode,BitOracleMachine.localCost,empty_update ws ha]

/-- Three actual generated ticks perform one native hash, with charge derived
from the entry, clearing instruction and actual oracle transfer. -/
theorem hash_run {l : Nat} (native : NativeOracleTape.Code l) (q next : Fin l)
    (hc : ∀ v, native q (heads v) = .oracle .hash next)
    (ws : Fin 6 → List Bool) (ha : ws 4 = []) :
    BitOracleMachine.run (code native) 3 (present (some q) ws) = (do
      let a ← liftM (BitOracleMachine.spec.query (.hash (ws 3)))
      pure (present (some next) (Function.update ws 5 a),
        8+(ws 3).length+(ws 5).length+a.length)) := by
  rw [BitOracleMachine.run,entry_step]
  simp only [pure_bind]
  rw [BitOracleMachine.run,oracle_prepare native q next .hash (snapshot ws) (hc _) ws ha]
  simp only [pure_bind]
  rw [BitOracleMachine.run]
  simp only [BitOracleMachine.step,code_event,event,hc,BitOracleMachine.resume,
    bind_assoc,pure_bind,BitOracleMachine.run,Nat.add_zero]
  refine bind_congr (fun (a : List Bool) => ?_)
  congr 1
  congr 1
  omega

/-- Coin replacement uses the same generated finite dispatcher and charges
clearing/replacement of the previous answer word. -/
theorem coin_run {l : Nat} (native : NativeOracleTape.Code l) (q next : Fin l)
    (hc : ∀ v, native q (heads v) = .oracle .coin next)
    (ws : Fin 6 → List Bool) (ha : ws 4 = []) :
    BitOracleMachine.run (code native) 3 (present (some q) ws) = (do
      let a ← liftM (BitOracleMachine.spec.query .coin)
      pure (present (some next) (Function.update ws 5 [a]),9+(ws 5).length)) := by
  rw [BitOracleMachine.run,entry_step]
  simp only [pure_bind]
  rw [BitOracleMachine.run,oracle_prepare native q next .coin (snapshot ws) (hc _) ws ha]
  simp only [pure_bind]
  rw [BitOracleMachine.run]
  simp only [BitOracleMachine.step,code_event,event,hc,BitOracleMachine.resume,
    bind_assoc,pure_bind,BitOracleMachine.run,Nat.add_zero]
  refine bind_congr (fun (a : Bool) => ?_)
  congr 1
  congr 1
  omega

abbrev program := NativeWordCompiler.code NativeAdaptiveProbe.code
abbrev State := NativeWordCompiler.Config 9

def words (before work query answer : List Bool) : Fin 6 → List Bool :=
  ![before,work,[],query,[],answer]

def start (before work input oldAnswer : List Bool) : State :=
  NativeWordCompiler.start 0 (words before work input oldAnswer)

def finish (before work input firstReply : List Bool) (coin : Bool)
    (secondReply : List Bool) : State :=
  present none (words before work (NativeAdaptiveProbe.dependentWord input firstReply coin) secondReply)

/-- Expected tree is calculated from the literal native instruction table. -/
def expected (before work input oldAnswer : List Bool) :
    OracleComp BitOracleMachine.spec (State × Nat) := do
  let firstReply ← liftM (BitOracleMachine.spec.query (.hash input))
  let coin ← liftM (BitOracleMachine.spec.query .coin)
  let secondReply ← liftM (BitOracleMachine.spec.query
    (.hash (NativeAdaptiveProbe.dependentWord input firstReply coin)))
  pure (finish before work input firstReply coin secondReply,
    66 + input.length + oldAnswer.length + 2*firstReply.length +
    (NativeAdaptiveProbe.dependentWord input firstReply coin).length + secondReply.length)

private theorem update_answer (wb wr qb qr ab ar a : List Bool) :
    Function.update (![wb,wr,qb,qr,ab,ar] : Fin 6 → List Bool) (5 : Fin 6) a =
      ![wb,wr,qb,qr,ab,a] := by
  funext k
  fin_cases k <;> simp [Function.update]

/-- The generated controller executes the exact native adaptive tree. All
private words and the complete final answer are retained. Both replies are
arbitrary; the charge comes from actual steps. -/
theorem exact_run (before work input oldAnswer : List Bool) :
    BitOracleMachine.run program 19 (start before work input oldAnswer) =
      expected before work input oldAnswer := by
  unfold start NativeWordCompiler.start expected
  rw [BitOracleReturnLink.run_add program 3 16,
    hash_run NativeAdaptiveProbe.code 0 1 (by intro v; rfl) _ (by rfl)]
  simp only [words,bind_assoc,pure_bind]
  refine bind_congr (fun (a : List Bool) => ?_)
  simp only [update_answer]
  have hb := NativeAdaptiveSegments.branch_move before work input a
  simp only [NativeAdaptiveSegments.words] at hb
  rw [BitOracleReturnLink.run_add program 4 12,hb]
  simp only [pure_bind]
  rw [BitOracleReturnLink.run_add program 3 9,
    coin_run NativeAdaptiveProbe.code 4 5 (by intro v; rfl) _ (by rfl)]
  simp only [update_answer,bind_assoc,pure_bind]
  refine bind_congr (fun (coin : Bool) => ?_)
  have hl := NativeAdaptiveSegments.coin_write_left before work input.tail (a.headD false) coin
  simp only [NativeAdaptiveSegments.words] at hl
  rw [BitOracleReturnLink.run_add program 4 5,hl]
  simp only [pure_bind]
  have hd : a.headD false::coin::input.tail.tail =
      NativeAdaptiveProbe.dependentWord input a coin := by
    cases input with
    | nil => rfl
    | cons bit rest => cases rest <;> rfl
  rw [hd]
  rw [BitOracleReturnLink.run_add program 3 2,
    hash_run NativeAdaptiveProbe.code 7 8 (by intro v; rfl) _ (by rfl)]
  simp only [bind_assoc,pure_bind]
  change (liftM (BitOracleMachine.spec.query (.hash
    (NativeAdaptiveProbe.dependentWord input a coin))) >>= _) = _
  refine bind_congr (fun (b : List Bool) => ?_)
  rw [update_answer,NativeAdaptiveSegments.halt_run]
  simp only [pure_bind,finish,words,NativeAdaptiveProbe.dependentWord,
    NativeAdaptiveProbe.branchBit]
  congr 1
  congr 1
  change 8+input.length+oldAnswer.length+a.length+
    (17+(9+a.length+(17+(8+([a.headD false,coin]++input.drop 2).length+1+b.length+6)))) = _
  omega

/-- Observation is defined only at target halt, so a partial or unsupported
run cannot masquerade as the intended native terminal state. -/
def observe (cfg : State) : Option (NativeOracleTape.Config 9) :=
  if cfg.l = none ∧ cfg.var = 0 then some (nativeConfig none cfg.stk) else none

theorem observe_finish (before work input firstReply : List Bool) (coin : Bool)
    (secondReply : List Bool) :
    observe (finish before work input firstReply coin secondReply) =
      some (NativeAdaptiveProbe.result (tape before work) input firstReply coin secondReply) := by
  simp only [observe,finish,present,Option.map_none,and_self,ite_true,words,
    nativeConfig,NativeAdaptiveProbe.result]
  rfl

/-- Source-level query-tree and complete-native-state correspondence.
Only the generated target's successful halted state can be observed. -/
theorem native_correspondence (before work input oldAnswer : List Bool) :
    (fun out => observe out.1) <$>
      BitOracleMachine.run program 19 (start before work input oldAnswer) =
    some <$> NativeOracleTape.run NativeAdaptiveProbe.code 8
      (NativeAdaptiveProbe.start (tape before work) (OracleTapeOutput.wordTape oldAnswer) input) := by
  rw [exact_run,NativeAdaptiveProbe.exact_run]
  simp only [expected,NativeAdaptiveProbe.expected,map_bind,map_pure]
  refine bind_congr (fun (a : List Bool) => ?_)
  refine bind_congr (fun (coin : Bool) => ?_)
  refine bind_congr (fun (b : List Bool) => ?_)
  exact congrArg pure (observe_finish before work input a coin b)

end ExplainableCrypto.Helios.Computational.NativeAdaptiveRun
