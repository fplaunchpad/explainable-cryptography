import ExplainableCrypto.Helios.Computational.CacheHashMachine
import ExplainableCrypto.Helios.Computational.CacheReadMachine

/-! Literal caller storage, executed copy, sampler and oracle-frame controls. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashMachineControls
open OracleComp OracleSpec BitOracleMachine CacheHashMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun request tape =>
  match request with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

private def key := [true,false]
private def cache := [false,true,true]
private def log := [true,true,false]
private def snapshot {l : Nat} (cfg : Config 12 l 3) := (cfg.l,cfg.var,List.ofFn cfg.stk)
private def observe (fuel : Nat) (record tape : List Bool) :
    (Option (Fin 47) × Fin 3 × List (List Bool)) × List Bool :=
  (simulateQ handler ((fun out => snapshot out.1) <$>
    run sampleCode fuel (sampleStart record key cache log))).run tape

/-- Initially only retained port eleven contains the record; all work is empty. -/
theorem initial_control :
    snapshot (sampleStart [false,true,false,true] key cache log) =
      (some 0,0,[[],[],[],[],[],[],[],[],[true,false],[false,true,true],
        [true,true,false],[false,true,false,true]]) := by
  decide +kernel

/-- Copying precedes actual coins/division/writing, with complete persistent storage. -/
theorem sampled_control :
    observe (sampleClock 0 11) (SamplerOperands.input 0 11 [])
      [false,true,true,false,true,false] =
      ((none,2,[[],[true,true,false,true],[],[],[],[true,true,true,false,false,true,true],[],[],
        [true,false],[false,true,true],[true,true,false],
        [false,true,true,true,true,false,true,true,false,true]]),[true,false]) := by
  unfold observe
  obtain ⟨charge,_,hr⟩ := sample_run 0 11 (by decide) key cache log
  rw [hr]
  simp only [Functor.map_map]
  rfl

/-- Both copies of the input survive the live return; no coin is queried yet. -/
theorem transfer_control :
    observe 10 [false,true,false,true] [true,false] =
      ((some 2,0,[[],[],[],[],[false,true,false,true],[],[],[],[true,false],
        [false,true,true],[true,true,false],[false,true,false,true]]),[true,false]) := by
  decide +kernel

/-- Direct zero still fails after copying, retaining all caller data and future coins. -/
theorem zero_control :
    observe 25 [false,false] [true,false] =
      ((none,1,[[],[],[],[],[],[],[],[],[true,false],[false,true,true],
        [true,true,false],[false,false]]),[true,false]) := by
  decide +kernel

private def layout : Fin 2 ⊕ Fin 1 ≃ Fin 3 :=
  finSumFinEquiv.trans (Equiv.swap 0 2)
private def hashCode : Code 2 1 1 := fun _ => .hash 0 1 0
private def source : Config 2 1 1 := ⟨some 0,0,![[true,false],[false]]⟩

/-- A permuted workspace sends the original request and replaces its reply port;
the nonempty private word and exact word-transfer charge are retained. -/
theorem hash_frame_control :
    (fun out => (List.ofFn out.1.stk,out.2)) <$>
      step (BitOracleStackFrame.code layout hashCode)
        (BitOracleStackFrame.embed layout source (fun _ => [true,true,false])) =
      (fun answer : List Bool => ([[true,true,false],answer,[true,false]],4+answer.length)) <$>
        liftM (spec.query (.hash [true,false])) := by
  rw [BitOracleStackFrame.step]
  simp only [step,hashCode,source,map_bind,map_pure]
  rfl

/-- Routing a coin to the retained port destroys a literal private word. -/
theorem misroute_control :
    let good := (simulateQ handler (step (BitOracleStackFrame.code layout (fun _ => .coin 1 0))
      (BitOracleStackFrame.embed layout source (fun _ => [true,true,false])))).run [false]
    let bad := (simulateQ handler (step (fun _ => .coin 0 0)
      (BitOracleStackFrame.embed layout source (fun _ => [true,true,false])))).run [false]
    good.1.1.stk 0 = [true,true,false] ∧ bad.1.1.stk 0 = [false] ∧ good.1.1.stk 0 ≠ bad.1.1.stk 0 := by
  decide +kernel

/-- A successful cache hit has real residual counter storage, even for one entry.
This excludes silently treating every routine return as an empty workspace. -/
theorem hit_counter_control :
    let cached : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
      AList.singleton BallotCacheCodecControls.key 6
    ∃ fuel ≤ CacheReadMachine.cost 23 11 1 ((ballotCacheBitCodec 23 11).encode cached).length,
      let cfg := CacheReadMachine.tick^[fuel] (CacheReadMachine.start
        ((ballotKeyBitCodec 23 11).encode BallotCacheCodecControls.key)
        ((ballotCacheBitCodec 23 11).encode cached))
      cfg.stk CacheReadMachine.digits = [false,true,true] ∧
        cfg.stk CacheLookupMachine.outer ≠ [] := by
  dsimp only
  obtain ⟨fuel,hf,n,tail,hr⟩ := CacheReadMachine.hit_run
    (AList.singleton BallotCacheCodecControls.key (6 : ZMod 11))
    BallotCacheCodecControls.key 6 (by decide)
  refine ⟨fuel,hf,?_⟩
  rw [hr]
  refine ⟨rfl,?_⟩
  change (n+1).bits ≠ []
  intro h
  have he := congrArg bitsValue h
  rw [bitsValue_bits] at he
  change n+1 = 0 at he
  omega

end ExplainableCrypto.Helios.Computational.CacheHashMachineControls
