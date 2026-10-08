import ExplainableCrypto.Helios.Computational.BitCompareMachine

/-! Concrete copying needed to preserve query/cache data during destructive
local operations. Exact TM2 runs retain complete source and destination words. -/
namespace ExplainableCrypto.Helios.Computational
namespace BitCopyMachine
open Turing.TM2

inductive Stack where
  | source | destination | scratch
  deriving DecidableEq
open Stack

instance : Fintype Stack where
  elems := {source,destination,scratch}
  complete x := by cases x <;> simp

abbrev Config := Cfg (fun _ : Stack => Bool) Bool (Option Bool)

def program : Bool → Stmt (fun _ : Stack => Bool) Bool (Option Bool)
  | false => .pop source (fun _ b => b) <|
      .branch Option.isSome
        (.push scratch (fun b => b.getD false) (.goto (fun _ => false)))
        (.goto (fun _ => true))
  | true => .pop scratch (fun _ b => b) <|
      .branch Option.isSome
        (.push source (fun b => b.getD false)
          (.push destination (fun b => b.getD false) (.goto (fun _ => true)))) .halt

def config (phase : Option Bool) (xs ys zs : List Bool) (v : Option Bool := none) : Config :=
  ⟨phase,v,fun k => match k with
    | source => xs | destination => ys | scratch => zs⟩

def tick (c : Config) : Config := (step program c).getD c

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro q _
    cases q <;> simp [program,SupportsStmt]

private theorem source_step (xs ys zs : List Bool) (v : Option Bool) :
    tick (config (some false) xs ys zs v) = match xs with
      | [] => config (some true) [] ys zs
      | b::bs => config (some false) bs ys (b::zs) (some b) := by
  cases xs with
  | nil => simp [tick,config,program,stepAux,Function.update]
  | cons b bs =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp

private theorem scratch_step (xs ys zs : List Bool) (v : Option Bool) :
    tick (config (some true) xs ys zs v) = match zs with
      | [] => config none xs ys []
      | b::bs => config (some true) (b::xs) (b::ys) bs (some b) := by
  cases zs with
  | nil => simp [tick,config,program,stepAux,Function.update]
  | cons b bs =>
    simp [tick,config,program,stepAux]
    funext k
    cases k <;> simp

private theorem collect_run (xs ys zs : List Bool) (v : Option Bool) :
    tick^[xs.length+1] (config (some false) xs ys zs v) =
      config (some true) [] ys (xs.reverse ++ zs) := by
  induction xs generalizing zs v with
  | nil => simp [source_step]
  | cons b xs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,source_step,ih]
    simp

private theorem restore_run (xs ys zs : List Bool) (v : Option Bool) :
    tick^[zs.length+1] (config (some true) xs ys zs v) =
      config none (zs.reverse ++ xs) (zs.reverse ++ ys) [] := by
  induction zs generalizing xs ys v with
  | nil => simp [scratch_step]
  | cons b zs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,scratch_step,ih]
    simp

/-- Exact complete configuration after both passes, for every initial local
memory and destination suffix. Empty scratch is the explicit workspace invariant. -/
theorem run (xs ys : List Bool) (v : Option Bool) :
    tick^[2*xs.length+2] (config (some false) xs ys [] v) =
      config none xs (xs ++ ys) [] := by
  have hn : 2*xs.length+2 = (xs.length+1)+(xs.length+1) := by omega
  rw [hn,Function.iterate_add_apply,collect_run]
  simpa using restore_run [] ys xs.reverse none

/-- Copy a complete query key while retaining its original encoded word. -/
theorem key_copy {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q)) (suffix : List Bool) :
    ∃ fuel ≤ 2*keyRecordBitBound p+2,
      tick^[fuel] (config (some false) ((ballotKeyBitCodec p q).encode key) suffix []) =
        config none ((ballotKeyBitCodec p q).encode key)
          (((ballotKeyBitCodec p q).encode key) ++ suffix) [] := by
  refine ⟨_,?_,run _ _ none⟩
  have h := ballotKeyBits_length_le key
  omega

open OracleComp OracleSpec

/-- Copy the complete cache in an actual supported explicit-source result.
Its query bound derives the word-length bound; no cache-size or machine-cost
certificate is assumed. Initial encoding/loading remains outside this run. -/
theorem source_cache_copy {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[])))
    (suffix : List Bool) :
    ∃ fuel ≤ 2*cacheRecordBitBound p q (n+15)+2,
      tick^[fuel] (config (some false) ((ballotCacheBitCodec p q).encode out.2.1) suffix []) =
        config none ((ballotCacheBitCodec p q).encode out.2.1)
          (((ballotCacheBitCodec p q).encode out.2.1) ++ suffix) [] := by
  refine ⟨_,?_,run _ _ none⟩
  have h := repairedSubmissionPrime_cache_bits_le g pk vote attacker n hb out ho
  omega

/-- Copying preserves an existing suffix and the source's nonpalindromic order. -/
theorem copy_control :
    tick^[6] (config (some false) [true,false] [false,true] []) =
      config none [true,false] [true,false,false,true] [] := by
  exact run [true,false] [false,true] none

/-- An empty source still executes both end checks and preserves the suffix. -/
theorem empty_control :
    tick^[2] (config (some false) [] [true] [] (some false)) =
      config none [] [true] [] := by
  exact run [] [true] (some false)

/-- A single reversed pass is not a completed copy. -/
theorem first_pass_not_copy :
    let out := tick^[3] (config (some false) [true,false] [true] [])
    out.l = some true ∧ out.stk source = [] ∧ out.stk scratch = [false,true] ∧
      out.stk destination = [true] := by decide

/-- Finished copying neither reverses the destination nor destroys the source. -/
theorem no_erasure_or_reversal :
    let out := tick^[6] (config (some false) [true,false] [] [])
    out.stk source ≠ [] ∧ out.stk destination ≠ [false,true] := by decide

#print axioms supports
#print axioms run
#print axioms key_copy
#print axioms source_cache_copy
#print axioms copy_control
#print axioms empty_control
#print axioms first_pass_not_copy
#print axioms no_erasure_or_reversal
end BitCopyMachine
end ExplainableCrypto.Helios.Computational
