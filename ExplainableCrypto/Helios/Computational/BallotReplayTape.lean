import ExplainableCrypto.Helios.Computational.BallotReplayCost
import PolyFun.PFunctor.Free.Path.Bounded

/-! Finite saved replay input using PolyFun's existing tagged event list.
Decoding reconstructs a path against the source program and rejects malformed
or trailing input. The source itself remains an OracleComp. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
open PFunctor.FreeM
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

variable {P : PFunctor.{0,0}} {A : Type} [DecidableEq P.A]

/-- Decode a complete tagged tape. Each tag is checked before transporting its
answer to the actual query's answer type. Pure leaves require an empty tape. -/
def ballotReplayReadTape : (oa : PFunctor.FreeM P A) → PFunctor.TraceList P →
    Option (Path oa)
  | .pure _, [] => some ⟨⟩
  | .pure _, _ :: _ => none
  | .liftBind _ _, [] => none
  | .liftBind t next, ⟨u,answer⟩ :: tail =>
      if h : u = t then
        let a : P.B t := h ▸ answer
        (ballotReplayReadTape (next a) tail).map (fun p => ⟨a,p⟩)
      else none

/-- Every actual path reconstructs exactly, with no reachability premise. -/
theorem ballotReplayReadTape_trace (oa : PFunctor.FreeM P A) (path : Path oa) :
    ballotReplayReadTape oa (Path.trace oa path) = some path := by
  induction oa with
  | pure x => cases path; rfl
  | lift_bind t next ih =>
    change ballotReplayReadTape (.liftBind t next) (Path.trace (.liftBind t next) path) = some path
    rcases path with ⟨a,tail⟩
    rw [show Path.trace (.liftBind t next) ⟨a,tail⟩ =
      (⟨t,a⟩ :: Path.trace (next a) tail) from rfl,ballotReplayReadTape,dif_pos rfl]
    change (ballotReplayReadTape (next a) (Path.trace (next a) tail)).map
      (fun p => (⟨a,p⟩ : Path (.liftBind t next))) = some ⟨a,tail⟩
    rw [ih a tail]
    rfl

/-- Successful decoding consumes exactly the supplied tape; no suffix is ignored. -/
theorem ballotReplayReadTape_exact (oa : PFunctor.FreeM P A)
    (tape : PFunctor.TraceList P) (path : Path oa)
    (h : ballotReplayReadTape oa tape = some path) : Path.trace oa path = tape := by
  induction oa generalizing tape with
  | pure x =>
    cases tape with
    | nil => rfl
    | cons head tail =>
      change (none : Option (Path (.pure x : PFunctor.FreeM P A))) = some path at h
      cases h
  | lift_bind t next ih =>
    change ballotReplayReadTape (.liftBind t next) tape = some path at h
    change Path.trace (.liftBind t next) path = tape
    cases tape with
    | nil => simp [ballotReplayReadTape] at h
    | cons head tail =>
      rcases head with ⟨u,a⟩
      by_cases he : u = t
      · subst u
        rw [ballotReplayReadTape,dif_pos rfl] at h
        change (ballotReplayReadTape (next a) tail).map
          (fun p => (⟨a,p⟩ : Path (.liftBind t next))) = some path at h
        obtain ⟨suffix,hs,hp⟩ := Option.map_eq_some_iff.mp h
        subst path
        change (⟨t,a⟩ :: Path.trace (next a) suffix) = (⟨t,a⟩ :: tail)
        exact congrArg (List.cons ⟨t,a⟩) (ih a tail suffix hs)
      · simp [ballotReplayReadTape,he] at h

/-- Collect the finite tape directly while executing the source once. -/
def ballotReplayCollectTape : (oa : PFunctor.FreeM P A) →
    PFunctor.FreeM P (PFunctor.TraceList P)
  | .pure _ => .pure []
  | .liftBind t next => .liftBind t fun a =>
      PFunctor.FreeM.map (List.cons ⟨t,a⟩) (ballotReplayCollectTape (next a))

omit [DecidableEq P.A] in
/-- Direct tape collection has the same random computation as erasing the
existing typed path. It adds no random queries or fresh source run. -/
theorem ballotReplayCollectTape_eq (oa : PFunctor.FreeM P A) :
    ballotReplayCollectTape oa = PFunctor.FreeM.map (Path.trace oa) (PFunctor.FreeM.withPath oa) := by
  induction oa with
  | pure x => rfl
  | lift_bind t next ih =>
    change ballotReplayCollectTape (.liftBind t next) =
      PFunctor.FreeM.map (Path.trace (.liftBind t next)) (PFunctor.FreeM.withPath (.liftBind t next))
    simp only [ballotReplayCollectTape,PFunctor.FreeM.withPath,PFunctor.FreeM.map]
    apply congrArg (PFunctor.FreeM.liftBind t)
    funext a
    rw [ih a,← PFunctor.FreeM.comp_map,← PFunctor.FreeM.comp_map]
    rfl

omit [DecidableEq P.A] in
/-- Every saved tape has at most as many entries as the source's total-query
bound. This counts entries, not encoded bits or decoding time. -/
theorem ballotReplayCollectTape_length_le {ι : Type} {spec : OracleSpec.{0,0} ι}
    (oa : OracleComp spec A) (m : Nat) (hb : oa.IsTotalQueryBound m)
    (tape : PFunctor.TraceList spec.toPFunctor)
    (ht : tape ∈ support (ballotReplayCollectTape oa : OracleComp spec _)) :
    tape.length ≤ m := by
  have he : (ballotReplayCollectTape oa : OracleComp spec _) =
      Path.trace oa <$> replayFirstPath oa := ballotReplayCollectTape_eq oa
  rw [he,support_map] at ht
  obtain ⟨path,_,rfl⟩ := ht
  rw [← Path.length_eq_trace_length]
  exact Path.length_le_of_isTotalRollBound oa hb path

#print axioms ballotReplayReadTape_trace
#print axioms ballotReplayReadTape_exact
#print axioms ballotReplayCollectTape_eq
#print axioms ballotReplayCollectTape_length_le
end ExplainableCrypto.Helios.Computational
