import ExplainableCrypto.Helios.Computational.NativeRoundTripExecution

/-! Explicit allowed-reply and instruction bounds for one native oracle call.
Hash replies have the existing size contract; both actual coin values remain. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

/-- Hash support is exactly the existing length contract, with no additional
restriction on reply values. -/
theorem boundedCall_hash_support (limit : Nat) (query reply : List Bool) :
    reply ∈ support (boundedCall limit .hash query) ↔ reply.length ≤ limit := by
  let mx : OracleComp (BitOracleLoopBounded.spec limit)
      {word : List Bool // word.length ≤ limit} :=
    liftM ((BitOracleLoopBounded.spec limit).query (.hash query))
  change reply ∈ support (mx >>= fun a => pure a.val) ↔ _
  rw [mem_support_bind_iff]
  constructor
  · rintro ⟨a,_,ha⟩
    have he := OracleComp.eq_of_mem_support_pure a.val ha
    rw [he]
    exact a.property
  · intro hr
    exact ⟨⟨reply,hr⟩,OracleComp.mem_support_query _ _,by simp⟩


/-- Both coin values survive unchanged as singleton words. -/
theorem boundedCall_coin_support (limit : Nat) (query reply : List Bool) :
    reply ∈ support (boundedCall limit .coin query) ↔ ∃ bit : Bool, reply = [bit] := by
  let mx : OracleComp (BitOracleLoopBounded.spec limit)
      {bit : Bool // True} :=
    liftM ((BitOracleLoopBounded.spec limit).query .coin)
  change reply ∈ support (mx >>= fun a => pure [a.val]) ↔ _
  rw [mem_support_bind_iff]
  constructor
  · rintro ⟨a,_,ha⟩
    exact ⟨a.val,OracleComp.eq_of_mem_support_pure [a.val] ha⟩
  · rintro ⟨bit,rfl⟩
    exact ⟨⟨bit,trivial⟩,OracleComp.mem_support_query _ _,by simp⟩


/-- A common bound that covers the permitted hashes and the one-bit coin. -/
theorem boundedCall_length (limit : Nat) (kind : OracleTapeDispatch.Kind) (query reply : List Bool)
    (hr : reply ∈ support (boundedCall limit kind query)) : reply.length ≤ limit+1 := by
  cases kind with
  | hash => have := (boundedCall_hash_support limit query reply).mp hr; omega
  | coin => obtain ⟨bit,rfl⟩ := (boundedCall_coin_support limit query reply).mp hr; simp

/-- The native event's actual charged dispatch has the shared uniform bound. -/
theorem eventCost_le (limit : Nat) (kind : OracleTapeDispatch.Kind)
    (query oldAfter reply : List Bool) (hr : reply.length ≤ limit+1) :
    eventCost kind query oldAfter reply ≤ 2+query.length+oldAfter.length+(limit+1) := by
  cases kind <;> simp only [eventCost] <;> omega

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
