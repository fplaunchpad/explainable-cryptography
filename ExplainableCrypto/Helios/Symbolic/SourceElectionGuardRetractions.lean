import ExplainableCrypto.Helios.Symbolic.SourceRetractionSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceRetractedInterpretation

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem Term.NameRetracts.drop {b : Term V} {f g : Nat → Nat}
    (h : b.NameRetracts f g) (i : Nat) : (b.drop i).NameRetracts f g := by
  induction i generalizing b with
  | zero => exact h
  | succ i ih => exact ih (h.unary .snd)

theorem Term.NameRetracts.project {b : Term V} {f g : Nat → Nat}
    (h : b.NameRetracts f g) (i : Nat) : (b.project i).NameRetracts f g :=
  (h.drop i).unary .fst

theorem aggregateCiphertext_nameRetracts {b : Term V} {f g : Nat → Nat}
    (hb : b.NameRetracts f g) (n : Nat) : (aggregateCiphertext n b).NameRetracts f g := by
  have fold (is : List (Fin n)) (acc : Term V) (ha : acc.NameRetracts f g) :
      (is.foldl (fun a i => Term.binary .mul a (b.project (i.val+1))) acc).NameRetracts f g := by
    induction is generalizing acc with
    | nil => exact ha
    | cons i is ih => exact ih _ (ha.binary .mul (hb.project _))
  exact fold _ _ (hb.project 0)

namespace Historical.General.Source

theorem Formula.NameRetracts.all (fs : List (Formula V)) (f g : Nat → Nat)
    (h : ∀ p ∈ fs, p.NameRetracts f g) : (Formula.all fs).NameRetracts f g := by
  induction fs with
  | nil => exact Formula.EquivE.equal (.refl _) (.refl _)
  | cons p ps ih =>
    exact Formula.EquivE.both (h p (by simp)) (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-- Recovering the public key and complete board/incoming terms recovers the
literal finite guard, including every proof, tail and cross-candidate replay test.
Malformed terms and both guard outcomes are included. -/
theorem electionGuard_nameRetracts (n : Nat) (key : Term V) (board : List (Term V)) (b : Term V)
    (f g : Nat → Nat) (hk : key.NameRetracts f g) (hb : b.NameRetracts f g)
    (hboard : ∀ earlier ∈ board, earlier.NameRetracts f g) :
    (electionGuard n key board b).NameRetracts f g := by
  unfold electionGuard
  refine Formula.EquivE.both (Formula.EquivE.both
    (Formula.EquivE.equal (hk.ternary .checkspk (aggregateCiphertext_nameRetracts hb n) (hb.project _)) (.refl _)) ?_)
    (Formula.EquivE.both (Formula.EquivE.equal (hb.drop _) (.refl _)) ?_)
  · apply Formula.NameRetracts.all
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact Formula.EquivE.equal (hk.ternary .checkspk (hb.project _) (hb.project _)) (.refl _)
  · apply Formula.NameRetracts.all
    intro p hp
    obtain ⟨earlier,he,rfl⟩ := List.mem_map.mp hp
    apply Formula.NameRetracts.all
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    apply Formula.NameRetracts.all
    intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact Formula.EquivE.unequal ((hboard earlier he).project _) (hb.project _)

theorem electionGuard_holds_mapNames_of_retractions (n : Nat) (key : Ground)
    (board : List Ground) (b : Ground) (f g : Nat → Nat)
    (hk : key.NameRetracts f g) (hb : b.NameRetracts f g)
    (hboard : ∀ earlier ∈ board, earlier.NameRetracts f g) :
    ((electionGuard n key board b).mapNames f).Holds Empty.elim ↔
      (electionGuard n key board b).Holds Empty.elim :=
  (electionGuard_nameRetracts n key board b f g hk hb hboard).holds_mapNames

/-- Full check-state Tau transport with a semantic premise on the key, both
honest ballots, accepted history and incoming message, not their raw name union. -/
theorem residual_check_tau_mapNames_of_retractions (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) (r : Recipe 3) (f g k : Nat → Nat)
    (hk : (publicKey ns).NameRetracts f g)
    (hb : ((frame ns swap left right).eval r).NameRetracts f g)
    (hboard : ∀ earlier ∈ ballot ns 0 (choice swap left right 0).value ::
      ballot ns 1 (choice swap left right 1).value :: receivedBallots ns swap left right rs,
      earlier.NameRetracts f g)
    {q : Agent Empty} (h : Agent.Tau (residual ns swap left right extra ch (.check rs r)) q) :
    Agent.Tau ((residual ns swap left right extra ch (.check rs r)).mapNames f k) (q.mapNames f k) :=
  h.mapNames_of_guard_retractions f g k
    ⟨electionGuard_nameRetracts n _ _ _ f g hk hb hboard,trivial⟩

end Historical.General.Source
end ExplainableCrypto.Helios.Symbolic
