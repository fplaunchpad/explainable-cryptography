import ExplainableCrypto.Helios.Symbolic.SourceProcessBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

namespace Formula
/-- Empty conjunction is encoded by the source equality ok=ok. -/
def all : List (Formula V) → Formula V
  | [] => .equal (.const .ok) (.const .ok)
  | f :: fs => .both f (all fs)

theorem all_holds (fs : List (Formula V)) (env : V → Ground) :
    (all fs).Holds env ↔ ∀ f ∈ fs, f.Holds env := by
  induction fs with
  | nil => simp [all,Holds,EqE.refl]
  | cons f fs ih => simp only [all,Holds,ih,List.mem_cons,forall_eq_or_imp]

theorem all_public (fs : List (Formula V)) (restricted : Finset Nat) :
    (all fs).Public restricted ↔ ∀ f ∈ fs, f.Public restricted := by
  induction fs with
  | nil => simp [all,Public,Term.Public]
  | cons f fs ih => simp only [all,Public,ih,List.mem_cons,forall_eq_or_imp]

theorem all_subst (fs : List (Formula V)) (σ : V → Term W) :
    (all fs).subst σ = all (fs.map (Formula.subst σ)) := by
  induction fs <;> simp_all [all,subst,Term.subst]
end Formula

/-- This is the finite source formula, not an abstract acceptance callback.
Every earlier/current candidate pair is checked, and snd^fieldCount is used
for the documented correction of the source's printed tuple-tail guard. -/
def electionGuard (n : Nat) (key : Term V) (board : List (Term V)) (b : Term V) : Formula V :=
  .both
    (.both
      (.equal (.ternary .checkspk key (aggregateCiphertext n b)
        (b.project (2 * (n+1)))) (.const .ok))
      (.all ((List.finRange (n+1)).map (fun i => .equal
        (.ternary .checkspk key (b.project i.val) (b.project (n+1+i.val))) (.const .ok)))))
    (.both (.equal (b.drop (fieldCount n)) (.const .bottom))
      (.all (board.map (fun earlier => .all ((List.finRange (n+1)).map (fun i =>
        .all ((List.finRange (n+1)).map (fun j =>
          .unequal (earlier.project i.val) (b.project j.val)))))))))

/-- Exact agreement for every ground environment and malformed as well as valid
ballot syntax. No publicness, freshness or successful-proof premise is needed. -/
theorem electionGuard_holds (n : Nat) (key : Term V) (board : List (Term V)) (b : Term V)
    (env : V → Ground) :
    (electionGuard n key board b).Holds env ↔
      Accepted n (key.subst env) (board.map (Term.subst env)) (b.subst env) := by
  simp [electionGuard,Formula.Holds,Formula.all_holds,Accepted,ProofValid,TailGuard,NoReuse,
    Term.subst,Term.subst_project,Term.subst_drop,aggregateCiphertext_subst]

theorem electionGuard_subst (n : Nat) (key : Term V) (board : List (Term V)) (b : Term V)
    (σ : V → Term W) :
    (electionGuard n key board b).subst σ =
      electionGuard n (key.subst σ) (board.map (Term.subst σ)) (b.subst σ) := by
  simp [electionGuard,Formula.subst,Formula.all_subst,List.map_map,Function.comp_def,
    Term.subst,Term.subst_project,Term.subst_drop,aggregateCiphertext_subst]

/-- The generated guard uses only the public key, board and received ballot
recipes. Every cross-candidate test obeys the same public-name policy. -/
theorem electionGuard_public (n : Nat) (key : Term V) (board : List (Term V)) (b : Term V)
    (restricted : Finset Nat) (hk : key.Public restricted) (hb : b.Public restricted)
    (hboard : ∀ earlier ∈ board, earlier.Public restricted) :
    (electionGuard n key board b).Public restricted := by
  unfold electionGuard
  refine ⟨⟨⟨⟨hk,aggregateCiphertext_public hb n,hb.project _⟩,trivial⟩,?_⟩,
    ⟨⟨hb.drop _,trivial⟩,?_⟩⟩
  · rw [Formula.all_public]
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨⟨hk,hb.project _,hb.project _⟩,trivial⟩
  · rw [Formula.all_public]
    intro f hf
    obtain ⟨earlier,he,rfl⟩ := List.mem_map.mp hf
    rw [Formula.all_public]
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    rw [Formula.all_public]
    intro f hf
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨(hboard earlier he).project _,hb.project _⟩

/-- A closed source guard is exactly the already checked Accepted predicate. -/
theorem electionGuard_ground (n : Nat) (key : Ground) (board : List Ground) (b : Ground) :
    (electionGuard n key board b).Holds Empty.elim ↔ Accepted n key board b := by
  have he : (Empty.elim : Empty → Ground) = Term.var := funext (fun v => v.elim)
  have hs : (Term.subst (Term.var : Empty → Ground)) = id := funext Term.subst_var
  simpa only [he,hs,Term.subst_var,List.map_id] using electionGuard_holds n key board b Empty.elim
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
