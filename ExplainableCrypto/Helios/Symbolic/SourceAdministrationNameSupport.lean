import ExplainableCrypto.Helios.Symbolic.SourceVoterScopeContext

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

/-- Syntactic absence of restricted base names in all plain-process payloads
and guards. Static channel names have a different source sort. -/
def Agent.BasePublic (restricted : Finset Nat) : {V : Type} → Agent V → Prop
  | _, .nil => True
  | _, .par p q => p.BasePublic restricted ∧ q.BasePublic restricted
  | _, .output _ m p => m.Public restricted ∧ p.BasePublic restricted
  | _, .input _ p => p.BasePublic restricted
  | _, .branch f p q => f.Public restricted ∧ p.BasePublic restricted ∧ q.BasePublic restricted

theorem Formula.public_name_absent (f : Formula V) (restricted : Finset Nat)
    (hf : f.Public restricted) (m : Nat) (hm : m ∈ restricted) : m ∉ f.nameSupport := by
  have term (t : Term V) (ht : t.Public restricted) : m ∉ t.nameSupport :=
    fun h => (Term.public_iff_nameSupport t restricted).mp ht m h hm
  induction f with
  | equal a b | unequal a b => exact fun h => (Finset.mem_union.mp h).elim (term a hf.1) (term b hf.2)
  | both a b ha hb => exact fun h => (Finset.mem_union.mp h).elim (ha hf.1) (hb hf.2)

theorem Agent.basePublic_name_absent (p : Agent V) (restricted : Finset Nat)
    (hp : p.BasePublic restricted) (m : Nat) (hm : m ∈ restricted) : .base m ∉ p.nameSupport := by
  have term {W : Type} (t : Term W) (ht : t.Public restricted) : m ∉ t.nameSupport :=
    fun h => (Term.public_iff_nameSupport t restricted).mp ht m h hm
  induction p with
  | nil => exact Finset.notMem_empty _
  | par p q ih jh => exact fun h => (Finset.mem_union.mp h).elim (ih hp.1) (jh hp.2)
  | output c t p ih => simpa [Agent.nameSupport] using And.intro (term t hp.1) (ih hp.2)
  | input c p ih => simpa [Agent.nameSupport] using ih hp
  | branch f p q ih jh =>
    simpa [Agent.nameSupport] using And.intro (f.public_name_absent restricted hp.1 m hm) ⟨ih hp.2.1,jh hp.2.2⟩

theorem shiftTerm_public {t : Term V} {restricted : Finset Nat} (h : t.Public restricted) :
    (shiftTerm t).Public restricted := Term.Public.subst t _ h (fun _ => trivial)

theorem boardTally_public (first second : Term V) (others : List (Term V)) (j : Fin (n+1))
    (restricted : Finset Nat) (hf : first.Public restricted) (hs : second.Public restricted)
    (ho : ∀ t ∈ others, t.Public restricted) : (boardTally first second others j).Public restricted := by
  have fold (xs : List (Term V)) (acc : Term V) (ha : acc.Public restricted)
      (hx : ∀ t ∈ xs, t.Public restricted) :
      (xs.foldl (fun a b => .binary .mul a (b.project j.val)) acc).Public restricted := by
    induction xs generalizing acc with
    | nil => exact ha
    | cons x xs ih => exact ih _ ⟨ha,(hx x (by simp)).project _⟩ (fun t ht => hx t (by simp [ht]))
  exact fold others _ ⟨hf.project _,hs.project _⟩ ho

theorem boardFinish_basePublic (ch : Channels) (first second : Term V) (others : List (Term V))
    (restricted : Finset Nat) (hf : first.Public restricted) (hs : second.Public restricted)
    (ho : ∀ t ∈ others, t.Public restricted) :
    (boardFinish (n := n) ch first second others).BasePublic restricted := by
  have ht : (tallyMessage (n := n) first second others).Public restricted :=
    candidateTuple_public _ (fun j => boardTally_public first second others j restricted hf hs ho)
  exact ⟨ht,trivial,candidateTuple_public _ (fun j =>
    ⟨(show (Term.var (none : Option V)).Public restricted from trivial).project _,(shiftTerm_public ht).project _⟩),trivial⟩

theorem collectBallots_basePublic (n : Nat) (ch : Channels) (remaining : Nat)
    (key first second : Term V) (others : List (Term V)) (restricted : Finset Nat)
    (hk : key.Public restricted) (hf : first.Public restricted) (hs : second.Public restricted)
    (ho : ∀ t ∈ others, t.Public restricted) :
    (collectBallots n ch remaining key first second others).BasePublic restricted := by
  induction remaining generalizing V with
  | zero => exact boardFinish_basePublic ch first second others restricted hf hs ho
  | succ remaining ih =>
    refine ⟨electionGuard_public n _ _ _ restricted (shiftTerm_public hk) trivial ?_,
      ih _ _ _ _ (shiftTerm_public hk) (shiftTerm_public hf) (shiftTerm_public hs) ?_,trivial⟩
    · intro t ht
      simp only [List.mem_cons,List.mem_map] at ht
      rcases ht with rfl | rfl | ⟨u,hu,rfl⟩
      · exact shiftTerm_public hf
      · exact shiftTerm_public hs
      · exact shiftTerm_public (ho u hu)
    · intro t ht
      simp only [List.mem_append,List.mem_map,List.mem_singleton] at ht
      rcases ht with ⟨u,hu,rfl⟩ | rfl
      · exact shiftTerm_public (ho u hu)
      · trivial

theorem boardStart_basePublic (n extra : Nat) (ch : Channels) (key : Term V)
    (restricted : Finset Nat) (hk : key.Public restricted) :
    (boardStart n extra ch key).BasePublic restricted := by
  refine ⟨trivial,trivial,?_⟩
  exact collectBallots_basePublic n ch extra _ _ _ [] restricted
    (shiftTerm_public (shiftTerm_public hk)) (by trivial) (by trivial) (by simp)

theorem trusteeAgent_basePublic (ch : Channels) (secret : Term V) (restricted : Finset Nat)
    (hs : secret.Public restricted) : (trusteeAgent (n := n) ch secret).BasePublic restricted :=
  ⟨candidateTuple_public _ (fun _ => ⟨shiftTerm_public hs,
    (show (Term.var (none : Option V)).Public restricted from trivial).project _⟩),trivial⟩

/-- The real administration body contains its secret-key name and static
channels, but no honest voter nonce, for every candidate and voter count. -/
def voterAdministration (ns : Names n) (extra : Nat) (ch : Channels) : Named Empty :=
  .embed (.plain (.par (boardStart n extra ch (publicKey ns)) (trusteeAgent (n := n) ch (.name ns.secretKey))))

theorem voterAdministration_nonce_fresh (ns : Names n) (hf : ns.Fresh) (extra : Nat) (ch : Channels) :
    ∀ u ∈ voterNonceList ns 0 ++ voterNonceList ns 1, u ∉ (voterAdministration ns extra ch).freeNames := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  all_goals obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
  all_goals
    apply Agent.basePublic_name_absent _ {_} _ _ (Finset.mem_singleton_self _)
    constructor
    · apply boardStart_basePublic
      simpa only [publicKey,Term.Public,Finset.mem_singleton] using (hf.2.2 _ j).1.symm
    · apply trusteeAgent_basePublic
      simpa only [Term.Public,Finset.mem_singleton] using (hf.2.2 _ j).1.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
