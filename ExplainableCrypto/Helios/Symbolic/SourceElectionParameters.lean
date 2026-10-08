import ExplainableCrypto.Helios.Symbolic.SourceOpenVoterTemplate

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The exported key handle and two families of open vote parameters are
separate summands; application preserves the former as a variable. -/
abbrev ElectionParameter (n : Nat) := Fin 1 ⊕ (Fin 2 × Fin (n+1))

def voterInElectionParameters (ns : Names n) (i : Fin 2) : Option (Fin (n+1)) → Term (ElectionParameter n)
  | none => .unary .pk (.name ns.secretKey)
  | some j => .var (.inr (i,j))

def voterInElectionTemplate (ns : Names n) (i : Fin 2) : ScopedTermProgram (ElectionParameter n) :=
  (voterTemplate ns i).subst (voterInElectionParameters ns i)

def electionCandidateSubst (swap : Bool) (left right : CandidateSubstitution n Empty) :
    ElectionParameter n → Term (Fin 1)
  | .inl x => .var x
  | .inr (i,j) => Extended.groundTerm ((choice swap left right i).value j)

/-- All administration and voter binders are fresh for the candidates' full
terms. This also protects key/auxiliary scopes, not just the voter nonces. -/
def ElectionParametersFresh (ns : Names n) (left right : CandidateSubstitution n Empty) : Prop :=
  ∀ m ∈ ns.restricted, m ∉ candidateParameterNames left.value right.value

theorem voterInElectionTemplate_apply (ns : Names n) (i : Fin 2) (swap : Bool)
    (left right : CandidateSubstitution n Empty) :
    (voterInElectionTemplate ns i).subst (electionCandidateSubst swap left right) =
      (scopedVoterProgram ns i (choice swap left right i).value).subst (Empty.elim : Empty → Term (Fin 1)) := by
  rw [voterInElectionTemplate,← voterTemplate_apply,ScopedTermProgram.subst_subst,ScopedTermProgram.subst_subst]
  congr 1
  funext v
  cases v <;> rfl

theorem electionCandidateSubst_name_fresh (ns : Names n) (left right : CandidateSubstitution n Empty)
    (hf : ElectionParametersFresh ns left right) (swap : Bool) (m : Nat) (hm : m ∈ ns.restricted)
    (v : ElectionParameter n) : m ∉ (electionCandidateSubst swap left right v).nameSupport := by
  cases v with
  | inl x => exact Finset.notMem_empty _
  | inr ij =>
    obtain ⟨i,j⟩ := ij
    have hl : m ∉ (left.value j).nameSupport := fun h => hf m hm
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_union_left _ h⟩)
    have hr : m ∉ (right.value j).nameSupport := fun h => hf m hm
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_union_right _ h⟩)
    simp only [electionCandidateSubst,Extended.groundTerm_nameSupport]
    unfold General.choice
    split <;> cases swap <;> assumption

theorem voterInElectionTemplate_instantiates (ns : Names n) (left right : CandidateSubstitution n Empty)
    (hf : ElectionParametersFresh ns left right) (swap : Bool) (i : Fin 2) (channel : Nat) :
    Named.Instantiates (electionCandidateSubst swap left right)
      ((voterInElectionTemplate ns i).compile channel)
      (((scopedVoterProgram ns i (choice swap left right i).value).compile channel).rename Empty.elim) := by
  have hp : (voterInElectionTemplate ns i).FreshFor (electionCandidateSubst swap left right) := by
    intro m hm v
    rw [voterInElectionTemplate,ScopedTermProgram.names_subst,voterTemplate,scopedVoterComponents_names] at hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    apply electionCandidateSubst_name_fresh ns left right hf swap _ _ v
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
  simpa only [voterInElectionTemplate_apply,ScopedTermProgram.compile_ground_subst] using
    (voterInElectionTemplate ns i).compile_instantiates (electionCandidateSubst swap left right) channel hp

/-- Root candidate application preserves the public key's exported domain. -/
theorem electionCandidateSubst_key_domain (swap : Bool) (left right : CandidateSubstitution n Empty) (x : Fin 1) :
    electionCandidateSubst swap left right (.inl x) = .var x := rfl

theorem Named.Instantiates.restrictNames {V W : Type} {σ : V → Term W} {a : Named V} {b : Named W}
    (h : Named.Instantiates σ a b) (ns : List SourceName)
    (hf : ∀ u ∈ ns, ∀ v, u ∉ (σ v).nameSupport.image SourceName.base) :
    Named.Instantiates σ (Named.restrictNames ns a) (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact .newName n (hf n (by simp)) (ih (fun u hu v => hf u (by simp [hu]) v))

/-- The actual administration has no vote parameters. Variable substitution
leaves it unchanged, including all of its own future input binders. -/
theorem voterAdministration_instantiates (ns : Names n) (extra : Nat) (ch : Channels)
    (swap : Bool) (left right : CandidateSubstitution n Empty) :
    Named.Instantiates (electionCandidateSubst swap left right)
      ((voterAdministration ns extra ch).rename (Empty.elim : Empty → ElectionParameter n))
      ((voterAdministration ns extra ch).rename (Empty.elim : Empty → Fin 1)) := by
  let p := Agent.par (boardStart n extra ch (publicKey ns)) (trusteeAgent (n := n) ch (.name ns.secretKey))
  have h := Extended.Instantiates.plain (electionCandidateSubst swap left right)
    (p.subst (fun v : Empty => .var (Empty.elim v : ElectionParameter n)))
  have he : (fun v : Empty => electionCandidateSubst swap left right (Empty.elim v)) =
      (fun v : Empty => Term.var (Empty.elim v : Fin 1)) := by funext v; exact v.elim
  simpa only [voterAdministration,Named.rename,Extended.rename,Agent.subst_subst,Term.subst,he,p] using
    Named.Instantiates.embed h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
