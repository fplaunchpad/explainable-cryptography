import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedOutput
import ExplainableCrypto.Helios.Symbolic.SourceJointHandleOutput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Distinct fresh voter nonces distinguish whole ballots, even for equal
candidate values. The first ciphertext suffices to witness the difference. -/
theorem fresh_ballots_distinct (ns : Names n) (hf : ns.Fresh) (i j : Fin 2) (hij : i ≠ j)
    (values values' : Fin (n+1) → Ground) : ¬ EqE (ballot ns i values) (ballot ns j values') := by
  intro he
  have hc := (ballot_project_ciphertext ns i values 0).symm.trans
    ((EqE.unary .fst (he.drop 0)).trans (ballot_project_ciphertext ns j values' 0))
  have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  have hpair : (i,(0 : Fin (n+1))) = (j,0) := hf.2.1 hn
  exact hij (congrArg Prod.fst hpair)

/-- A candidate tuple has n+1 cells; a ballot has 2(n+1)+1 cells. Full E
preserves those lengths regardless of any reductions inside the fields. -/
theorem candidateTuple_not_ballot (values : Fin (n+1) → Ground) (ns : Names n)
    (i : Fin 2) (votes : Fin (n+1) → Ground) : ¬ EqE (candidateTuple values) (ballot ns i votes) := by
  intro he
  have hl := he.tuple_length
  change ((List.finRange (n+1)).map values).length = (ballotFields ns i votes).length at hl
  rw [List.length_map,List.length_finRange,ballot_fields_length] at hl
  unfold fieldCount at hl
  omega

/-- A candidate tuple is distinct from every initial key/ballot handle. -/
theorem candidateTuple_not_initial_handle (values : Fin (n+1) → Ground) (ns : Names n)
    (swap : Bool) (left right : CandidateSubstitution n Empty) (i : Fin 3) :
    ¬ EqE (candidateTuple values) ((frame ns swap left right).value i) := by
  fin_cases i
  · exact tuple_not_eqE_pk _ _
  · exact candidateTuple_not_ballot values ns 0 _
  · exact candidateTuple_not_ballot values ns 1 _

/-- Numeric results cannot equal the previously published trustee-partial
vector. The complete first components have incompatible E-value shapes. -/
theorem source_results_not_partials (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) :
    ¬ EqE (sourceResults ns swap left right rs) (sourcePartials ns swap left right rs) := by
  intro he
  have ht := (sourceResults_eqE ns swap left right rs).symm.trans
    (he.trans (sourcePartials_eqE ns swap left right rs))
  have hv := (candidateTuple_project (tallyResult ns swap left right rs) 0).symm.trans
    ((EqE.unary .fst (ht.drop 0)).trans (candidateTuple_project (tallyPartial ns swap left right rs) 0))
  obtain ⟨number,hnum⟩ := hn 0
  exact (numeric_not_data_shapes number).2.2 ⟨_,_,hnum.symm.trans hv⟩

/-- Every actual publication in a reached fresh election differs modulo E
from every old handle. Acceptance supplies numeric result separation. -/
theorem Publication.old_handle_distinct {ns : Names n} (hf : ns.Fresh)
    {swap : Bool} {left right : CandidateSubstitution n Empty} {extra handle : Nat}
    {phase next : Process.Phase} {m : Ground}
    (hp : Publication ns swap left right extra phase handle m next)
    (hr : Process.Reachable ns swap left right extra phase) (i : Fin phase.handles) :
    ¬ EqE ((sourceView ns swap left right phase).value i) m := by
  cases hp with
  | first =>
    fin_cases i
    exact fun he => tuple_not_eqE_pk _ _ he.symm
  | second =>
    fin_cases i
    · exact fun he => tuple_not_eqE_pk _ _ he.symm
    · exact fresh_ballots_distinct ns hf 0 1 (by decide) _ _
  | partials =>
    intro he
    exact candidateTuple_not_initial_handle _ ns swap left right i
      ((sourcePartials_eqE ns swap left right _).symm.trans he.symm)
  | results =>
    rename_i rs
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro he
      have hw := (hr.swap hf false).wellFormed
      exact source_results_not_partials ns swap left right rs
        (accepted_expanded_results_numeric ns hf left right rs hw.publicHistory hw.accepted swap) he.symm
    · intro he
      simp only [sourceView,sourcePartialFrame,Frame.extend_old] at he
      exact candidateTuple_not_initial_handle _ ns swap left right j
        ((sourceResults_eqE ns swap left right rs).symm.trans he.symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
