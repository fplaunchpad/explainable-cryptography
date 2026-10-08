import ExplainableCrypto.Helios.Symbolic.SPOT
import ExplainableCrypto.Helios.Symbolic.Ballot
import ExplainableCrypto.Helios.Symbolic.RewriteSPOT
import ExplainableCrypto.Helios.Symbolic.HomomorphicOverlap

#check ExplainableCrypto.Helios.Symbolic.Term.subst_var
#print axioms ExplainableCrypto.Helios.Symbolic.Term.subst_var
#check ExplainableCrypto.Helios.Symbolic.Term.subst_subst
#print axioms ExplainableCrypto.Helios.Symbolic.Term.subst_subst
#check ExplainableCrypto.Helios.Symbolic.Equation.subst
#print axioms ExplainableCrypto.Helios.Symbolic.Equation.subst
#check ExplainableCrypto.Helios.Symbolic.EqE.subst
#print axioms ExplainableCrypto.Helios.Symbolic.EqE.subst
#check ExplainableCrypto.Helios.Symbolic.Term.subst_congr
#print axioms ExplainableCrypto.Helios.Symbolic.Term.subst_congr
#check ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.refl
#print axioms ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.refl
#check ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.symm
#print axioms ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.symm
#check ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.trans
#print axioms ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.trans
#check ExplainableCrypto.Helios.Symbolic.Frame.staticEq_of_pointwise
#print axioms ExplainableCrypto.Helios.Symbolic.Frame.staticEq_of_pointwise
#check ExplainableCrypto.Helios.Symbolic.Term.Public.subst
#print axioms ExplainableCrypto.Helios.Symbolic.Term.Public.subst
#check ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.derive
#print axioms ExplainableCrypto.Helios.Symbolic.Frame.StaticEq.derive
#check ExplainableCrypto.Helios.Symbolic.Equation.denote
#print axioms ExplainableCrypto.Helios.Symbolic.Equation.denote
#check ExplainableCrypto.Helios.Symbolic.EqE.denote
#print axioms ExplainableCrypto.Helios.Symbolic.EqE.denote
#check ExplainableCrypto.Helios.Symbolic.zero_not_one
#print axioms ExplainableCrypto.Helios.Symbolic.zero_not_one
#check ExplainableCrypto.Helios.Symbolic.two_not_one
#print axioms ExplainableCrypto.Helios.Symbolic.two_not_one
#check ExplainableCrypto.Helios.Symbolic.combined_zero_one
#print axioms ExplainableCrypto.Helios.Symbolic.combined_zero_one
#check ExplainableCrypto.Helios.Symbolic.aggregate_example
#print axioms ExplainableCrypto.Helios.Symbolic.aggregate_example
#check ExplainableCrypto.Helios.Symbolic.aggregate_permutation
#print axioms ExplainableCrypto.Helios.Symbolic.aggregate_permutation
#check ExplainableCrypto.Helios.Symbolic.partial_decryption_observable
#print axioms ExplainableCrypto.Helios.Symbolic.partial_decryption_observable
#check ExplainableCrypto.Helios.Symbolic.honest_tally_swap
#print axioms ExplainableCrypto.Helios.Symbolic.honest_tally_swap
#check ExplainableCrypto.Helios.Symbolic.public_handle_allowed
#print axioms ExplainableCrypto.Helios.Symbolic.public_handle_allowed
#check ExplainableCrypto.Helios.Symbolic.secret_name_forbidden
#print axioms ExplainableCrypto.Helios.Symbolic.secret_name_forbidden
#check ExplainableCrypto.Helios.Symbolic.public_name_allowed
#print axioms ExplainableCrypto.Helios.Symbolic.public_name_allowed
#check ExplainableCrypto.Helios.Symbolic.replay_recipe_allowed
#print axioms ExplainableCrypto.Helios.Symbolic.replay_recipe_allowed
#check ExplainableCrypto.Helios.Symbolic.published_bit_distinguishable
#print axioms ExplainableCrypto.Helios.Symbolic.published_bit_distinguishable
#check ExplainableCrypto.Helios.Symbolic.reduced_bit_staticEq
#print axioms ExplainableCrypto.Helios.Symbolic.reduced_bit_staticEq
#check ExplainableCrypto.Helios.Symbolic.EqE.drop
#print axioms ExplainableCrypto.Helios.Symbolic.EqE.drop
#check ExplainableCrypto.Helios.Symbolic.drop_tuple
#print axioms ExplainableCrypto.Helios.Symbolic.drop_tuple
#check ExplainableCrypto.Helios.Symbolic.next_projection_tuple
#print axioms ExplainableCrypto.Helios.Symbolic.next_projection_tuple
#check ExplainableCrypto.Helios.Symbolic.fst_bottom_not_bottom
#print axioms ExplainableCrypto.Helios.Symbolic.fst_bottom_not_bottom
#check ExplainableCrypto.Helios.Symbolic.canonical_tuple_fails_printed_guard
#print axioms ExplainableCrypto.Helios.Symbolic.canonical_tuple_fails_printed_guard
#check ExplainableCrypto.Helios.Symbolic.drop_tupleWithTail
#print axioms ExplainableCrypto.Helios.Symbolic.drop_tupleWithTail
#check ExplainableCrypto.Helios.Symbolic.extra_bottom_passes_printed_guard
#print axioms ExplainableCrypto.Helios.Symbolic.extra_bottom_passes_printed_guard
#check ExplainableCrypto.Helios.Symbolic.canonical_tuple_passes_tail_guard
#print axioms ExplainableCrypto.Helios.Symbolic.canonical_tuple_passes_tail_guard
#check ExplainableCrypto.Helios.Symbolic.project_tuple_get
#print axioms ExplainableCrypto.Helios.Symbolic.project_tuple_get
#check ExplainableCrypto.Helios.Symbolic.oneCandidate_proofs_valid
#print axioms ExplainableCrypto.Helios.Symbolic.oneCandidate_proofs_valid
#check ExplainableCrypto.Helios.Symbolic.oneCandidate_corrected_accepts
#print axioms ExplainableCrypto.Helios.Symbolic.oneCandidate_corrected_accepts
#check ExplainableCrypto.Helios.Symbolic.oneCandidate_printed_rejects
#print axioms ExplainableCrypto.Helios.Symbolic.oneCandidate_printed_rejects
#check ExplainableCrypto.Helios.Symbolic.accepted_excludes_replay
#print axioms ExplainableCrypto.Helios.Symbolic.accepted_excludes_replay
#check ExplainableCrypto.Helios.Symbolic.Equation.classify
#print axioms ExplainableCrypto.Helios.Symbolic.Equation.classify
#check ExplainableCrypto.Helios.Symbolic.Context.weight_fill
#print axioms ExplainableCrypto.Helios.Symbolic.Context.weight_fill
#check ExplainableCrypto.Helios.Symbolic.Context.congr
#print axioms ExplainableCrypto.Helios.Symbolic.Context.congr
#check ExplainableCrypto.Helios.Symbolic.BaseEquation.weight_eq
#print axioms ExplainableCrypto.Helios.Symbolic.BaseEquation.weight_eq
#check ExplainableCrypto.Helios.Symbolic.BaseEq.weight_eq
#print axioms ExplainableCrypto.Helios.Symbolic.BaseEq.weight_eq
#check ExplainableCrypto.Helios.Symbolic.RootStep.weight_lt
#print axioms ExplainableCrypto.Helios.Symbolic.RootStep.weight_lt
#check ExplainableCrypto.Helios.Symbolic.RewriteStep.weight_lt
#print axioms ExplainableCrypto.Helios.Symbolic.RewriteStep.weight_lt
#check ExplainableCrypto.Helios.Symbolic.ModuloStep.weight_lt
#print axioms ExplainableCrypto.Helios.Symbolic.ModuloStep.weight_lt
#check ExplainableCrypto.Helios.Symbolic.BaseEquation.sound
#print axioms ExplainableCrypto.Helios.Symbolic.BaseEquation.sound
#check ExplainableCrypto.Helios.Symbolic.BaseEq.sound
#print axioms ExplainableCrypto.Helios.Symbolic.BaseEq.sound
#check ExplainableCrypto.Helios.Symbolic.RootStep.sound
#print axioms ExplainableCrypto.Helios.Symbolic.RootStep.sound
#check ExplainableCrypto.Helios.Symbolic.RewriteStep.sound
#print axioms ExplainableCrypto.Helios.Symbolic.RewriteStep.sound
#check ExplainableCrypto.Helios.Symbolic.ModuloStep.sound
#print axioms ExplainableCrypto.Helios.Symbolic.ModuloStep.sound
#check ExplainableCrypto.Helios.Symbolic.rewrite_wellFounded
#print axioms ExplainableCrypto.Helios.Symbolic.rewrite_wellFounded
#check ExplainableCrypto.Helios.Symbolic.exists_normal_form
#print axioms ExplainableCrypto.Helios.Symbolic.exists_normal_form
#check ExplainableCrypto.Helios.Symbolic.Reduces.sound
#print axioms ExplainableCrypto.Helios.Symbolic.Reduces.sound
#check ExplainableCrypto.Helios.Symbolic.exists_equivalent_normal_form
#print axioms ExplainableCrypto.Helios.Symbolic.exists_equivalent_normal_form
#check ExplainableCrypto.Helios.Symbolic.rootReduce_sound
#print axioms ExplainableCrypto.Helios.Symbolic.rootReduce_sound
#check ExplainableCrypto.Helios.Symbolic.rootReduce_complete
#print axioms ExplainableCrypto.Helios.Symbolic.rootReduce_complete
#check ExplainableCrypto.Helios.Symbolic.rootReduce_correct
#print axioms ExplainableCrypto.Helios.Symbolic.rootReduce_correct
#check ExplainableCrypto.Helios.Symbolic.tree_size_not_base_invariant
#print axioms ExplainableCrypto.Helios.Symbolic.tree_size_not_base_invariant
#check ExplainableCrypto.Helios.Symbolic.reduction_not_base_equality
#print axioms ExplainableCrypto.Helios.Symbolic.reduction_not_base_equality
#check ExplainableCrypto.Helios.Symbolic.zero_weight_irreducible
#print axioms ExplainableCrypto.Helios.Symbolic.zero_weight_irreducible
#check ExplainableCrypto.Helios.Symbolic.constant_irreducible
#print axioms ExplainableCrypto.Helios.Symbolic.constant_irreducible
#check ExplainableCrypto.Helios.Symbolic.projection_reduces
#print axioms ExplainableCrypto.Helios.Symbolic.projection_reduces
#check ExplainableCrypto.Helios.Symbolic.projection_not_irreducible
#print axioms ExplainableCrypto.Helios.Symbolic.projection_not_irreducible
#check ExplainableCrypto.Helios.Symbolic.nested_root_no_match
#print axioms ExplainableCrypto.Helios.Symbolic.nested_root_no_match
#check ExplainableCrypto.Helios.Symbolic.nested_still_reduces
#print axioms ExplainableCrypto.Helios.Symbolic.nested_still_reduces
#check ExplainableCrypto.Helios.Symbolic.wrong_key_no_match
#print axioms ExplainableCrypto.Helios.Symbolic.wrong_key_no_match
#check ExplainableCrypto.Helios.Symbolic.right_key_match
#print axioms ExplainableCrypto.Helios.Symbolic.right_key_match
#check ExplainableCrypto.Helios.Symbolic.background_root_no_match
#print axioms ExplainableCrypto.Helios.Symbolic.background_root_no_match
#check ExplainableCrypto.Helios.Symbolic.background_still_reduces
#print axioms ExplainableCrypto.Helios.Symbolic.background_still_reduces
#check ExplainableCrypto.Helios.Symbolic.Context.fill_compose
#print axioms ExplainableCrypto.Helios.Symbolic.Context.fill_compose
#check ExplainableCrypto.Helios.Symbolic.Context.base_congr
#print axioms ExplainableCrypto.Helios.Symbolic.Context.base_congr
#check ExplainableCrypto.Helios.Symbolic.RewriteStep.context
#print axioms ExplainableCrypto.Helios.Symbolic.RewriteStep.context
#check ExplainableCrypto.Helios.Symbolic.ModuloStep.context
#print axioms ExplainableCrypto.Helios.Symbolic.ModuloStep.context
#check ExplainableCrypto.Helios.Symbolic.ModuloStep.pre_base
#print axioms ExplainableCrypto.Helios.Symbolic.ModuloStep.pre_base
#check ExplainableCrypto.Helios.Symbolic.ModuloStep.post_base
#print axioms ExplainableCrypto.Helios.Symbolic.ModuloStep.post_base
#check ExplainableCrypto.Helios.Symbolic.RootStep.to_modulo
#print axioms ExplainableCrypto.Helios.Symbolic.RootStep.to_modulo
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.refl
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.refl
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.single
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.single
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.pre_base
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.pre_base
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.trans
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.trans
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.post_base
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.post_base
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.context
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.context
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.sound
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.sound
#check ExplainableCrypto.Helios.Symbolic.ReducesModulo.weight_le
#print axioms ExplainableCrypto.Helios.Symbolic.ReducesModulo.weight_le
#check ExplainableCrypto.Helios.Symbolic.Reduces.to_modulo
#print axioms ExplainableCrypto.Helios.Symbolic.Reduces.to_modulo
#check ExplainableCrypto.Helios.Symbolic.Irreducible.base
#print axioms ExplainableCrypto.Helios.Symbolic.Irreducible.base
#check ExplainableCrypto.Helios.Symbolic.Irreducible.reducesModulo
#print axioms ExplainableCrypto.Helios.Symbolic.Irreducible.reducesModulo
#check ExplainableCrypto.Helios.Symbolic.normal_forms_unique_of_local_confluence
#print axioms ExplainableCrypto.Helios.Symbolic.normal_forms_unique_of_local_confluence
#check ExplainableCrypto.Helios.Symbolic.confluence_of_local_confluence
#print axioms ExplainableCrypto.Helios.Symbolic.confluence_of_local_confluence
#check ExplainableCrypto.Helios.Symbolic.JoinModulo.refl
#print axioms ExplainableCrypto.Helios.Symbolic.JoinModulo.refl
#check ExplainableCrypto.Helios.Symbolic.JoinModulo.symm
#print axioms ExplainableCrypto.Helios.Symbolic.JoinModulo.symm
#check ExplainableCrypto.Helios.Symbolic.JoinModulo.trans
#print axioms ExplainableCrypto.Helios.Symbolic.JoinModulo.trans
#check ExplainableCrypto.Helios.Symbolic.JoinModulo.context
#print axioms ExplainableCrypto.Helios.Symbolic.JoinModulo.context
#check ExplainableCrypto.Helios.Symbolic.JoinModulo.sound
#print axioms ExplainableCrypto.Helios.Symbolic.JoinModulo.sound
#check ExplainableCrypto.Helios.Symbolic.EqE.join_of_confluence
#print axioms ExplainableCrypto.Helios.Symbolic.EqE.join_of_confluence
#check ExplainableCrypto.Helios.Symbolic.eqE_iff_join_of_local_confluence
#print axioms ExplainableCrypto.Helios.Symbolic.eqE_iff_join_of_local_confluence
#check ExplainableCrypto.Helios.Symbolic.irreducible_eqE_iff_base_of_local_confluence
#print axioms ExplainableCrypto.Helios.Symbolic.irreducible_eqE_iff_base_of_local_confluence
#check ExplainableCrypto.Helios.Symbolic.triple_left_step
#print axioms ExplainableCrypto.Helios.Symbolic.triple_left_step
#check ExplainableCrypto.Helios.Symbolic.triple_right_step
#print axioms ExplainableCrypto.Helios.Symbolic.triple_right_step
#check ExplainableCrypto.Helios.Symbolic.triple_endpoints_base
#print axioms ExplainableCrypto.Helios.Symbolic.triple_endpoints_base
#check ExplainableCrypto.Helios.Symbolic.triple_join
#print axioms ExplainableCrypto.Helios.Symbolic.triple_join
#check ExplainableCrypto.Helios.Symbolic.triple_peak_joined
#print axioms ExplainableCrypto.Helios.Symbolic.triple_peak_joined
#check ExplainableCrypto.Helios.Symbolic.triple_raw_endpoints_differ
#print axioms ExplainableCrypto.Helios.Symbolic.triple_raw_endpoints_differ
#check ExplainableCrypto.Helios.Symbolic.Irreducible.reduces_eq
#print axioms ExplainableCrypto.Helios.Symbolic.Irreducible.reduces_eq
#check ExplainableCrypto.Helios.Symbolic.raw_confluence_false
#print axioms ExplainableCrypto.Helios.Symbolic.raw_confluence_false
