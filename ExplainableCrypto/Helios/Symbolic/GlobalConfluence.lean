import ExplainableCrypto.Helios.Symbolic.AdditionLocalConfluence
import ExplainableCrypto.Helios.Symbolic.ProofCheckingLocalConfluence
import ExplainableCrypto.Helios.Symbolic.DecryptionLocalConfluence
import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private def LocalRepresentatives (s : Multiset (BaseClass V)) : Prop :=
  ∀ q ∈ s, ∃ a : Term V, a.baseClass = q ∧ LocallyConfluentAt a

private theorem singleton_representatives (t : Term V) (h : LocallyConfluentAt t) :
    LocalRepresentatives {t.baseClass} := by
  intro q hq
  rw [Multiset.mem_singleton] at hq
  exact ⟨t, hq.symm, h⟩

private theorem empty_representatives : LocalRepresentatives (V := V) 0 := by
  intro q hq
  exact False.elim (Multiset.notMem_zero q hq)

private theorem append_representatives {s t : Multiset (BaseClass V)}
    (hs : LocalRepresentatives s) (ht : LocalRepresentatives t) : LocalRepresentatives (s + t) := by
  intro q hq
  rcases Multiset.mem_add.mp hq with hq | hq
  · exact hs q hq
  · exact ht q hq

private theorem mul_local_of_representatives (t : Term V) (h : LocalRepresentatives t.mulFactors) :
    LocallyConfluentAt t := by
  intro u v hu hv
  apply modulo_peaks_joined_of_factor_local ?_ hu hv
  intro a b c _ hm hab hac
  obtain ⟨r, hr, hl⟩ := h a.baseClass hm
  exact (hl.of_base ((baseClass_eq_iff _ _).mp hr.symm)) b c hab hac

/-- The factor witnesses are carried alongside the term property, so an AC
constructor inherits them from its children without recursion on E0 representatives. -/
private structure LocalBundle (t : Term V) : Prop where
  lc : LocallyConfluentAt t
  mul : LocalRepresentatives t.mulFactors
  compose : LocalRepresentatives t.composeFactors
  add : LocalRepresentatives t.addSummary.atoms

private theorem singleton_bundle (t : Term V) (h : LocallyConfluentAt t)
    (hm : t.mulFactors = {t.baseClass}) (hc : t.composeFactors = {t.baseClass})
    (ha : t.addSummary.atoms = {t.baseClass}) : LocalBundle t :=
  ⟨h, hm ▸ singleton_representatives t h, hc ▸ singleton_representatives t h,
    ha ▸ singleton_representatives t h⟩

private theorem local_bundle (t : Term V) : LocalBundle t := by
  induction t with
  | name n => exact singleton_bundle _ (name_irreducible n).locally_confluent_at rfl rfl rfl
  | var v => exact singleton_bundle _ (var_irreducible v).locally_confluent_at rfl rfl rfl
  | const c =>
    have h := (constant_irreducible (V := V) c).locally_confluent_at
    refine ⟨h, singleton_representatives _ h, singleton_representatives _ h, ?_⟩
    cases c with
    | zero | one => exact empty_representatives
    | ok | bottom => exact singleton_representatives _ h
  | unary f a ih =>
    exact singleton_bundle _ (locally_confluent_at_unary f a ih.lc) rfl rfl rfl
  | binary f a b ia ib =>
    cases f with
    | mul =>
      have hr := append_representatives ia.mul ib.mul
      have hl := mul_local_of_representatives (.binary .mul a b) hr
      exact ⟨hl, hr, singleton_representatives _ hl, singleton_representatives _ hl⟩
    | compose =>
      have hr := append_representatives ia.compose ib.compose
      have hl := locally_confluent_at_of_compose_factors (.binary .compose a b)
        (compose_factors_local_of_representatives _ hr)
      exact ⟨hl, singleton_representatives _ hl, hr, singleton_representatives _ hl⟩
    | add =>
      have hr := append_representatives ia.add ib.add
      have hl := locally_confluent_at_of_add_summaries (.binary .add a b)
        (add_summaries_local_of_representatives _ hr)
      exact ⟨hl, singleton_representatives _ hl, singleton_representatives _ hl, hr⟩
    | pair =>
      exact singleton_bundle _ (locally_confluent_at_passive_binary .pair (Or.inl rfl)
        a b ia.lc ib.lc) rfl rfl rfl
    | partialDecrypt =>
      exact singleton_bundle _ (locally_confluent_at_passive_binary .partialDecrypt (Or.inr rfl)
        a b ia.lc ib.lc) rfl rfl rfl
    | dec =>
      exact singleton_bundle _ (locally_confluent_at_decryption a b ia.lc ib.lc) rfl rfl rfl
  | ternary f a b c ia ib ic =>
    cases f with
    | penc =>
      exact singleton_bundle _ (locally_confluent_at_penc a b c ia.lc ib.lc ic.lc) rfl rfl rfl
    | checkspk =>
      exact singleton_bundle _ (locally_confluent_at_checkspk a b c ia.lc ib.lc ic.lc) rfl rfl rfl
  | spk a b c d ia ib ic id =>
    exact singleton_bundle _ (locally_confluent_at_spk a b c d ia.lc ib.lc ic.lc id.lc) rfl rfl rfl

/-- Local confluence for every term in the encoded E0-modulo rewrite system. -/
theorem locally_confluent_at (t : Term V) : LocallyConfluentAt t := (local_bundle t).lc

theorem local_confluence_modulo : LocalConfluentModulo V := locally_confluent_at

/-- Checked termination and unconditional local confluence establish confluence. -/
theorem confluence_modulo : ConfluentModulo V := confluence_of_local_confluence local_confluence_modulo

theorem single_factor_local_confluence : SingleFactorLocalConfluent V :=
  local_confluence_iff_single_factor.mp local_confluence_modulo

theorem normal_forms_unique_modulo (a b c : Term V)
    (hab : ReducesModulo a b) (hb : Irreducible b)
    (hac : ReducesModulo a c) (hc : Irreducible c) : BaseEq b c :=
  normal_forms_unique_of_local_confluence local_confluence_modulo a b c hab hb hac hc

theorem eqE_iff_join (a b : Term V) : EqE a b ↔ JoinModulo a b :=
  eqE_iff_join_of_local_confluence local_confluence_modulo a b

theorem irreducible_eqE_iff_base {a b : Term V} (ha : Irreducible a) (hb : Irreducible b) :
    EqE a b ↔ BaseEq a b :=
  irreducible_eqE_iff_base_of_local_confluence local_confluence_modulo ha hb

end ExplainableCrypto.Helios.Symbolic
