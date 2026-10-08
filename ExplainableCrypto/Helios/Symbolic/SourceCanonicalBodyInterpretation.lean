import ExplainableCrypto.Helios.Symbolic.SourceNamedStructuralInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

/-- A name prefix permits assignments precisely at its bound names, in both
sorts. The same assignment interprets the frame and every continuation. -/
theorem interprets_restrictNames (ns : List SourceName) (a : Named V)
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    (restrictNames ns a).Interprets ρ env p ↔
      ∃ τ : NameAssignment, (∀ n, n ∉ ns → τ n = ρ n) ∧ a.Interprets τ env p := by
  induction ns generalizing ρ with
  | nil =>
    simp only [restrictNames,List.foldr,List.not_mem_nil,not_false_eq_true,forall_true_left]
    constructor
    · intro h; exact ⟨ρ,fun _ => rfl,h⟩
    · rintro ⟨τ,hτ,h⟩; rw [funext hτ] at h; exact h
  | cons c ns ih =>
    change (∃ k, (restrictNames ns a).Interprets (Function.update ρ c k) env p) ↔ _
    simp only [ih]
    constructor
    · rintro ⟨k,τ,hτ,ha⟩
      refine ⟨τ,?_,ha⟩
      intro n hn
      have hnc : n ≠ c := fun he => hn (by simp [he])
      have hns : n ∉ ns := fun hm => hn (List.mem_cons_of_mem _ hm)
      simpa only [Function.update_of_ne hnc] using hτ n hns
    · rintro ⟨τ,hτ,ha⟩
      refine ⟨τ c,τ,?_,ha⟩
      intro n hn
      by_cases hnc : n=c
      · simp [hnc]
      · rw [Function.update_of_ne hnc]
        exact hτ n (by simp only [List.mem_cons,hnc,false_or]; exact hn)

theorem restrictedState_interprets_iff (s : ScopedState restricted handles)
    (ρ : NameAssignment) (env : Fin handles → Ground) (p : Agent Empty) :
    (restrictedState hidden s).Interprets ρ env p ↔
      ∃ τ : NameAssignment,
        (∀ n, n ∉ restricted → τ.base n = ρ.base n) ∧
        (∀ c, c ∉ hidden → τ.channel c = ρ.channel c) ∧
        (∀ i, EqE (env i) ((s.frame.value i).mapNames τ.base)) ∧
        Agent.EvalEq (s.body.mapNames τ.base τ.channel) p := by
  simp only [restrictedState,interprets_restrictNames,Interprets,
    Extended.frameProcess_mapNames,Extended.frameProcess_realizes_iff,Frame.mapNames]
  apply exists_congr
  intro τ
  have hf : (∀ n, n ∉ restrictionNames hidden restricted → τ n = ρ n) ↔
      (∀ n, n ∉ restricted → τ.base n = ρ.base n) ∧
      (∀ c, c ∉ hidden → τ.channel c = ρ.channel c) := by
    constructor
    · intro h
      exact ⟨fun n hn => h (.base n) (by simpa only [base_mem_restrictionNames] using hn),
        fun c hc => h (.channel c) (by simpa only [channel_mem_restrictionNames] using hc)⟩
    · rintro ⟨hb,hc⟩ n hn
      cases n with
      | base n => exact hb n (by simpa only [base_mem_restrictionNames] using hn)
      | channel c => exact hc c (by simpa only [channel_mem_restrictionNames] using hn)
  rw [hf]
  exact and_assoc

/-- Every canonical state interprets its literal full frame and body. -/
theorem restrictedState_interprets (s : ScopedState restricted handles) :
    (restrictedState hidden s).Interprets NameAssignment.literal s.frame.value s.body := by
  apply (restrictedState_interprets_iff s _ _ _).mpr
  refine ⟨NameAssignment.literal,fun _ _ => rfl,fun _ _ => rfl,?_,?_⟩
  · intro i
    change EqE (s.frame.value i) ((s.frame.value i).mapNames id)
    rw [Term.mapNames_id]
    exact .refl _
  · change Agent.EvalEq (s.body.mapNames id id) s.body
    rw [Agent.mapNames_id]
    exact .refl _

/-- An actual structural path carries the original complete body to its raw
representative. No injectivity of the existential assignments is asserted. -/
theorem Structural.canonical_interprets (s : ScopedState restricted handles)
    {a : Named (Fin handles)} (h : Structural (restrictedState hidden s) a) :
    a.Interprets NameAssignment.literal s.frame.value s.body :=
  (h.interprets _ _ _).mp (restrictedState_interprets s)

theorem Structural.canonical_prenex_interprets (s : ScopedState restricted handles)
    (ns : List SourceName) (a : Extended (Fin handles))
    (h : Structural (restrictedState hidden s) (Named.restrictNames ns (.embed a))) :
    ∃ τ : NameAssignment, (∀ n, n ∉ ns → τ n = NameAssignment.literal n) ∧
      (a.mapNames τ.base τ.channel).Realizes s.frame.value s.body :=
  (interprets_restrictNames ns (.embed a) _ _ _).mp (h.canonical_interprets s)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
