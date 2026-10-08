import ExplainableCrypto.Helios.Symbolic.SourceCanonicalBodyInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

theorem Extended.FreeLabel.mapAssignments_congr (l : Extended.FreeLabel V)
    (ρ τ : NameAssignment) (h : ∀ n ∈ l.nameSupport, ρ n = τ n) :
    l.mapNames ρ.base ρ.channel = l.mapNames τ.base τ.channel := by
  cases l with
  | input c m =>
    exact congrArg₂ Extended.FreeLabel.input (h (.channel c) (Finset.mem_insert_self _ _))
      (m.mapNames_congr _ _ (fun n hn => h (.base n)
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n,hn,rfl⟩))))
  | output c x =>
    exact congrArg (fun c => Extended.FreeLabel.output c x)
      (h (.channel c) (Finset.mem_singleton_self _))

namespace Named

/-- Every actual Named free step has full interpreted visible behavior.
Name-prefix freshness keeps the complete label under the outer assignment;
forward visible transport needs no injectivity assumption. -/
theorem FreeStep.interprets {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) :
    ∃ q, (l.mapNames ρ.base ρ.channel).RealizedStep env p q ∧ b.Interprets ρ env q := by
  obtain ⟨ns,a',b',hs,ht,hr,hn⟩ := h.prenex
  obtain ⟨τ,hfix,hp⟩ := (interprets_restrictNames ns (.embed a') ρ env p).mp
    ((hs.interprets ρ env p).mp ha)
  have hl : l.mapNames τ.base τ.channel = l.mapNames ρ.base ρ.channel :=
    l.mapAssignments_congr τ ρ (fun n hm => hfix n (fun hns => hn n hns hm))
  obtain ⟨q,hq,hb⟩ := (hr.mapNames τ.base τ.channel).realizes env hp
  rw [hl] at hq
  exact ⟨q,hq,(ht.interprets ρ env q).mpr
    ((interprets_restrictNames ns (.embed b') ρ env q).mpr ⟨τ,hfix,hb⟩)⟩

/-- The emitted complete message extends the old environment exactly once.
The target retains the same assignment for its frame and executable body. -/
theorem BoundOutput.interprets {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) :
    ∃ m q, Agent.Visible p (.output (ρ.channel c) m) q ∧
      b.Interprets ρ (extendEnv env m) q := by
  obtain ⟨ns,a',b',hs,ht,hr,hn⟩ := h.prenex
  obtain ⟨τ,hfix,hp⟩ := (interprets_restrictNames ns (.embed a') ρ env p).mp
    ((hs.interprets ρ env p).mp ha)
  have hc : τ.channel c = ρ.channel c := hfix (.channel c) (fun hns => hn _ hns rfl)
  obtain ⟨m,q,hq,hb⟩ := (hr.mapNames τ.base τ.channel).realizes env hp
  rw [hc] at hq
  exact ⟨m,q,hq,(ht.interprets ρ (extendEnv env m) q).mpr
    ((interprets_restrictNames ns (.embed b') ρ (extendEnv env m) q).mpr ⟨τ,hfix,hb⟩)⟩

theorem FreeStep.literal_interprets {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets NameAssignment.literal env p) :
    ∃ q, l.RealizedStep env p q ∧ b.Interprets NameAssignment.literal env q := by
  have hl : l.mapNames NameAssignment.literal.base NameAssignment.literal.channel = l := by
    change l.mapNames id id = l
    cases l <;> simp only [Extended.FreeLabel.mapNames,Term.mapNames_id]
    all_goals rfl
  simpa only [hl] using h.interprets NameAssignment.literal env ha

theorem FreeStep.input_interprets {a b : Named V} {c : Nat} {r : Term V}
    (h : FreeStep a (.input c r) b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets NameAssignment.literal env p) :
    ∃ q, Agent.Visible p (.input c (r.subst env)) q ∧
      b.Interprets NameAssignment.literal env q := h.literal_interprets env ha

theorem FreeStep.output_interprets {a b : Named V} {c : Nat} {x : V}
    (h : FreeStep a (.output c x) b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets NameAssignment.literal env p) :
    ∃ m q, EqE (env x) m ∧ Agent.Visible p (.output c m) q ∧
      b.Interprets NameAssignment.literal env q := by
  obtain ⟨q,⟨m,hm,hq⟩,hb⟩ := h.literal_interprets env ha
  exact ⟨m,q,hm,hq,hb⟩

theorem BoundOutput.literal_interprets {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets NameAssignment.literal env p) :
    ∃ m q, Agent.Visible p (.output c m) q ∧
      b.Interprets NameAssignment.literal (extendEnv env m) q :=
  h.interprets NameAssignment.literal env ha

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
