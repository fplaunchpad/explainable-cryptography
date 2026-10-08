import ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningComparison

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- An actual Extended reduction under a name prefix acts on the full chosen
opening when allocations avoid both endpoint supports. Finite faithfulness is
maintained down the prefix; no inverse assignment is assumed. -/
theorem Opens.prefix_reduction_realizes (bound : List SourceName) {a b : Extended V}
    (hr : Extended.Reduction a b) (ρ : NameAssignment) {ns : List SourceName}
    {a' : Extended V} (ho : Opens (restrictNames bound (.embed a)) ρ ns a')
    (hi : ρ.FaithfulOn (a.nameSupport ∪ b.nameSupport))
    (hf : ∀ n ∈ ns, n ∉ (a.nameSupport ∪ b.nameSupport).image
      (SourceName.map ρ.base ρ.channel))
    (env : V → Ground) {p : Agent Empty} (ha : a'.Realizes env p) :
    ∃ q, Agent.Tau p q ∧ (restrictNames bound (.embed b)).Interprets ρ env q := by
  induction bound generalizing ρ ns with
  | nil =>
    cases ho
    exact hr.interprets_faithful ρ env hi ha
  | cons n bound ih =>
    cases ho with
    | newName _ v ho hn =>
      obtain ⟨q,hq,hb⟩ := ih (Function.update ρ n v) ho
        (hi.update_fresh n v (hf _ List.mem_cons_self))
        (fun m hm => nameAssignment_fresh_update_image ρ _ n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun he => hn (he ▸ hm)))
      exact ⟨q,hq,v,hb⟩

/-- Any original Named reduction can be interpreted from a suitably fresh
chosen opening of its source. The finite avoidance set is derived from the
actual reduction, rather than an assumed reconstruction witness. -/
theorem Reduction.opening_interpretation {a b : Named V} (h : Reduction a b) :
    ∃ avoid : Finset SourceName,
      ∀ (ns : List SourceName) (a' : Extended V),
        Opens a NameAssignment.literal ns a' → (∀ n ∈ ns, n ∉ avoid) →
        ∀ (env : V → Ground) (p : Agent Empty), a'.Realizes env p →
          ∃ q, Agent.Tau p q ∧ b.Interprets NameAssignment.literal env q := by
  obtain ⟨bound,c,d,hc,hd,hr⟩ := h.prenex
  let avoid := c.nameSupport ∪ d.nameSupport
  refine ⟨avoid,?_⟩
  intro ns a' ho hf env p ha
  obtain ⟨ms,c',hc',hg,he⟩ := hc.transport_opening _ ns a' avoid ho hf
  have hmap : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  have hi : NameAssignment.literal.FaithfulOn avoid := by
    intro x y hx hy hxy
    simpa only [hmap,id_eq] using hxy
  obtain ⟨q,hq,hb⟩ := hc'.prefix_reduction_realizes bound hr NameAssignment.literal hi
    (by simpa only [hmap,Finset.image_id] using hg) env ((he env p).mp ha)
  exact ⟨q,hq,(hd.interprets _ _ _).mpr hb⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
