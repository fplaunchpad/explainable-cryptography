import ExplainableCrypto.Helios.Symbolic.SourcePairedOpeningReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Rename allocated values and assigned free values without renaming source
binder keys. Base and channel assignments remain separate. -/
def NameAssignment.mapValues (ρ : NameAssignment) (f g : Nat → Nat) : NameAssignment
  | .base n => f (ρ (.base n))
  | .channel n => g (ρ (.channel n))

theorem NameAssignment.mapValues_update_base (ρ : NameAssignment) (f g : Nat → Nat) (n v : Nat) :
    NameAssignment.mapValues (Function.update ρ (.base n) v) f g = Function.update (ρ.mapValues f g) (.base n) (f v) := by
  funext m
  cases m with
  | base t => by_cases ht : t=n <;> simp [mapValues,ht]
  | channel t => simp [mapValues]

theorem NameAssignment.mapValues_update_channel (ρ : NameAssignment) (f g : Nat → Nat) (n v : Nat) :
    NameAssignment.mapValues (Function.update ρ (.channel n) v) f g = Function.update (ρ.mapValues f g) (.channel n) (g v) := by
  funext m
  cases m with
  | base t => simp [mapValues]
  | channel t => by_cases ht : t=n <;> simp [mapValues,ht]

namespace Named
variable {V : Type}

/-- Bijections of assigned values preserve the full opened process and the
recorded allocation list. The source syntax itself is unchanged. -/
theorem Opens.mapValues {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) (e k : Nat ≃ Nat) :
    Opens a (ρ.mapValues e k) (ns.map (SourceName.map e k)) (b.mapNames e k) := by
  induction h with
  | embed a ρ =>
    have he : (a.mapNames ρ.base ρ.channel).mapNames e k =
        a.mapNames (ρ.mapValues e k).base (ρ.mapValues e k).channel := by
      rw [Extended.mapNames_comp]
      rfl
    rw [he]
    exact .embed a (ρ.mapValues e k)
  | par ha hb hd ih ij =>
    rw [List.map_append]
    apply Opens.par ih ij
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,hv,he⟩ := List.mem_map.mp hy
    exact hd u hu ((SourceName.map_injective e k he) ▸ hv)
  | @newName _ n v _ _ tail _ ha hf ih =>
    have hg : (n.withValue v).map e k ∉ List.map (SourceName.map e k) tail := by
      intro hm
      obtain ⟨u,hu,he⟩ := List.mem_map.mp hm
      exact hf ((SourceName.map_injective e k he) ▸ hu)
    cases n with
    | base n =>
      rw [NameAssignment.mapValues_update_base] at ih
      exact .newName (.base n) (e v) ih hg
    | channel n =>
      rw [NameAssignment.mapValues_update_channel] at ih
      exact .newName (.channel n) (k v) ih hg
  | newVar ha ih => exact .newVar ih

theorem Opens.mapValues_literal {a : Named V} {ns : List SourceName} {b : Extended V}
    (h : Opens a NameAssignment.literal ns b) (e k : Nat ≃ Nat)
    (hf : ∀ n ∈ a.freeNames, n.map e k = n) :
    Opens a NameAssignment.literal (ns.map (SourceName.map e k)) (b.mapNames e k) := by
  apply (h.mapValues e k).names_congr
  intro n hn
  have he := congrArg NameAssignment.literal (hf n hn)
  cases n <;> exact he

/-- Any externally fresh opening can avoid a new finite set while preserving
its whole body by actual value permutations. Free source names stay fixed. -/
theorem Opens.refresh {a : Named V} {ns : List SourceName} {b : Extended V}
    (h : Opens a NameAssignment.literal ns b) (hf : ∀ n ∈ ns, n ∉ a.freeNames)
    (avoid : Finset SourceName) :
    ∃ e k : Nat ≃ Nat,
      Opens a NameAssignment.literal (ns.map (SourceName.map e k)) (b.mapNames e k) ∧
      (∀ n ∈ ns.map (SourceName.map e k), n ∉ avoid ∪ a.freeNames) ∧
      (∀ n ∈ a.freeNames, n.map e k = n) := by
  obtain ⟨ms,e,k,_,_,hg,_,_,hm,hfix⟩ := exists_common_fresh_prefix ns (.embed b) (.embed b)
    (avoid ∪ a.freeNames)
  have he : ∀ n ∈ a.freeNames, n.map e k = n := by
    intro n hn
    exact hfix n (Finset.mem_union_right _ hn) (fun hm => hf n hm hn)
  refine ⟨e,k,h.mapValues_literal e k he,?_,he⟩
  intro n hn hav
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hn
  exact hg _ (hm u hu) hav

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
