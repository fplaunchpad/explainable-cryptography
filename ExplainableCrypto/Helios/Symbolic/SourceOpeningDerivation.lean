import ExplainableCrypto.Helios.Symbolic.SourceOpeningAlpha

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem SourceName.map_eq_of_assignment_eq (n : SourceName) (ρ : NameAssignment) (e k : Nat ≃ Nat)
    (h : ρ n = NameAssignment.permutations e k n) : n.map ρ.base ρ.channel = n.map e k := by
  rw [SourceName.map_assignment_eq,h,← SourceName.map_assignment_eq,SourceName.map_permutations]

namespace Named
variable {V : Type}

theorem Opens.fresh_for_permuted_context {a : Named V} {ρ : NameAssignment}
    {ns : List SourceName} {b : Extended V} (h : Opens a ρ ns b) (e k : Nat ≃ Nat)
    (he : ∀ n ∈ a.freeNames, ρ n = NameAssignment.permutations e k n)
    (m : SourceName) (hm : m ∉ (a.mapNames e k).allNames) (hn : m ∉ ns) :
    m ∉ b.nameSupport := by
  apply h.fresh_for_opened_context m _ hn
  intro hx
  obtain ⟨x,hx,hex⟩ := Finset.mem_image.mp hx
  apply hm
  rw [allNames_mapNames]
  exact Finset.mem_image.mpr ⟨x,freeNames_subset_allNames a hx,
    (SourceName.map_eq_of_assignment_eq x ρ e k (he x hx)).symm.trans hex⟩

/-- A sufficiently fresh opening is an actual source prenex derivation. The
outer assignment need agree with the permutations only on free source names.
This proves derivability of the chosen allocation, not uniqueness or comparison
of arbitrary structural paths. -/
theorem Opens.structural {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) (e k : Nat ≃ Nat)
    (he : ∀ n ∈ a.freeNames, ρ n = NameAssignment.permutations e k n)
    (hf : ∀ n ∈ ns, n ∉ (a.mapNames e k).allNames) :
    Structural (a.mapNames e k) (restrictNames ns (.embed b)) := by
  induction h generalizing e k with
  | embed a ρ =>
    have hh := a.mapAssignments_congr ρ (NameAssignment.permutations e k) he
    change a.mapNames ρ.base ρ.channel = a.mapNames e k at hh
    rw [hh]
    exact .refl _
  | @par V a b ρ ns ms a' b' ha hb hd ih ij =>
    have hel : ∀ n ∈ a.freeNames, ρ n = NameAssignment.permutations e k n :=
      fun n hn => he n (Finset.mem_union_left _ hn)
    have her : ∀ n ∈ b.freeNames, ρ n = NameAssignment.permutations e k n :=
      fun n hn => he n (Finset.mem_union_right _ hn)
    have hfl : ∀ n ∈ ns, n ∉ (a.mapNames e k).allNames :=
      fun n hn hm => hf n (List.mem_append_left _ hn) (Finset.mem_union_left _ hm)
    have hfr : ∀ n ∈ ms, n ∉ (b.mapNames e k).allNames :=
      fun n hn hm => hf n (List.mem_append_right _ hn) (Finset.mem_union_right _ hm)
    have hs := ih e k hel hfl
    have ht := ij e k her hfr
    exact (Structural.parLeft _ hs).trans
      (Structural.par_prefix_combine ns ms a' b' (b.mapNames e k) ht
        (fun n hn hm => hf n (List.mem_append_left _ hn)
          (Finset.mem_union_right _ (freeNames_subset_allNames _ hm)))
        (fun n hn => ha.fresh_for_permuted_context e k hel n
          (fun hm => hf n (List.mem_append_right _ hn) (Finset.mem_union_left _ hm))
          (fun hm => hd n hm hn)))
  | @newName V n v a ρ ns b ha hn ih =>
    cases n with
    | base n =>
      have hv : SourceName.base v ∉ (a.mapNames e k).allNames :=
        fun hm => hf _ (List.mem_cons_self) (Finset.mem_insert_of_mem hm)
      have hc := ih (e.trans (Equiv.swap (e n) v)) k
        (opening_alphaBase_agreement a ρ e k n v he hv)
        (fun m hm => opening_alphaBase_fresh a e k n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun hh => hn (by simpa only [SourceName.withValue,← hh] using hm)))
      have hs := Structural.alphaBase (a.mapNames e k) (e n) v hv
      rw [Named.mapNames_comp] at hs
      exact hs.trans (.newName (.base v) hc)
    | channel n =>
      have hv : SourceName.channel v ∉ (a.mapNames e k).allNames :=
        fun hm => hf _ (List.mem_cons_self) (Finset.mem_insert_of_mem hm)
      have hc := ih e (k.trans (Equiv.swap (k n) v))
        (opening_alphaChannel_agreement a ρ e k n v he hv)
        (fun m hm => opening_alphaChannel_fresh a e k n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun hh => hn (by simpa only [SourceName.withValue,← hh] using hm)))
      have hs := Structural.alphaChannel (a.mapNames e k) (k n) v hv
      rw [Named.mapNames_comp] at hs
      exact hs.trans (.newName (.channel v) hc)
  | newVar ha ih =>
    exact (Structural.newVar (ih e k he hf)).trans
      ((Structural.var_restrictNames _ _).trans ((Structural.embedVar _).symm.restrictNames _))

theorem Opens.structural_literal {a : Named V} {ns : List SourceName} {b : Extended V}
    (h : Opens a NameAssignment.literal ns b) (hf : ∀ n ∈ ns, n ∉ a.allNames) :
    Structural a (restrictNames ns (.embed b)) := by
  simpa only [Equiv.coe_refl,Named.mapNames_id] using
    h.structural (Equiv.refl Nat) (Equiv.refl Nat) (by intro n hn; cases n <;> rfl)
      (by simpa only [Equiv.coe_refl,Named.mapNames_id] using hf)

theorem exists_fresh_opening_structural (a : Named V) (avoid : Finset SourceName) :
    ∃ ns b, Opens a NameAssignment.literal ns b ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid ∪ a.allNames) ∧ Structural a (restrictNames ns (.embed b)) := by
  obtain ⟨ns,b,hb,hf⟩ := exists_fresh_opening a NameAssignment.literal (avoid ∪ a.allNames)
  exact ⟨ns,b,hb,hb.nodup,hf,hb.structural_literal
    (fun n hn hm => hf n hn (Finset.mem_union_right _ hm))⟩

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
