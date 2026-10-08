import ExplainableCrypto.Helios.Symbolic.SourceFrameEquationActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

/-- One assignment for both source sorts. Equal numerals in different sorts
remain different assignment keys. This definition imposes no freshness. -/
abbrev NameAssignment := SourceName → Nat

namespace NameAssignment
def base (ρ : NameAssignment) (n : Nat) : Nat := ρ (.base n)
def channel (ρ : NameAssignment) (n : Nat) : Nat := ρ (.channel n)
def literal : NameAssignment
  | .base n | .channel n => n

theorem update_comp (ρ : NameAssignment) (e k : Nat ≃ Nat) (n : SourceName) (v : Nat) :
    Function.update ρ (n.map e k) v ∘ SourceName.map e k =
      Function.update (ρ ∘ SourceName.map e k) n v := by
  funext m
  by_cases he : m=n <;> simp [Function.comp_def,he,(SourceName.map_injective e k).eq_iff]

end NameAssignment

theorem SourceName.map_base_swap_eq (n m : Nat) :
    SourceName.map (Equiv.swap n m) id = Equiv.swap (.base n) (.base m) := by
  funext u
  cases u <;> simp [SourceName.map,Equiv.swap_apply_def]
  all_goals split_ifs <;> rfl

theorem SourceName.map_channel_swap_eq (n m : Nat) :
    SourceName.map id (Equiv.swap n m) = Equiv.swap (.channel n) (.channel m) := by
  funext u
  cases u <;> simp [SourceName.map,Equiv.swap_apply_def]
  all_goals split_ifs <;> rfl

theorem Formula.mapNames_congr (f : Formula V) (ρ τ : Nat → Nat)
    (h : ∀ n ∈ f.nameSupport, ρ n = τ n) : f.mapNames ρ = f.mapNames τ := by
  induction f with
  | equal a b | unequal a b =>
    simp only [Formula.mapNames]
    congr 1
    · exact a.mapNames_congr ρ τ (fun n hn => h n (Finset.mem_union_left _ hn))
    · exact b.mapNames_congr ρ τ (fun n hn => h n (Finset.mem_union_right _ hn))
  | both a b ha hb =>
    exact congrArg₂ Formula.both (ha (fun n hn => h n (Finset.mem_union_left _ hn)))
      (hb (fun n hn => h n (Finset.mem_union_right _ hn)))

theorem Agent.mapAssignments_congr (p : Agent V) (ρ τ : NameAssignment)
    (h : ∀ n ∈ p.nameSupport, ρ n = τ n) :
    p.mapNames ρ.base ρ.channel = p.mapNames τ.base τ.channel := by
  induction p with
  | nil => rfl
  | par p q hp hq =>
    exact congrArg₂ Agent.par (hp (fun n hn => h n (Finset.mem_union_left _ hn)))
      (hq (fun n hn => h n (Finset.mem_union_right _ hn)))
  | output c m p ih =>
    simp only [mapNames]
    congr 1
    · exact h (.channel c) (Finset.mem_insert_self _ _)
    · exact m.mapNames_congr _ _ (fun n hn => h (.base n)
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n,hn,rfl⟩))))
    · exact ih (fun n hn => h n (Finset.mem_insert_of_mem (Finset.mem_union_right _ hn)))
  | input c p ih =>
    exact congrArg₂ Agent.input (h (.channel c) (Finset.mem_insert_self _ _))
      (ih (fun n hn => h n (Finset.mem_insert_of_mem hn)))
  | branch f p q hp hq =>
    simp only [mapNames]
    congr 1
    · exact f.mapNames_congr _ _ (fun n hn => h (.base n)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n,hn,rfl⟩)))
    · exact hp (fun n hn => h n (Finset.mem_union_right _ (Finset.mem_union_left _ hn)))
    · exact hq (fun n hn => h n (Finset.mem_union_right _ (Finset.mem_union_right _ hn)))

theorem Extended.mapAssignments_congr (a : Extended V) (ρ τ : NameAssignment)
    (h : ∀ n ∈ a.nameSupport, ρ n = τ n) :
    a.mapNames ρ.base ρ.channel = a.mapNames τ.base τ.channel := by
  induction a with
  | plain p => exact congrArg Extended.plain (p.mapAssignments_congr ρ τ h)
  | active x m =>
    exact congrArg (Extended.active x)
      (m.mapNames_congr _ _ (fun n hn => h (.base n) (Finset.mem_image.mpr ⟨n,hn,rfl⟩)))
  | par a b ha hb =>
    exact congrArg₂ Extended.par (ha (fun n hn => h n (Finset.mem_union_left _ hn)))
      (hb (fun n hn => h n (Finset.mem_union_right _ hn)))
  | newVar a ih => exact congrArg Extended.newVar (ih h)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
