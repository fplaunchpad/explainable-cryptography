import ExplainableCrypto.Helios.Symbolic.SourceNamedInternalPrenex

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

theorem Term.nameSupport_rename (m : Term V) (σ : V → W) :
    (m.subst (fun v => .var (σ v))).nameSupport = m.nameSupport := by
  induction m <;> simp_all only [Term.subst,Term.nameSupport]

theorem Term.mapNames_eq_of_fixed (m : Term V) (f : Nat → Nat)
    (hf : ∀ n ∈ m.nameSupport, f n = n) : m.mapNames f = m := by
  induction m <;> simp_all [Term.nameSupport,Term.mapNames,or_imp,forall_and]

namespace Historical.General.Source.Extended

theorem FreeLabel.input_shift_nameSupport (c : Nat) (m : Term V) :
    (FreeLabel.input c (shiftTerm m)).nameSupport = (FreeLabel.input c m).nameSupport := by
  simp only [FreeLabel.nameSupport,shiftTerm,Term.nameSupport_rename]

/-- Fixing the complete sorted name support fixes the entire source label,
including every name occurring deep inside an input recipe. -/
theorem FreeLabel.mapNames_eq_of_fixed (l : FreeLabel V) (f g : Nat → Nat)
    (hf : ∀ n ∈ l.nameSupport, n.map f g = n) : l.mapNames f g = l := by
  cases l with
  | input c m =>
    have hc : g c = c := SourceName.channel.inj (hf (.channel c) (by simp [FreeLabel.nameSupport]))
    have hm : m.mapNames f = m := m.mapNames_eq_of_fixed f (by
      intro n hn
      exact SourceName.base.inj (hf (.base n)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem SourceName.base hn))))
    simp only [FreeLabel.mapNames,hc,hm]
  | output c x =>
    have hc : g c = c := SourceName.channel.inj (hf (.channel c) (by simp [FreeLabel.nameSupport]))
    simp only [FreeLabel.mapNames,hc]

end Historical.General.Source.Extended
end ExplainableCrypto.Helios.Symbolic
