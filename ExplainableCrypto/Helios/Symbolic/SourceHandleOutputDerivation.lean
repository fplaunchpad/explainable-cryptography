import ExplainableCrypto.Helios.Symbolic.SourceJointHandleOutput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- Reverse the existing active-substitution derivation to expose the old
handle, apply Out-Atom and keep the original complete frame. -/
theorem Extended.frame_handle_output_derivable (φ : Frame restricted handles)
    (c : Nat) (x : Fin handles) (p : Agent Empty) :
    Extended.FreeStep (Extended.frameProcess φ (.output c (φ.value x) p)) (.output c x)
      (Extended.frameProcess φ p) := by
  have hs := Extended.activeFrame_apply φ (.output c (.var x) (Extended.groundAgent p))
  simp only [Agent.subst,Term.subst,Extended.groundAgent_subst] at hs
  exact .congr hs.symm (.parRight _ (.output c x _)) (.refl _)

/-- Name Scope permits the old-handle label exactly when its channel is
public; restricted names inside the handle's value remain scoped. -/
theorem Named.restricted_handle_output_derivable (φ : Frame restricted handles)
    (c : Nat) (x : Fin handles) (p : Agent Empty) (hc : c ∉ hidden) :
    Named.FreeStep (Named.restrictedState hidden ⟨φ,.output c (φ.value x) p⟩) (.output c x)
      (Named.restrictedState hidden ⟨φ,p⟩) := by
  apply (Named.FreeStep.embed (Extended.frame_handle_output_derivable φ c x p)).restrictNames
  intro n hn hm
  have he : n = .channel c := by simpa only [Extended.FreeLabel.nameSupport,Finset.mem_singleton] using hm
  subst n
  exact hc ((Named.channel_mem_restrictionNames c hidden restricted).mp hn)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
