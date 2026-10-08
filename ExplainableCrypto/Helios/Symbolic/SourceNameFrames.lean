import ExplainableCrypto.Helios.Symbolic.SourceNameLabels

namespace ExplainableCrypto.Helios.Symbolic

theorem names_image_inverse (s : Finset Nat) (e : Nat ≃ Nat) :
    (s.image e).image e.symm = s := by
  ext v
  simp

namespace Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- Every handle keeps its index and full payload; the policy moves too. -/
def mapNames (φ : Frame restricted handles) (f : Nat → Nat) : Frame (restricted.image f) handles :=
  ⟨fun i => (φ.value i).mapNames f⟩

theorem mapNames_eval (φ : Frame restricted handles) (r : Recipe handles) (f : Nat → Nat) :
    (φ.mapNames f).eval (r.mapNames f) = (φ.eval r).mapNames f :=
  (Term.mapNames_subst r f φ.value).symm

theorem mapNames_extend (φ : Frame restricted handles) (m : Ground) (f : Nat → Nat) :
    (φ.extend m).mapNames f = (φ.mapNames f).extend (m.mapNames f) := by
  change Frame.mk _ = Frame.mk _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Frame.extend_last,Fin.lastCases_last]
  · simp only [Frame.extend_old,Fin.lastCases_castSucc,mapNames]

theorem mapNames_injective (e : Nat ≃ Nat) :
    Function.Injective (fun φ : Frame restricted handles => φ.mapNames e) := by
  rintro ⟨φ⟩ ⟨ψ⟩ h
  congr 1
  funext i
  have hi := congrArg (fun a => a.value i) h
  have he := congrArg (fun m => m.mapNames e.symm) hi
  simpa only [mapNames,Term.mapNames_inverse] using he

theorem eval_mapNames_inverse (φ : Frame restricted handles) (r : Recipe handles) (e : Nat ≃ Nat) :
    (φ.mapNames e).eval r = (φ.eval (r.mapNames e.symm)).mapNames e := by
  rw [← mapNames_eval]
  rw [show (r.mapNames e.symm).mapNames e = r from Term.mapNames_inverse r e.symm]

/-- Quantifies over all public recipes in the renamed policy, using inverse
renaming to recover their original observations. -/
theorem StaticEq.mapNames {φ ψ : Frame restricted handles} (h : φ.StaticEq ψ) (e : Nat ≃ Nat) :
    (φ.mapNames e).StaticEq (ψ.mapNames e) := by
  intro r s hr hs
  have publicInverse (t : Recipe handles) (ht : t.Public (restricted.image e)) :
      (t.mapNames e.symm).Public restricted := by
    simpa only [names_image_inverse] using (Term.public_mapNames_iff t e.symm (restricted.image e)).mpr ht
  have hh := h (r.mapNames e.symm) (s.mapNames e.symm) (publicInverse r hr) (publicInverse s hs)
  simpa only [eval_mapNames_inverse,EqE.mapNames_iff] using hh

theorem staticEq_mapNames_iff (φ ψ : Frame restricted handles) (e : Nat ≃ Nat) :
    (φ.mapNames e).StaticEq (ψ.mapNames e) ↔ φ.StaticEq ψ := by
  constructor
  · intro h r s hr hs
    have hh := h (r.mapNames e) (s.mapNames e)
      ((Term.public_mapNames_iff r e restricted).mpr hr)
      ((Term.public_mapNames_iff s e restricted).mpr hs)
    simpa only [mapNames_eval,EqE.mapNames_iff] using hh
  · exact fun h => h.mapNames e
end Frame
end ExplainableCrypto.Helios.Symbolic
