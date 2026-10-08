import ExplainableCrypto.Helios.Symbolic.SourceRawInternalMatching
import Mathlib.Data.List.FinRange

namespace ExplainableCrypto.Helios.Symbolic
namespace Frame
variable {restricted : Finset Nat} {h j : Nat}

/-- Reindex all public handles bijectively; every complete value is retained. -/
def reindex (φ : Frame restricted h) (e : Fin h ≃ Fin j) : Frame restricted j :=
  ⟨fun i => φ.value (e.symm i)⟩

theorem StaticEq.reindex {φ ψ : Frame restricted h} (he : φ.StaticEq ψ) (e : Fin h ≃ Fin j) :
    (φ.reindex e).StaticEq (ψ.reindex e) := by
  intro r s hr hs
  have ht := he (r.subst (fun i => .var (e.symm i))) (s.subst (fun i => .var (e.symm i)))
    (Term.Public.subst r _ hr (fun _ => trivial)) (Term.Public.subst s _ hs (fun _ => trivial))
  simpa only [eval,Frame.reindex,Term.subst_subst,Term.subst] using ht
end Frame

namespace Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {h j : Nat}

private def providerList (xs : List (Extended V)) : Extended V := xs.foldr .par (.plain .nil)

private theorem providerList_perm {xs ys : List (Extended V)} (h : xs.Perm ys) :
    Structural (providerList xs) (providerList ys) := by
  induction h with
  | nil => exact .refl _
  | cons a h ih => exact ih.parRight a
  | swap a b xs =>
    exact (Structural.assoc _ _ _).symm.trans
      (((Structural.comm _ _).parLeft _).trans (Structural.assoc _ _ _))
  | trans _ _ ih ij => exact ih.trans ij

private theorem frameEntries_providerList (n : Nat) (vars : Fin n → V) (values : Fin n → Ground) :
    frameEntries n vars values = providerList (List.ofFn (fun i =>
      Extended.active (vars i) (groundTerm (values i)))).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,List.reverse_append]
    simpa only [frameEntries,List.reverse_singleton,List.singleton_append,providerList,List.foldr_cons] using
      congrArg (Extended.par (.active (vars (Fin.last n)) (groundTerm (values (Fin.last n)))))
        (ih (fun i => vars i.castSucc) (fun i => values i.castSucc))

/-- Reordering the actual full provider forest uses only source parallel laws. -/
theorem activeFrame_reindex (φ : Frame restricted h) (e : Fin h ≃ Fin j) :
    Structural ((activeFrame φ).rename e) (activeFrame (φ.reindex e)) := by
  have hj : h = j := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst j
  rw [activeFrame,frameEntries_rename,activeFrame,frameEntries_providerList,frameEntries_providerList]
  have hp := Equiv.Perm.ofFn_comp_perm e (fun i => Extended.active i (groundTerm ((φ.reindex e).value i)))
  apply providerList_perm
  simpa only [Function.comp_def,Frame.reindex,Equiv.symm_apply_apply,id] using (List.reverse_perm'.mpr (List.perm_reverse.mpr hp))

end Historical.General.Source.Extended

namespace Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {h j : Nat}

theorem RepresentsFrame.reindex {a : Named (Fin h)} {φ : Frame restricted h}
    (ha : a.RepresentsFrame hidden φ) (e : Fin h ≃ Fin j) :
    (a.rename e).RepresentsFrame hidden (φ.reindex e) := by
  have hs := ha.rename e e.injective
  rw [← frameOf_rename] at hs
  apply hs.trans
  simpa only [canonicalFrame,restrictNames_rename,rename] using
    (Structural.embed (Extended.activeFrame_reindex φ e)).restrictNames (restrictionNames hidden restricted)

theorem StaticEq.reindex {a b : Named (Fin h)} (he : StaticEq a b) (e : Fin h ≃ Fin j) :
    StaticEq (a.rename e) (b.rename e) := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,he⟩ := he
  exact .of_presentations (ha.reindex e) (hb.reindex e) (he.reindex e)

end Historical.General.Source.Named
end ExplainableCrypto.Helios.Symbolic
