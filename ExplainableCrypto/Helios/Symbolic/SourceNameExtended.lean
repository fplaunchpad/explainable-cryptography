import ExplainableCrypto.Helios.Symbolic.SourceNameBehavior

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

theorem replaceVar_mapNames (x : V) (m : Term V) (f : Nat → Nat) (v : V) :
    (replaceVar x m v).mapNames f = replaceVar x (m.mapNames f) v := by
  classical
  by_cases h : v=x <;> simp [replaceVar,h,Term.mapNames]

namespace Extended

/-- Independent base-name and channel maps leave variable binders and active
domains unchanged. This is global renaming, not a name-restriction constructor. -/
def mapNames : {V : Type} → (Nat → Nat) → (Nat → Nat) → Extended V → Extended V
  | _, f, g, .plain p => .plain (p.mapNames f g)
  | _, f, g, .par a b => .par (a.mapNames f g) (b.mapNames f g)
  | _, f, g, .newVar a => .newVar (a.mapNames f g)
  | _, f, _, .active x m => .active x (m.mapNames f)

theorem mapNames_id (a : Extended V) : a.mapNames id id = a := by
  induction a <;> simp_all only [Extended.mapNames,Agent.mapNames_id,Term.mapNames_id]

theorem mapNames_comp (a : Extended V) (f g f' g' : Nat → Nat) :
    (a.mapNames f g).mapNames f' g' = a.mapNames (f' ∘ f) (g' ∘ g) := by
  induction a <;> simp_all only [Extended.mapNames,Agent.mapNames_comp,Term.mapNames_comp]

theorem mapNames_inverse (a : Extended V) (e k : Nat ≃ Nat) :
    (a.mapNames e k).mapNames e.symm k.symm = a := by
  induction a <;> simp_all only [Extended.mapNames,Agent.mapNames_inverse,Term.mapNames_inverse]

theorem mapNames_rename (a : Extended V) (f g : Nat → Nat) (σ : V → W) :
    (a.rename σ).mapNames f g = (a.mapNames f g).rename σ := by
  induction a generalizing W with
  | plain p => simp only [rename,mapNames,Agent.mapNames_subst,Term.mapNames]
  | active x m => simp only [rename,mapNames,Term.mapNames_subst,Term.mapNames]
  | par a b ha hb => simp only [rename,mapNames,ha,hb]
  | newVar a ha => simp only [rename,mapNames,ha]

theorem Structural.mapNames {a b : Extended V} (h : Structural a b) (f g : Nat → Nat) :
    Structural (a.mapNames f g) (b.mapNames f g) := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newVar h ih => exact .newVar ih
  | plainPar p q => exact .plainPar _ _
  | zero => exact .zero _
  | assoc => exact .assoc _ _ _
  | comm => exact .comm _ _
  | newPar a b =>
    simpa only [Extended.mapNames,mapNames_rename] using Structural.newPar (a.mapNames f g) (b.mapNames f g)
  | «alias» m =>
    simpa only [Extended.mapNames,Agent.mapNames,shiftTerm_mapNames] using Structural.alias (m.mapNames f)
  | substPlain x m p =>
    simpa only [Extended.mapNames,Agent.mapNames_subst,replaceVar_mapNames] using Structural.substPlain x (m.mapNames f) (p.mapNames f g)
  | substActive x y m n hxy =>
    simpa only [Extended.mapNames,Term.mapNames_subst,replaceVar_mapNames] using
      Structural.substActive x y (m.mapNames f) (n.mapNames f) hxy
  | rewrite x h => exact .rewrite x (h.mapNames f)

theorem Structural.mapNames_iff (a b : Extended V) (e k : Nat ≃ Nat) :
    Structural (a.mapNames e k) (b.mapNames e k) ↔ Structural a b := by
  constructor
  · intro h
    simpa only [Extended.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem Reduction.mapNames {a b : Extended V} (h : Reduction a b) (e k : Nat ≃ Nat) :
    Reduction (a.mapNames e k) (b.mapNames e k) := by
  induction h with
  | atomComm c x p q =>
    simpa only [Extended.mapNames,Agent.mapNames,Agent.mapNames_bind,Term.mapNames] using Reduction.atomComm (k c) x (p.mapNames e k) (q.mapNames e k)
  | thenBranch f p q hf =>
    rename_i V'
    have he : (fun v : Empty => (Empty.elim v : Term V').mapNames e) = Empty.elim := by funext v; exact v.elim
    simpa only [Extended.mapNames,Agent.mapNames,Formula.mapNames_subst,he] using Reduction.thenBranch (f.mapNames e) (p.mapNames e k) (q.mapNames e k) ((Formula.holds_mapNames_ground f e).mpr hf)
  | elseBranch f p q hf =>
    rename_i V'
    have he : (fun v : Empty => (Empty.elim v : Term V').mapNames e) = Empty.elim := by funext v; exact v.elim
    simpa only [Extended.mapNames,Agent.mapNames,Formula.mapNames_subst,he] using Reduction.elseBranch (f.mapNames e) (p.mapNames e k) (q.mapNames e k) (fun h => hf ((Formula.holds_mapNames_ground f e).mp h))
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newVar h ih => exact .newVar ih
  | congr hp h hq ih => exact .congr (hp.mapNames e k) ih (hq.mapNames e k)

theorem Reduction.mapNames_iff (a b : Extended V) (e k : Nat ≃ Nat) :
    Reduction (a.mapNames e k) (b.mapNames e k) ↔ Reduction a b := by
  constructor
  · intro h
    simpa only [Extended.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k
end Extended
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
