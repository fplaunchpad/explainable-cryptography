import ExplainableCrypto.Helios.Symbolic.SourceNameTerms

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

namespace Formula

def mapNames (f : Nat → Nat) : Formula V → Formula V
  | .equal a b => .equal (a.mapNames f) (b.mapNames f)
  | .unequal a b => .unequal (a.mapNames f) (b.mapNames f)
  | .both a b => .both (a.mapNames f) (b.mapNames f)

theorem mapNames_id (p : Formula V) : p.mapNames id = p := by
  induction p <;> simp_all [mapNames,Term.mapNames_id]

theorem mapNames_comp (p : Formula V) (f g : Nat → Nat) :
    (p.mapNames f).mapNames g = p.mapNames (g ∘ f) := by
  induction p <;> simp_all [mapNames,Term.mapNames_comp]

theorem mapNames_subst (p : Formula V) (f : Nat → Nat) (σ : V → Term W) :
    (p.subst σ).mapNames f = (p.mapNames f).subst (fun v => (σ v).mapNames f) := by
  induction p <;> simp_all [mapNames,subst,Term.mapNames_subst]

/-- Full equality, disequality and conjunction transport under a permutation;
all free-variable values are renamed consistently with the literal formula. -/
theorem holds_mapNames (p : Formula V) (e : Nat ≃ Nat) (env : V → Ground) :
    (p.mapNames e).Holds (fun v => (env v).mapNames e) ↔ p.Holds env := by
  induction p with
  | equal a b =>
    simp only [mapNames,Holds,← Term.mapNames_subst,EqE.mapNames_iff]
  | unequal a b =>
    simp only [mapNames,Holds,← Term.mapNames_subst,EqE.mapNames_iff]
  | both a b ha hb => exact and_congr ha hb

theorem holds_mapNames_ground (p : Formula Empty) (e : Nat ≃ Nat) :
    (p.mapNames e).Holds Empty.elim ↔ p.Holds Empty.elim := by
  have he : (fun v : Empty => (Empty.elim v : Ground).mapNames e) = Empty.elim := by
    funext v
    exact v.elim
  simpa only [he] using holds_mapNames p e Empty.elim
end Formula

/-- Name mapping commutes with the shift past a variable binder. -/
theorem shiftTerm_mapNames (m : Term V) (f : Nat → Nat) :
    (shiftTerm m).mapNames f = shiftTerm (m.mapNames f) := by
  simp only [shiftTerm,Term.mapNames_subst,Term.mapNames]

theorem liftSubst_mapNames (σ : V → Term W) (f : Nat → Nat) (v : Option V) :
    (liftSubst σ v).mapNames f = liftSubst (fun x => (σ x).mapNames f) v := by
  cases v with
  | none => rfl
  | some v => exact shiftTerm_mapNames (σ v) f

namespace Agent
/-- Base names and static channel names have independent maps. Variables and
input binders are unchanged; channel and payload numerals are different sorts. -/
def mapNames : {V : Type} → (Nat → Nat) → (Nat → Nat) → Agent V → Agent V
  | _, _, _, .nil => .nil
  | _, f, g, .par p q => .par (p.mapNames f g) (q.mapNames f g)
  | _, f, g, .output c m p => .output (g c) (m.mapNames f) (p.mapNames f g)
  | _, f, g, .input c p => .input (g c) (p.mapNames f g)
  | _, f, g, .branch q p p' => .branch (q.mapNames f) (p.mapNames f g) (p'.mapNames f g)

theorem mapNames_id (p : Agent V) : p.mapNames id id = p := by
  induction p <;> simp_all [mapNames,Term.mapNames_id,Formula.mapNames_id]

theorem mapNames_comp (p : Agent V) (f g f' g' : Nat → Nat) :
    (p.mapNames f g).mapNames f' g' = p.mapNames (f' ∘ f) (g' ∘ g) := by
  induction p <;> simp_all [mapNames,Term.mapNames_comp,Formula.mapNames_comp]

theorem mapNames_subst (p : Agent V) (f g : Nat → Nat) (σ : V → Term W) :
    (p.subst σ).mapNames f g = (p.mapNames f g).subst (fun v => (σ v).mapNames f) := by
  induction p generalizing W with
  | nil => rfl
  | par p q hp hq => simp only [subst,mapNames,hp,hq]
  | output c m p hp => simp only [subst,mapNames,hp,Term.mapNames_subst]
  | branch q p p' hp hp' => simp only [subst,mapNames,hp,hp',Formula.mapNames_subst]
  | input c p hp =>
    simp only [subst,mapNames,hp]
    congr 2
    funext v
    exact liftSubst_mapNames σ f v

theorem mapNames_bind (p : Agent (Option V)) (m : Term V) (f g : Nat → Nat) :
    (p.bind m).mapNames f g = (p.mapNames f g).bind (m.mapNames f) := by
  simp only [bind,mapNames_subst]
  congr 1
  funext v
  cases v <;> rfl

theorem mapNames_inverse (p : Agent V) (e k : Nat ≃ Nat) :
    (p.mapNames e k).mapNames e.symm k.symm = p := by
  rw [mapNames_comp]
  have he : (e.symm ∘ e : Nat → Nat) = id := by funext v; exact e.symm_apply_apply v
  have hk : (k.symm ∘ k : Nat → Nat) = id := by funext v; exact k.symm_apply_apply v
  rw [he,hk,mapNames_id]
end Agent
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
