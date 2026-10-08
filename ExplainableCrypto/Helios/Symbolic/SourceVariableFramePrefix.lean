import ExplainableCrypto.Helios.Symbolic.SourcePresentationAlignment

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

/-- Variable coordinates beneath a finite prefix of original local binders. -/
def LocalVars : Nat → Type → Type
  | 0, V => V
  | n+1, V => LocalVars n (Option V)

/-- Reclose the original binders; this is notation for existing newVar syntax. -/
def closeVars : (n : Nat) → {V : Type} → Extended (LocalVars n V) → Extended V
  | 0, _, a => a
  | n+1, _, a => .newVar (closeVars n a)

def localMap : (n : Nat) → {V W : Type} → (V → W) → LocalVars n V → LocalVars n W
  | 0, _, _, f => f
  | n+1, _, _, f => localMap n (Option.map f)

def outerVar : (n : Nat) → {V : Type} → V → LocalVars n V
  | 0, _, v => v
  | n+1, _, v => outerVar n (some v)

/-- The residual frame contains only nil and active definitions in parallel;
all local restrictions have been moved to the explicit prefix. -/
def FrameForest : {V : Type} → Extended V → Prop
  | _, .plain p => p = .nil
  | _, .active _ _ => True
  | _, .par a b => a.FrameForest ∧ b.FrameForest
  | _, .newVar _ => False

variable {V W : Type}

theorem FrameForest.rename {a : Extended V} (ha : a.FrameForest) (f : V → W) :
    (a.rename f).FrameForest := by
  induction a generalizing W with
  | plain p => change p = .nil at ha; subst p; rfl
  | active => trivial
  | par a b ih ij => exact ⟨ih ha.1 f,ij ha.2 f⟩
  | newVar => exact ha.elim

theorem FrameForest.frameOf {a : Extended V} (ha : a.FrameForest) : a.frameOf = a := by
  induction a with
  | plain p => change p = .nil at ha; subst p; rfl
  | active => rfl
  | par a b ih ij => simp only [Extended.frameOf,ih ha.1,ij ha.2]
  | newVar => exact ha.elim

/-- Extract any chosen provider from the forest while retaining every other
equation. The uniqueness invariant derives absence from the remainder. -/
theorem FrameForest.extract_provider {a : Extended V} (ha : a.FrameForest)
    (hu : a.UniqueDefinitions) {x : V} (hx : a.Exports x) :
    ∃ (m : Term V) (b : Extended V), b.FrameForest ∧ ¬ b.Exports x ∧
      Structural a (.par (.active x m) b) := by
  induction a with
  | plain => exact hx.elim
  | newVar => exact ha.elim
  | active y m =>
    change x = y at hx
    subst y
    exact ⟨m,.plain .nil,rfl,not_false,(Structural.zero _).symm⟩
  | par a b ih ij =>
    rcases hx with hx | hx
    · obtain ⟨m,c,hc,hn,hs⟩ := ih ha.1 hu.1 hx
      refine ⟨m,.par c b,⟨hc,ha.2⟩,?_,(hs.parLeft b).trans (Structural.assoc _ _ _)⟩
      rintro (he | he)
      · exact hn he
      · exact hu.2.2 x ⟨hx,he⟩
    · obtain ⟨m,c,hc,hn,hs⟩ := ij ha.2 hu.2.1 hx
      refine ⟨m,.par c a,⟨hc,ha.1⟩,?_,(Structural.comm _ _).trans
        ((hs.parLeft a).trans (Structural.assoc _ _ _))⟩
      rintro (he | he)
      · exact hn he
      · exact hu.2.2 x ⟨he,hx⟩

theorem closeVars_rename (n : Nat) (a : Extended (LocalVars n V)) (f : V → W) :
    (closeVars n a).rename f = closeVars n (a.rename (localMap n f)) := by
  induction n generalizing V W with
  | zero => rfl
  | succ n ih => exact congrArg Extended.newVar (ih a (Option.map f))

theorem outerVar_injective (n : Nat) : Function.Injective (@outerVar n V) := by
  induction n generalizing V with
  | zero => exact Function.injective_id
  | succ n ih => exact (ih (V := Option V)).comp (Option.some_injective V)

/-- Closing locals retains precisely the old public coordinates. -/
theorem closeVars_exports (n : Nat) (a : Extended (LocalVars n V)) (v : V) :
    (closeVars n a).Exports v ↔ a.Exports (outerVar n v) := by
  induction n generalizing V with
  | zero => rfl
  | succ n ih => exact ih a (some v)

/-- Every hidden slot has a provider under the original uniqueness invariant;
complete public coverage then gives complete coverage of the opened forest. -/
theorem closeVars_complete (n : Nat) (a : Extended (LocalVars n V))
    (hu : (closeVars n a).UniqueDefinitions) (ha : ∀ v, (closeVars n a).Exports v) :
    a.UniqueDefinitions ∧ ∀ v, a.Exports v := by
  induction n generalizing V with
  | zero => exact ⟨hu,ha⟩
  | succ n ih =>
    apply ih a hu.1
    intro v
    cases v with
    | none => exact hu.2
    | some v => exact ha v

private theorem forest_par_prefix (a : Extended V) (ha : a.FrameForest)
    (m : Nat) (b : Extended (LocalVars m V)) (hb : b.FrameForest) :
    ∃ (k : Nat) (c : Extended (LocalVars k V)), c.FrameForest ∧
      Structural (.par a (closeVars m b)) (closeVars k c) := by
  induction m generalizing V with
  | zero => exact ⟨0,.par a b,⟨ha,hb⟩,.refl _⟩
  | succ m ih =>
    obtain ⟨k,c,hc,hs⟩ := ih (a.rename some) (ha.rename some) b hb
    exact ⟨k+1,c,hc,(Structural.newPar a (closeVars m b)).trans (.newVar hs)⟩

private theorem prefix_par_prefix (n m : Nat)
    (a : Extended (LocalVars n V)) (b : Extended (LocalVars m V))
    (ha : a.FrameForest) (hb : b.FrameForest) :
    ∃ (k : Nat) (c : Extended (LocalVars k V)), c.FrameForest ∧
      Structural (.par (closeVars n a) (closeVars m b)) (closeVars k c) := by
  induction n generalizing V with
  | zero => exact forest_par_prefix a ha m b hb
  | succ n ih =>
    obtain ⟨k,c,hc,hs⟩ := ih a (b.rename (localMap m some)) ha (hb.rename _)
    have he : Structural (.par (.newVar (closeVars n a)) (closeVars m b))
        (.newVar (.par (closeVars n a) ((closeVars m b).rename some))) :=
      (Structural.comm _ _).trans ((Structural.newPar _ _).trans
        (.newVar (Structural.comm _ _)))
    rw [closeVars_rename] at he
    exact ⟨k+1,c,hc,he.trans (.newVar hs)⟩

/-- Every original frame admits this finite prefix. No program, dependency
order, rigidity or realization assumption is supplied by the caller. -/
theorem exists_variable_frame_prefix (a : Extended V) :
    ∃ (n : Nat) (b : Extended (LocalVars n V)), b.FrameForest ∧
      Structural a.frameOf (closeVars n b) := by
  induction a with
  | plain => exact ⟨0,.plain .nil,rfl,.refl _⟩
  | active x m => exact ⟨0,.active x m,True.intro,.refl _⟩
  | newVar a ih =>
    obtain ⟨n,b,hb,hs⟩ := ih
    exact ⟨n+1,b,hb,.newVar hs⟩
  | par a b ih ij =>
    obtain ⟨n,c,hc,hs⟩ := ih
    obtain ⟨m,d,hd,ht⟩ := ij
    obtain ⟨k,e,he,hu⟩ := prefix_par_prefix n m c d hc hd
    exact ⟨k,e,he,((Structural.parLeft _ hs).trans (Structural.parRight _ ht)).trans hu⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Extract name allocation and a complete variable-prefix frame from the raw
source itself. All allocated names avoid both the caller's finite context and
the raw frame's literal names. Active equations remain unsolved. -/
theorem exists_fresh_variable_frame_prefix (a : Named V) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (n : Nat) (b : Extended (Extended.LocalVars n V)),
      b.FrameForest ∧
      (∀ x ∈ ns, x ∉ avoid ∪ a.frameOf.allNames) ∧
      Structural a.frameOf (restrictNames ns (.embed (Extended.closeVars n b))) := by
  obtain ⟨ns,c,hc,hf⟩ := exists_fresh_opening a NameAssignment.literal
    (avoid ∪ a.frameOf.allNames)
  obtain ⟨n,b,hb,hs⟩ := c.exists_variable_frame_prefix
  exact ⟨ns,n,b,hb,hf,(hc.frameOf.structural_literal (fun x hx hh =>
    hf x hx (Finset.mem_union_right _ hh))).trans ((Structural.embed hs).restrictNames ns)⟩

/-- Complete source domains and unique definitions are sufficient to extract
one provider for every local and public slot, with an actual structural path. -/
theorem exists_complete_frame_prefix (a : Named V) (hu : a.UniqueDefinitions)
    (ha : ∀ v, a.Exports v) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (n : Nat) (d : Extended (Extended.LocalVars n V)),
      d.FrameForest ∧ d.UniqueDefinitions ∧ (∀ v, d.Exports v) ∧
      (∀ x ∈ ns, x ∉ avoid ∪ a.frameOf.allNames) ∧
      Structural a.frameOf (restrictNames ns (.embed (Extended.closeVars n d))) := by
  obtain ⟨ns,n,d,hd,hf,hs⟩ := a.exists_fresh_variable_frame_prefix avoid
  have hu' := (restrictNames_uniqueDefinitions _ _).mp
    (hs.uniqueDefinitions.mp (a.frameOf_uniqueDefinitions.mpr hu))
  have hx : ∀ v, (Extended.closeVars n d).Exports v := by
    intro v
    exact (restrictNames_exports _ _ v).mp ((hs.exports v).mp
      ((a.frameOf_exports v).mpr (ha v)))
  obtain ⟨hd',hx'⟩ := Extended.closeVars_complete n d hu' hx
  exact ⟨ns,n,d,hd,hd',hx',hf,hs⟩

/-- Actual output provenance and the current presentation derive all provider
and freshness conditions for the extracted target. Values remain unsolved. -/
theorem BoundOutput.exists_complete_frame_prefix {handles : Nat}
    {r hidden : Finset Nat} {φ : Frame r handles}
    {a : Named (Fin handles)} {b : Named (Option (Fin handles))} {c : Nat}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ)
    (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (n : Nat)
      (d : Extended (Extended.LocalVars n (Option (Fin handles)))),
      d.FrameForest ∧ d.UniqueDefinitions ∧ (∀ v, d.Exports v) ∧
      (∀ x ∈ ns, x ∉ avoid ∪ b.frameOf.allNames) ∧
      Structural b.frameOf (Named.restrictNames ns (.embed (Extended.closeVars n d))) :=
  b.exists_complete_frame_prefix (h.uniqueDefinitions hp.wellFormed.1)
    (h.all_exports hp.wellFormed.1 hp.all_exports) avoid

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
