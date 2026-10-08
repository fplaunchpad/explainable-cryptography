import ExplainableCrypto.Helios.Symbolic.SourceNameSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Explicit name and variable restrictions in source evaluation contexts.
Leaves reuse the checked finite variable/active fragment. Restrictions beneath
plain input/output/conditional prefixes and replication are not added here. -/
inductive Named : Type → Type 1 where
  | embed : Extended V → Named V
  | par : Named V → Named V → Named V
  | newName : SourceName → Named V → Named V
  | newVar : Named (Option V) → Named V

namespace Named

def freeNames : {V : Type} → Named V → Finset SourceName
  | _, .embed a => a.nameSupport
  | _, .par a b => a.freeNames ∪ b.freeNames
  | _, .newName n a => a.freeNames.erase n
  | _, .newVar a => a.freeNames

/-- Including nested binders gives a conservative, capture-free alpha rule. -/
def allNames : {V : Type} → Named V → Finset SourceName
  | _, .embed a => a.nameSupport
  | _, .par a b => a.allNames ∪ b.allNames
  | _, .newName n a => insert n a.allNames
  | _, .newVar a => a.allNames

def mapNames : {V : Type} → (Nat → Nat) → (Nat → Nat) → Named V → Named V
  | _, f, g, .embed a => .embed (a.mapNames f g)
  | _, f, g, .par a b => .par (a.mapNames f g) (b.mapNames f g)
  | _, f, g, .newName n a => .newName (n.map f g) (a.mapNames f g)
  | _, f, g, .newVar a => .newVar (a.mapNames f g)

def rename : {V W : Type} → (V → W) → Named V → Named W
  | _, _, σ, .embed a => .embed (a.rename σ)
  | _, _, σ, .par a b => .par (a.rename σ) (b.rename σ)
  | _, _, σ, .newName n a => .newName n (a.rename σ)
  | _, _, σ, .newVar a => .newVar (a.rename (Option.map σ))

theorem mapNames_inverse (a : Named V) (e k : Nat ≃ Nat) :
    (a.mapNames e k).mapNames e.symm k.symm = a := by
  induction a with
  | embed a => simp only [mapNames,Extended.mapNames_inverse]
  | par a b ha hb => simp only [mapNames,ha,hb]
  | newVar a ha => simp only [mapNames,ha]
  | newName n a ha => cases n <;> simp only [mapNames,SourceName.map,ha,Equiv.symm_apply_apply]

theorem mapNames_rename (a : Named V) (f g : Nat → Nat) (σ : V → W) :
    (a.rename σ).mapNames f g = (a.mapNames f g).rename σ := by
  induction a generalizing W with
  | embed a => simp only [rename,mapNames,Extended.mapNames_rename]
  | par a b ha hb => simp only [rename,mapNames,ha,hb]
  | newName n a ha => simp only [rename,mapNames,ha]
  | newVar a ha => simp only [rename,mapNames,ha]

/-- The source name rules and evaluation-context closures are explicit.
Same-sort alpha conversion uses a name absent even from nested binders. -/
inductive Structural : {V : Type} → Named V → Named V → Prop where
  | refl (a : Named V) : Structural a a
  | symm {a b : Named V} : Structural a b → Structural b a
  | trans {a b c : Named V} : Structural a b → Structural b c → Structural a c
  | embed {a b : Extended V} : Extended.Structural a b → Structural (.embed a) (.embed b)
  | parLeft {a b : Named V} (c : Named V) : Structural a b → Structural (.par a c) (.par b c)
  | parRight (a : Named V) {b c : Named V} : Structural b c → Structural (.par a b) (.par a c)
  | newName (n : SourceName) {a b : Named V} : Structural a b → Structural (.newName n a) (.newName n b)
  | newVar {a b : Named (Option V)} : Structural a b → Structural (.newVar a) (.newVar b)
  | embedPar (a b : Extended V) : Structural (.embed (.par a b)) (.par (.embed a) (.embed b))
  | embedVar (a : Extended (Option V)) : Structural (.embed (.newVar a)) (.newVar (.embed a))
  | zero (a : Named V) : Structural (.par a (.embed (.plain .nil))) a
  | assoc (a b c : Named V) : Structural (.par (.par a b) c) (.par a (.par b c))
  | comm (a b : Named V) : Structural (.par a b) (.par b a)
  | nameZero (n : SourceName) : Structural (.newName n (.embed (.plain .nil) : Named V)) (.embed (.plain .nil))
  | nameComm (n m : SourceName) (a : Named V) :
      Structural (.newName n (.newName m a)) (.newName m (.newName n a))
  | nameVarComm (n : SourceName) (a : Named (Option V)) :
      Structural (.newName n (.newVar a)) (.newVar (.newName n a))
  | varComm (a : Named (Option (Option V))) :
      Structural (.newVar (.newVar a)) (.newVar (.newVar (a.rename Extended.swapBinders)))
  | namePar (a : Named V) (n : SourceName) (b : Named V) (hf : n ∉ a.freeNames) :
      Structural (.par a (.newName n b)) (.newName n (.par a b))
  | varPar (a : Named V) (b : Named (Option V)) :
      Structural (.par a (.newVar b)) (.newVar (.par (a.rename some) b))
  | alphaBase (a : Named V) (n m : Nat) (hf : SourceName.base m ∉ a.allNames) :
      Structural (.newName (.base n) a) (.newName (.base m) (a.mapNames (Equiv.swap n m) id))
  | alphaChannel (a : Named V) (n m : Nat) (hf : SourceName.channel m ∉ a.allNames) :
      Structural (.newName (.channel n) a) (.newName (.channel m) (a.mapNames id (Equiv.swap n m)))

def restrictNames (ns : List SourceName) (a : Named V) : Named V := ns.foldr Named.newName a

theorem restrictNames_rename (ns : List SourceName) (a : Named V) (σ : V → W) :
    (restrictNames ns a).rename σ = restrictNames ns (a.rename σ) := by
  induction ns <;> simp_all only [restrictNames,List.foldr,rename]

theorem Structural.restrictNames {a b : Named V} (h : Structural a b) (ns : List SourceName) :
    Structural (Named.restrictNames ns a) (Named.restrictNames ns b) := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact .newName n ih
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
