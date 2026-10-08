import ExplainableCrypto.Helios.Symbolic.SourceWellFormedPreservation

namespace ExplainableCrypto.Helios.Symbolic
namespace Term
variable {V W : Type}

/-- Literal names move; variables and every operator/argument position remain. -/
def mapNames (f : Nat → Nat) : Term V → Term V
  | .name n => .name (f n)
  | .var v => .var v
  | .const c => .const c
  | .unary op a => .unary op (a.mapNames f)
  | .binary op a b => .binary op (a.mapNames f) (b.mapNames f)
  | .ternary op a b c => .ternary op (a.mapNames f) (b.mapNames f) (c.mapNames f)
  | .spk a b c d => .spk (a.mapNames f) (b.mapNames f) (c.mapNames f) (d.mapNames f)

theorem mapNames_id (t : Term V) : t.mapNames id = t := by
  induction t <;> simp_all [mapNames]

theorem mapNames_comp (t : Term V) (f g : Nat → Nat) :
    (t.mapNames f).mapNames g = t.mapNames (g ∘ f) := by
  induction t <;> simp_all [mapNames]

theorem mapNames_subst (t : Term V) (f : Nat → Nat) (σ : V → Term W) :
    (t.subst σ).mapNames f = (t.mapNames f).subst (fun v => (σ v).mapNames f) := by
  induction t <;> simp_all [mapNames,subst]

theorem mapNames_inverse (t : Term V) (e : Nat ≃ Nat) :
    (t.mapNames e).mapNames e.symm = t := by
  rw [mapNames_comp]
  have he : (e.symm ∘ e : Nat → Nat) = id := by funext v; exact e.symm_apply_apply v
  rw [he,mapNames_id]

/-- Publicness is invariant when the restricted-name policy is renamed too. -/
theorem public_mapNames_iff (t : Term V) (e : Nat ≃ Nat) (restricted : Finset Nat) :
    (t.mapNames e).Public (restricted.image e) ↔ t.Public restricted := by
  induction t with
  | name n => simp [mapNames,Public,e.injective.eq_iff]
  | var v => rfl
  | const c => rfl
  | unary op a ha => exact ha
  | binary op a b ha hb => exact and_congr ha hb
  | ternary op a b c ha hb hc => exact and_congr ha (and_congr hb hc)
  | spk a b c d ha hb hc hd => exact and_congr ha (and_congr hb (and_congr hc hd))
end Term
variable {V : Type}

/-- All source equations are stable even under a noninjective name map;
reflection and negative observations require bijectivity. -/
theorem Equation.mapNames {a b : Term V} (h : Equation a b) (f : Nat → Nat) :
    Equation (a.mapNames f) (b.mapNames f) := by
  cases h <;> simp only [Term.mapNames] <;> constructor <;> assumption

theorem EqE.mapNames {a b : Term V} (h : EqE a b) (f : Nat → Nat) :
    EqE (a.mapNames f) (b.mapNames f) := by
  induction h with
  | equation h => exact .equation (h.mapNames f)
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | unary op h ih => exact .unary op ih
  | binary op h h' ih ih' => exact .binary op ih ih'
  | ternary op h h' h'' ih ih' ih'' => exact .ternary op ih ih' ih''
  | spk h h' h'' h''' ih ih' ih'' ih''' => exact .spk ih ih' ih'' ih'''

theorem EqE.mapNames_iff (a b : Term V) (e : Nat ≃ Nat) :
    EqE (a.mapNames e) (b.mapNames e) ↔ EqE a b := by
  constructor
  · intro h
    simpa only [Term.mapNames_inverse] using h.mapNames e.symm
  · exact fun h => h.mapNames e
end ExplainableCrypto.Helios.Symbolic
