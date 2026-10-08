import ExplainableCrypto.Helios.Symbolic.AdditionLeaves

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- Flatten outer addition, accounting for the known numbers published at
handles. Numeric presence, including a published zero, remains explicit. -/
def Term.addNumericSummary (ν : V → Option Nat) : Term V → AddSummary (Term V)
  | .const .zero => .number 0
  | .const .one => .number 1
  | .binary .add a b => (a.addNumericSummary ν).combine (b.addNumericSummary ν)
  | .var v => match ν v with
    | some n => .number n
    | none => .atom (.var v)
  | t => .atom t

/-- An E-equivalent value with literal numerals at the numeric leaves of the
outer addition skeleton. Other leaves retain their full substituted value. -/
def Term.addNumericValue (σ : V → Term W) (ν : V → Option Nat) : Term V → Term W
  | .const .zero => .const .zero
  | .const .one => .const .one
  | .binary .add a b => .binary .add (a.addNumericValue σ ν) (b.addNumericValue σ ν)
  | .var v => match ν v with
    | some n => addNumeral n
    | none => σ v
  | t => t.subst σ

/-- Only explicit numeric-handle equalities are needed to construct the value. -/
theorem Term.addNumericValue_eq (σ : V → Term W) (ν : V → Option Nat)
    (hn : ∀ v n, ν v = some n → EqE (σ v) (addNumeral n)) (r : Term V) :
    EqE (r.subst σ) (r.addNumericValue σ ν) := by
  induction r with
  | binary f a b ia ib =>
    cases f <;> first | exact EqE.binary .add ia ib | exact .refl _
  | const c => cases c <;> exact .refl _
  | var v =>
    simp only [Term.subst, Term.addNumericValue]
    split
    · rename_i n hv
      exact hn v n hv
    · exact .refl _
  | _ => exact .refl _

/-- Nonnumeric leaves remain actual subterms, and cannot be handles marked numeric. -/
theorem Term.addNumericSummary_mem (ν : V → Option Nat) {r a : Term V}
    (ha : a ∈ (r.addNumericSummary ν).atoms) :
    (∃ c : Context V, c.fill a = r) ∧
    (∀ x y, a ≠ .binary .add x y) ∧ a ≠ .const .zero ∧ a ≠ .const .one ∧
    (∀ v, a = .var v → ν v = none) := by
  induction r with
  | binary f x y ix iy =>
    cases f with
    | add =>
      rcases Multiset.mem_add.mp ha with hx | hy
      · obtain ⟨⟨c,hc⟩,hn⟩ := ix hx
        exact ⟨⟨.binaryLeft .add c y, by simp only [Context.fill,hc]⟩,hn⟩
      · obtain ⟨⟨c,hc⟩,hn⟩ := iy hy
        exact ⟨⟨.binaryRight .add x c, by simp only [Context.fill,hc]⟩,hn⟩
    | pair | mul | compose | partialDecrypt | dec =>
      have he := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole,rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h),
        (by intro h; cases h), (by intro _ h; cases h)⟩
  | const c =>
    cases c with
    | zero | one => exact False.elim (Multiset.notMem_zero a ha)
    | ok | bottom =>
      have he := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole,rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h),
        (by intro h; cases h), (by intro _ h; cases h)⟩
  | var v =>
    cases hv : ν v with
    | some n => simp [Term.addNumericSummary,hv,AddSummary.number] at ha
    | none =>
      have he : a = .var v := by simpa [Term.addNumericSummary,hv,AddSummary.atom] using ha
      subst a
      exact ⟨⟨.hole,rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h),
        (by intro h; cases h), (by intro _ h; cases h; exact hv)⟩
  | name | unary | ternary | spk =>
    have he := Multiset.mem_singleton.mp ha
    subst a
    exact ⟨⟨.hole,rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h),
      (by intro h; cases h), (by intro _ h; cases h)⟩

/-- Literal numerals carry no nonnumeric full-E factors. -/
theorem addNumeral_addValueSummary (number : Nat) :
    (addNumeral (V := V) number).addValueSummary = .number number := by
  induction number with
  | zero => rfl
  | succ number ih =>
    simp only [addNumeral, Term.addValueSummary, ih, AddSummary.combine_numbers]

private theorem singleton_numeric_value (σ : V → Term W) (ν : V → Option Nat) (r : Term V)
    (hr : r.addNumericSummary ν = .atom r) (hv : r.addNumericValue σ ν = r.subst σ)
    (h : ∀ a ∈ (r.addNumericSummary ν).atoms, (a.subst σ).fullClass.AddAtom) :
    (r.addNumericValue σ ν).addValueSummary =
      ⟨(r.addNumericSummary ν).atoms.map (fun a => (a.subst σ).fullClass), (r.addNumericSummary ν).numeric⟩ ∧
    (r.addNumericValue σ ν).AtomicAddFactors := by
  have he := Term.add_value_atom (h r (by rw [hr]; simp [AddSummary.atom]))
  simpa only [hv,hr,AddSummary.atom,Multiset.map_singleton] using he

/-- Numeric handles and semantic atoms give exact summary accounting for an
E-equivalent value; the raw published decryption need not itself be atomic. -/
theorem Term.addNumericValue_summary (σ : V → Term W) (ν : V → Option Nat) (r : Term V)
    (h : ∀ a ∈ (r.addNumericSummary ν).atoms, (a.subst σ).fullClass.AddAtom) :
    (r.addNumericValue σ ν).addValueSummary =
      ⟨(r.addNumericSummary ν).atoms.map (fun a => (a.subst σ).fullClass), (r.addNumericSummary ν).numeric⟩ ∧
    (r.addNumericValue σ ν).AtomicAddFactors := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | add =>
      have ha := ia (fun x hx => h x (Multiset.mem_add.mpr (Or.inl hx)))
      have hb := ib (fun x hx => h x (Multiset.mem_add.mpr (Or.inr hx)))
      refine ⟨?_, ?_⟩
      · simp only [Term.addNumericValue,Term.addValueSummary,Term.addNumericSummary,
          ha.1,hb.1,AddSummary.combine,Multiset.map_add]
      · intro q hq
        rcases Multiset.mem_add.mp hq with hqa | hqb
        · exact ha.2 q hqa
        · exact hb.2 q hqb
    | pair | mul | compose | partialDecrypt | dec => exact singleton_numeric_value σ ν _ rfl rfl h
  | const c =>
    cases c with
    | zero | one => exact ⟨rfl, by intro q hq; exact False.elim (Multiset.notMem_zero q hq)⟩
    | ok | bottom => exact singleton_numeric_value σ ν _ rfl rfl h
  | var v =>
    cases hv : ν v with
    | none =>
      exact singleton_numeric_value σ ν _ (by simp [Term.addNumericSummary,hv])
        (by simp [Term.addNumericValue,Term.subst,hv]) h
    | some number =>
      constructor
      · simp [Term.addNumericValue,Term.addNumericSummary,hv,addNumeral_addValueSummary,AddSummary.number]
      · intro q hq
        simp [Term.addNumericValue,hv,addNumeral_addValueSummary,AddSummary.number] at hq
  | _ => exact singleton_numeric_value σ ν _ rfl rfl h

end ExplainableCrypto.Helios.Symbolic
