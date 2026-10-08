import ExplainableCrypto.Helios.Computational.UniformOperandCodec

/-! Operational characterizations of the existing natural prefix reader.
These justify the finite parser's last-bit canonicality test without changing
its original format or decoder. -/
namespace ExplainableCrypto.Helios.Computational

theorem natPayload_canonical (n : Nat) : n.bits.reverse.head? ≠ some false := by
  rw [List.head?_reverse]
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    by_cases hn : n = 0
    · subst n
      simp [hb rfl]
    · have hne : n.bits ≠ [] := by
        intro he
        have hs : n.size = 0 := by rw [←Nat.size_eq_bits_len,he]; rfl
        exact hn (Nat.size_eq_zero.mp hs)
      rwa [List.getLast?_cons_of_ne_nil hne]

theorem natPayload_value_bits (bs : List Bool) (h : bs.reverse.head? ≠ some false) :
    (bs.foldr Nat.bit 0).bits = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases he : bs = []
    · subst bs
      cases b <;> simp_all
    · have ht : bs.reverse.head? ≠ some false := by
        simpa only [List.head?_reverse,List.getLast?_cons_of_ne_nil he] using h
      have hv := ih ht
      have hn : bs.foldr Nat.bit 0 ≠ 0 := by
        intro hz
        rw [hz,Nat.zero_bits] at hv
        exact he hv.symm
      simpa only [List.foldr_cons,hv] using
        Nat.bits_append_bit (bs.foldr Nat.bit 0) b (fun hz => (hn hz).elim)

private theorem header_unique (w v : Nat) (xs ys : List Bool)
    (h : List.replicate w true ++ false::xs = List.replicate v true ++ false::ys) :
    w = v ∧ xs = ys := by
  induction w generalizing v with
  | zero => cases v <;> simp_all [List.replicate_succ]
  | succ w ih =>
    cases v with
    | zero => simp [List.replicate_succ] at h
    | succ v =>
      simp only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] at h
      obtain ⟨rfl,rfl⟩ := ih v h
      exact ⟨rfl,rfl⟩

/-- Canonicality can be checked using the final payload bit. -/
theorem uniformNatRead_frame (bs suffix : List Bool) :
    uniformNatRead (List.replicate bs.length true ++ false::(bs++suffix)) =
      if bs.reverse.head? = some false then none
      else some (bs.foldr Nat.bit 0,suffix) := by
  split
  · rename_i hb
    cases hr : uniformNatRead (List.replicate bs.length true ++ false::(bs++suffix)) with
    | none => rfl
    | some pair =>
      obtain ⟨n,rest⟩ := pair
      have hx := uniformNatRead_exact _ n rest hr
      simp only [uniformNatEncode,List.append_assoc,List.cons_append] at hx
      obtain ⟨hlen,htail⟩ := header_unique _ _ _ _ hx
      have hp := congrArg (List.take bs.length) htail
      simp only [List.take_left,hlen] at hp
      have hp' : bs = n.bits := by simpa only [←hlen,List.take_left] using hp
      subst bs
      exact (natPayload_canonical n hb).elim
  · rename_i hb
    have he := natPayload_value_bits bs hb
    have hr := uniformNatRead_encode (bs.foldr Nat.bit 0) suffix
    simpa only [uniformNatEncode,he,List.append_assoc,List.cons_append] using hr

theorem uniformNatRead_no_delimiter (w : Nat) :
    uniformNatRead (List.replicate w true) = none := by
  cases hr : uniformNatRead (List.replicate w true) with
  | none => rfl
  | some pair =>
    obtain ⟨n,rest⟩ := pair
    have hx := uniformNatRead_exact _ n rest hr
    have hf : false ∈ List.replicate w true := by
      rw [hx]
      simp [uniformNatEncode]
    simp at hf

theorem uniformNatRead_truncated (w : Nat) (bs : List Bool) (h : bs.length < w) :
    uniformNatRead (List.replicate w true ++ false::bs) = none := by
  cases hr : uniformNatRead (List.replicate w true ++ false::bs) with
  | none => rfl
  | some pair =>
    obtain ⟨n,rest⟩ := pair
    have hx := uniformNatRead_exact _ n rest hr
    simp only [uniformNatEncode,List.append_assoc,List.cons_append] at hx
    obtain ⟨hw,hbs⟩ := header_unique _ _ _ _ hx
    have hl := congrArg List.length hbs
    simp only [List.length_append] at hl
    omega

#print axioms natPayload_canonical
#print axioms natPayload_value_bits
#print axioms uniformNatRead_frame
#print axioms uniformNatRead_no_delimiter
#print axioms uniformNatRead_truncated
end ExplainableCrypto.Helios.Computational
