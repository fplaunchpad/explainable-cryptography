import ExplainableCrypto.Helios.Symbolic.InitialTrusteeFree

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {secret : Nat}

theorem TrusteeFreeValue.pk_iff (a : Term V) :
    TrusteeFreeValue secret (.unary .pk a) ↔ TrusteeFreeValue secret a := by
  constructor
  · intro h
    obtain ⟨u, he, hi, hf⟩ := h.normal_rep
    obtain ⟨a', rfl, ha⟩ := he.pk_irreducible_shape hi
    exact ⟨a', ha, hf⟩
  · rintro ⟨a', ha, hf⟩
    exact ⟨.unary .pk a', .unary .pk ha, hf⟩

theorem TrusteeFreeValue.penc_iff (k r p : Term V) :
    TrusteeFreeValue secret (.ternary .penc k r p) ↔
      TrusteeFreeValue secret k ∧ TrusteeFreeValue secret r ∧ TrusteeFreeValue secret p := by
  constructor
  · intro h
    obtain ⟨u, he, hi, hf⟩ := h.normal_rep
    obtain ⟨k', r', p', rfl, hk, hr, hp⟩ := he.penc_irreducible_shape hi
    exact ⟨⟨k', hk, hf.1⟩, ⟨r', hr, hf.2.1⟩, ⟨p', hp, hf.2.2⟩⟩
  · rintro ⟨⟨k', hk, hf⟩, ⟨r', hr, hg⟩, ⟨p', hp, hh⟩⟩
    exact ⟨.ternary .penc k' r' p', .ternary .penc hk hr hp, hf, hg, hh⟩

theorem TrusteeFreeValue.spk_iff (a b c d : Term V) :
    TrusteeFreeValue secret (.spk a b c d) ↔
      TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b ∧
      TrusteeFreeValue secret c ∧ TrusteeFreeValue secret d := by
  constructor
  · intro h
    obtain ⟨u, he, hi, hf⟩ := h.normal_rep
    obtain ⟨a', b', c', d', rfl, ha, hb, hc, hd⟩ := he.spk_irreducible_shape hi
    exact ⟨⟨a', ha, hf.1⟩, ⟨b', hb, hf.2.1⟩, ⟨c', hc, hf.2.2.1⟩, ⟨d', hd, hf.2.2.2⟩⟩
  · rintro ⟨⟨a', ha, hf⟩, ⟨b', hb, hg⟩, ⟨c', hc, hh⟩, ⟨d', hd, hj⟩⟩
    exact ⟨.spk a' b' c' d', .spk ha hb hc hd, hf, hg, hh, hj⟩

theorem TrusteeFreeValue.passive_iff (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (a b : Term V) :
    TrusteeFreeValue secret (.binary f a b) ↔
      TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b ∧
      (f = .partialDecrypt → ¬ EqE a (.name secret)) := by
  constructor
  · intro h
    obtain ⟨u, he, hi, hfree⟩ := h.normal_rep
    obtain ⟨a', b', rfl, ha, hb⟩ := he.passive_binary_irreducible_shape hf hi
    exact ⟨⟨a', ha, hfree.1⟩, ⟨b', hb, hfree.2.1⟩,
      fun heq hk => hfree.2.2 heq (ha.symm.trans hk)⟩
  · rintro ⟨⟨a', ha, hfree⟩, ⟨b', hb, hfree'⟩, hg⟩
    exact ⟨.binary f a' b', .binary f ha hb, hfree, hfree',
      fun heq hk => hg heq (ha.trans hk)⟩

theorem TrusteeFreeValue.add_iff (a b : Term V) :
    TrusteeFreeValue secret (.binary .add a b) ↔
      TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b := by
  constructor
  · intro h
    obtain ⟨a', ha, hna⟩ := exists_normal_form a
    obtain ⟨b', hb, hnb⟩ := exists_normal_form b
    have hf := (h.of_eq (.binary .add ha.sound hb.sound)).irreducible (hna.add hnb)
    exact ⟨⟨a', ha.sound, hf.1⟩, ⟨b', hb.sound, hf.2.1⟩⟩
  · rintro ⟨⟨a', ha, hf⟩, ⟨b', hb, hg⟩⟩
    exact ⟨.binary .add a' b', .binary .add ha hb, hf, hg, by simp⟩

theorem TrusteeFreeValue.compose_iff (a b : Term V) :
    TrusteeFreeValue secret (.binary .compose a b) ↔
      TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b := by
  constructor
  · intro h
    obtain ⟨a', ha, hna⟩ := exists_normal_form a
    obtain ⟨b', hb, hnb⟩ := exists_normal_form b
    have hf := (h.of_eq (.binary .compose ha.sound hb.sound)).irreducible (hna.compose hnb)
    exact ⟨⟨a', ha.sound, hf.1⟩, ⟨b', hb.sound, hf.2.1⟩⟩
  · rintro ⟨⟨a', ha, hf⟩, ⟨b', hb, hg⟩⟩
    exact ⟨.binary .compose a' b', .binary .compose ha hb, hf, hg, by simp⟩

end ExplainableCrypto.Helios.Symbolic
