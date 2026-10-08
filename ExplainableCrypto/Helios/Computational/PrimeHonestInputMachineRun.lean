import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine
open Turing.TM2
set_option maxRecDepth 16384

private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel 0 (copyProgram l) := by fin_cases l <;> rfl
private theorem field_code (phase : Fin 7) (l : Fin 9) : program (fieldLabel phase l) =
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase) (fieldProgram phase l) := by
  fin_cases phase <;> fin_cases l <;> rfl
private theorem parse_code (phase : Fin 3) (l : Fin 3) : program (parseLabel phase l) =
    TM2ReturnLink.redirect (parseLabel phase) (parseReturn phase) (parseProgram phase l) := by
  fin_cases phase <;> fin_cases l <;> rfl

private def state (l : Option (Fin 97)) (raw pair temp modulus g pk record vote context : List Bool)
    (v : Fin 3 := 0) : Config :=
  ⟨l,v,![[],[],[],[],[],[],modulus,raw,temp,pair,[],[],[],[],context,pk,g,[],vote,record,[],[],[]]⟩

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

private theorem copy_run (raw : List Bool) :
    ∃ used ≤ 2*raw.length+2,
      tick^[used] (start raw) = state (some 0) raw [] [] [] [] [] [] [] raw := by
  let initial := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory (BitCopyMachine.config (some false) raw [] [])
  let final := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory (BitCopyMachine.config none raw raw [])
  have hi : (TM2ReturnLink.tick (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program))^[2*raw.length+2]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*raw.length+2]
      (BitCopyMachine.config (some false) raw [] []) =
      BitCopyMachine.config none raw (raw++[]) [] from BitCopyMachine.run raw [] none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run copyLayout
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program)
    (2*raw.length+2) initial (fun _ => [])
  rw [hi] at hf
  change (TM2ReturnLink.tick copyProgram)^[2*raw.length+2]
    (TM2StackFrame.embed copyLayout initial (fun _ => [])) = TM2StackFrame.embed copyLayout final (fun _ => []) at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel 0 copy_code
    (2*raw.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed copyLabel 0 (TM2StackFrame.embed copyLayout initial (fun _ => [])) = start raw := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed copyLabel 0 (TM2StackFrame.embed copyLayout final (fun _ => [])) =
      state (some 0) raw [] [] [] [] [] [] [] raw := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private def framedWord (payload suffix : List Bool) := uniformNatEncode payload.length ++ (payload++suffix)
private def beforeField (phase : Fin 7) (payload suffix raw pair modulus g pk record vote context : List Bool) : Config :=
  state (some (fieldLabel phase 0))
    (![framedWord payload suffix,framedWord payload suffix,raw,raw,framedWord payload suffix,framedWord payload suffix,framedWord payload suffix] phase)
    (![pair,[],framedWord payload suffix,framedWord payload suffix,pair,pair,pair] phase) [] modulus g pk
    (![record,record,record,record,[],record,record] phase)
    (![vote,vote,vote,vote,vote,[],vote] phase) context
private def afterField (phase : Fin 7) (payload suffix raw pair modulus g pk record vote context : List Bool) : Config :=
  state (some (fieldReturn phase)) (![suffix,suffix,raw,raw,suffix,suffix,suffix] phase)
    (![pair,payload,suffix,suffix,pair,pair,pair] phase) (![payload,[],payload,payload,[],[],payload] phase)
    modulus g pk (![record,record,record,record,payload,record,record] phase)
    (![vote,vote,vote,vote,vote,payload,vote] phase) context 2

private def fieldBound (payload : List Bool) :=
  3*payload.length.size+7+payload.length*(2*payload.length.size+3)

private theorem field_run (phase : Fin 7)
    (payload suffix raw pair modulus g pk record vote context : List Bool) :
    ∃ used ≤ fieldBound payload,
      tick^[used] (beforeField phase payload suffix raw pair modulus g pk record vote context) =
        afterField phase payload suffix raw pair modulus g pk record vote context := by
  let source := FieldPrefixMachine.start (framedWord payload suffix)
  let target : FieldPrefixMachine.Config :=
    ⟨none,some true,(FieldReadMachine.config none payload [] suffix [] (some true)).stk⟩
  let frame : Fin 19 → List Bool := fun k =>
    (beforeField phase payload suffix raw pair modulus g pk record vote context).stk (fieldLayout phase (.inr k))
  obtain ⟨fuel,hfuel,hi⟩ := RecordFieldStepMachine.field_complete payload suffix
  change FieldPrefixMachine.tick^[fuel] source = target at hi
  have hf := TM2StackFrame.run (fieldLayout phase) FieldPrefixMachine.program fuel source frame
  change _ = TM2StackFrame.embed (fieldLayout phase) (FieldPrefixMachine.tick^[fuel] source) frame at hf
  rw [hi] at hf
  have hc := TM2FiniteCoordinates.run (Equiv.refl (Fin 23)) CacheRequestInput.labels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (fieldLayout phase) (FieldPrefixMachine.program l)) fuel
    (TM2StackFrame.embed (fieldLayout phase) source frame)
  rw [hf] at hc
  change (TM2ReturnLink.tick (fieldProgram phase))^[fuel] _ = _ at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (fieldProgram phase) program (fieldLabel phase) (fieldReturn phase)
    (field_code phase) fuel _ (by rw [hc]; rfl)
  rw [hc] at he
  have hs : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) CacheRequestInput.labels BinaryModuloCode.memory
        (TM2StackFrame.embed (fieldLayout phase) source frame)) =
      beforeField phase payload suffix raw pair modulus g pk record vote context := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) CacheRequestInput.labels BinaryModuloCode.memory
        (TM2StackFrame.embed (fieldLayout phase) target frame)) =
      afterField phase payload suffix raw pair modulus g pk record vote context := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu.trans hfuel,by rwa [hs,ht] at he⟩

private theorem parse_run (phase : Fin 3) (n : Nat)
    (raw pair modulus g pk record vote context : List Bool) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (state (some (parseLabel phase 0)) raw pair (uniformNatEncode n)
        (![[],modulus,modulus] phase) (![g,[],g] phase) (![pk,pk,[]] phase) record vote context) =
      state (some (parseReturn phase)) raw pair []
        (![n.bits,modulus,modulus] phase) (![g,n.bits,g] phase) (![pk,pk,n.bits] phase) record vote context 2 := by
  let source := NatPrefixMachine.start (uniformNatEncode n)
  let target := NatPrefixMachine.config none [] [] [] n.bits (some true)
  let base := state none raw pair (uniformNatEncode n)
    (![[],modulus,modulus] phase) (![g,[],g] phase) (![pk,pk,[]] phase) record vote context
  let frame : Fin 19 → List Bool := fun k => base.stk (parseLayout phase (.inr k))
  have hi := NatPrefixMachine.encoded_run n []
  simp only [List.append_nil] at hi
  change NatPrefixMachine.tick^[3*n.size+3] source = target at hi
  have hf := TM2StackFrame.run (parseLayout phase) NatPrefixMachine.program (3*n.size+3) source frame
  change _ = TM2StackFrame.embed (parseLayout phase) (NatPrefixMachine.tick^[3*n.size+3] source) frame at hf
  rw [hi] at hf
  have hc := TM2FiniteCoordinates.run (Equiv.refl (Fin 23)) PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (parseLayout phase) (NatPrefixMachine.program l)) (3*n.size+3)
    (TM2StackFrame.embed (parseLayout phase) source frame)
  rw [hf] at hc
  change (TM2ReturnLink.tick (parseProgram phase))^[3*n.size+3] _ = _ at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (parseProgram phase) program (parseLabel phase) (parseReturn phase)
    (parse_code phase) (3*n.size+3) _ (by rw [hc]; rfl)
  rw [hc] at he
  have hs : TM2ReturnLink.embed (parseLabel phase) (parseReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
        (TM2StackFrame.embed (parseLayout phase) source frame)) =
      state (some (parseLabel phase 0)) raw pair (uniformNatEncode n)
        (![[],modulus,modulus] phase) (![g,[],g] phase) (![pk,pk,[]] phase) record vote context := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (parseLabel phase) (parseReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
        (TM2StackFrame.embed (parseLayout phase) target frame)) =
      state (some (parseReturn phase)) raw pair []
        (![n.bits,modulus,modulus] phase) (![g,n.bits,g] phase) (![pk,pk,n.bits] phase) record vote context 2 := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem outer_header (raw context : List Bool) :
    tick^[7] (state (some 0) (uniformNatEncode 5++raw) [] [] [] [] [] [] [] context) =
      state (some (fieldLabel 0 0)) raw [] [] [] [] [] [] [] context := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl
private theorem pair_header (raw pair modulus g pk record vote context : List Bool) :
    tick^[5] (state (some 10) raw (uniformNatEncode 2++pair) [] modulus g pk record vote context) =
      state (some (fieldLabel 2 0)) raw pair [] modulus g pk record vote context := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl
private theorem field_guard (phase : Fin 5) (raw pair temp modulus g pk record vote context : List Bool) :
    tick^[1] (state (some (![7,9,15,17,19] phase)) raw pair temp modulus g pk record vote context 2) =
      state (some (![parseLabel 0 0,10,parseLabel 1 0,parseLabel 2 0,fieldLabel 5 0] phase))
        raw pair temp modulus g pk record vote context := by
  fin_cases phase <;> rfl
private theorem parse_guard (phase : Fin 3) (raw pair modulus g pk record vote context : List Bool) :
    tick^[1] (state (some (parseReturn phase)) raw (![pair,pair,[]] phase) [] modulus g pk record vote context 2) =
      state (some (![fieldLabel 1 0,fieldLabel 3 0,fieldLabel 4 0] phase))
        raw (![pair,pair,[]] phase) [] modulus g pk record vote context := by
  fin_cases phase <;> rfl
private theorem vote_guard (raw pair modulus g pk record context : List Bool) (vote : Bool) :
    tick^[1] (state (some 20) raw pair [] modulus g pk record [vote] context 2) =
      state (some (fieldLabel 6 0)) raw pair [] modulus g pk record [vote] context := by
  cases vote <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem final_guard (saved modulus g pk record vote context : List Bool) :
    tick^[1] (state (some 21) [] [] saved modulus g pk record vote context 2) =
      state (some 22) [] [] saved modulus g pk record vote context := rfl
private theorem clear_saved (saved modulus g pk record vote context : List Bool) (v : Fin 3) :
    tick^[saved.length+1] (state (some 22) [] [] saved modulus g pk record vote context v) =
      state none [] [] [] modulus g pk record vote context 2 := by
  induction saved generalizing v with
  | nil =>
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  | cons b saved ih =>
    have h : tick (state (some 22) [] [] (b::saved) modulus g pk record vote context v) =
        state (some 22) [] [] saved modulus g pk record vote context (if b then 2 else 1) := by
      cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      all_goals congr 1; funext k; fin_cases k <;> rfl
    rw [List.length_cons,Function.iterate_succ_apply,h,ih]

private def keyWord (g pk : Nat) := uniformNatEncode 2 ++ framedWord (uniformNatEncode g) (framedWord (uniformNatEncode pk) [])
private def outerTail (record : List Bool) (vote : Bool) (saved : List Bool) :=
  framedWord record (framedWord [vote] (framedWord saved []))

private theorem parameters_run (p g pk : Nat) (tail context : List Bool) :
    ∃ used ≤ fieldBound (uniformNatEncode p)+fieldBound (keyWord g pk)+
        fieldBound (uniformNatEncode g)+fieldBound (uniformNatEncode pk)+
        3*p.size+3*g.size+3*pk.size+21,
      tick^[used] (state (some (fieldLabel 0 0))
        (framedWord (uniformNatEncode p) (framedWord (keyWord g pk) tail)) [] [] [] [] [] [] [] context) =
      state (some (fieldLabel 4 0)) tail [] [] p.bits g.bits pk.bits [] [] context := by
  obtain ⟨a,ha,h0⟩ := field_run 0 (uniformNatEncode p) (framedWord (keyWord g pk) tail) [] [] [] [] [] [] [] context
  have h1 := field_guard 0 (framedWord (keyWord g pk) tail) [] (uniformNatEncode p) [] [] [] [] [] context
  obtain ⟨b,hb,h2⟩ := parse_run 0 p (framedWord (keyWord g pk) tail) [] [] [] [] [] [] context
  have h3 := parse_guard 0 (framedWord (keyWord g pk) tail) [] p.bits [] [] [] [] context
  obtain ⟨c,hc,h4⟩ := field_run 1 (keyWord g pk) tail [] [] p.bits [] [] [] [] context
  have h5 := field_guard 1 tail (keyWord g pk) [] p.bits [] [] [] [] context
  have h6 := pair_header tail (framedWord (uniformNatEncode g) (framedWord (uniformNatEncode pk) [])) p.bits [] [] [] [] context
  obtain ⟨d,hd,h7⟩ := field_run 2 (uniformNatEncode g) (framedWord (uniformNatEncode pk) []) tail [] p.bits [] [] [] [] context
  have h8 := field_guard 2 tail (framedWord (uniformNatEncode pk) []) (uniformNatEncode g) p.bits [] [] [] [] context
  obtain ⟨e,he,h9⟩ := parse_run 1 g tail (framedWord (uniformNatEncode pk) []) p.bits [] [] [] [] context
  have h10 := parse_guard 1 tail (framedWord (uniformNatEncode pk) []) p.bits g.bits [] [] [] context
  obtain ⟨f,hf,h11⟩ := field_run 3 (uniformNatEncode pk) [] tail [] p.bits g.bits [] [] [] context
  have h12 := field_guard 3 tail [] (uniformNatEncode pk) p.bits g.bits [] [] [] context
  obtain ⟨j,hj,h13⟩ := parse_run 2 pk tail [] p.bits g.bits [] [] [] context
  have h14 := parse_guard 2 tail [] p.bits g.bits pk.bits [] [] context
  have h := sequence h0 (sequence h1 (sequence h2 (sequence h3 (sequence h4
    (sequence h5 (sequence h6 (sequence h7 (sequence h8 (sequence h9 (sequence h10
      (sequence h11 (sequence h12 (sequence h13 h14)))))))))))))
  refine ⟨j+f+e+d+c+b+a+12,by omega,?_⟩
  simpa [beforeField,afterField,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

private theorem trailing_run (modulus g pk record context saved : List Bool) (vote : Bool) :
    ∃ used ≤ fieldBound record+fieldBound [vote]+fieldBound saved+saved.length+4,
      tick^[used] (state (some (fieldLabel 4 0)) (outerTail record vote saved) [] [] modulus g pk [] [] context) =
      result modulus g pk record context vote := by
  obtain ⟨a,ha,h0⟩ := field_run 4 record (framedWord [vote] (framedWord saved [])) [] [] modulus g pk [] [] context
  have h1 := field_guard 4 (framedWord [vote] (framedWord saved [])) [] [] modulus g pk record [] context
  obtain ⟨b,hb,h2⟩ := field_run 5 [vote] (framedWord saved []) [] [] modulus g pk record [] context
  have h3 := vote_guard (framedWord saved []) [] modulus g pk record context vote
  obtain ⟨c,hc,h4⟩ := field_run 6 saved [] [] [] modulus g pk record [vote] context
  have h5 := final_guard saved modulus g pk record [vote] context
  have h6 := clear_saved saved modulus g pk record [vote] context 0
  have h := sequence h0 (sequence h1 (sequence h2 (sequence h3 (sequence h4 (sequence h5 h6)))))
  refine ⟨saved.length+c+b+a+4,by omega,?_⟩
  simpa [beforeField,afterField,outerTail,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,state,result] using h

private theorem keyWord_eq (g pk : Nat) :
    keyWord g pk = bitFieldsEncode [uniformNatEncode g,uniformNatEncode pk] := by
  simp [keyWord,framedWord,bitFieldsEncode,bitFramesEncode,List.append_assoc]
private def encodedInput (p g pk : Nat) (record : List Bool) (vote : Bool) (saved : List Bool) :=
  bitFieldsEncode [uniformNatEncode p,keyWord g pk,record,[vote],saved]
private theorem encoded_shape (p g pk : Nat) (record : List Bool) (vote : Bool) (saved : List Bool) :
    encodedInput p g pk record vote saved = uniformNatEncode 5 ++
      framedWord (uniformNatEncode p) (framedWord (keyWord g pk) (outerTail record vote saved)) := by
  simp [encodedInput,framedWord,outerTail,bitFieldsEncode,bitFramesEncode,List.append_assoc]

private theorem length_bounds (p g pk : Nat) (record : List Bool) (vote : Bool) (saved : List Bool) :
    let N := (encodedInput p g pk record vote saved).length
    p.size ≤ N ∧ g.size ≤ N ∧ pk.size ≤ N ∧
    (uniformNatEncode p).length ≤ N ∧ (keyWord g pk).length ≤ N ∧
    (uniformNatEncode g).length ≤ N ∧ (uniformNatEncode pk).length ≤ N ∧
    record.length ≤ N ∧ [vote].length ≤ N ∧ saved.length ≤ N := by
  have ho := bitFieldsEncode_length [uniformNatEncode p,keyWord g pk,record,[vote],saved]
  change (encodedInput p g pk record vote saved).length = _ at ho
  have hk := bitFieldsEncode_length [uniformNatEncode g,uniformNatEncode pk]
  rw [←keyWord_eq] at hk
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    uniformNatEncode_length] at ho hk ⊢
  omega

private theorem field_bound (payload : List Bool) (N : Nat) (h : payload.length ≤ N) :
    fieldBound payload ≤ 2*N*N+6*N+7 := by
  have hw : payload.length.size ≤ N := (Nat.size_le.mpr payload.length.lt_two_pow_self).trans h
  have hm := Nat.mul_le_mul h (show 2*payload.length.size+3 ≤ 2*N+3 by omega)
  unfold fieldBound
  nlinarith

private theorem run_encoded (p g pk : Nat) (record : List Bool) (vote : Bool) (saved : List Bool) :
    ∃ used ≤ clock (encodedInput p g pk record vote saved),
      tick^[used] (start (encodedInput p g pk record vote saved)) =
      result p.bits g.bits pk.bits record (encodedInput p g pk record vote saved) vote := by
  let word := encodedInput p g pk record vote saved
  obtain ⟨u,hu,hcopy⟩ := copy_run word
  have houter := outer_header
    (framedWord (uniformNatEncode p) (framedWord (keyWord g pk) (outerTail record vote saved))) word
  rw [←encoded_shape] at houter
  obtain ⟨v,hv,hparams⟩ := parameters_run p g pk (outerTail record vote saved) word
  obtain ⟨w,hw,htrail⟩ := trailing_run p.bits g.bits pk.bits record word saved vote
  have he := sequence hcopy (sequence houter (sequence hparams htrail))
  obtain ⟨hp,hg,hpk,hpF,hkey,hgF,hpkF,hrec,hvote,hsaved⟩ := length_bounds p g pk record vote saved
  have fp := field_bound (uniformNatEncode p) word.length hpF
  have fk := field_bound (keyWord g pk) word.length hkey
  have fg := field_bound (uniformNatEncode g) word.length hgF
  have fpk := field_bound (uniformNatEncode pk) word.length hpkF
  have fr := field_bound record word.length hrec
  have fv := field_bound [vote] word.length hvote
  have fs := field_bound saved word.length hsaved
  refine ⟨w+v+7+u,?_,?_⟩
  · change w+v+7+u ≤ 14*word.length*word.length+54*word.length+83
    change p.size ≤ word.length at hp
    change g.size ≤ word.length at hg
    change pk.size ≤ word.length at hpk
    change saved.length ≤ word.length at hsaved
    nlinarith
  · simpa only [Nat.add_assoc] using he

private theorem input_encoded {p q : Nat} [NeZero p] [NeZero q]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    input g pk slack vote saved = encodedInput p (primeGroupCoordinate g).val
      (primeGroupCoordinate pk).val (SamplerOperands.input slack q []) vote saved := by
  change bitFieldsEncode [uniformNatEncode p,
    bitFieldsEncode [uniformNatEncode (primeGroupCoordinate g).val,uniformNatEncode (primeGroupCoordinate pk).val],
    SamplerOperands.input slack q [],[vote],saved] = _
  rw [←keyWord_eq]
  rfl

/-- Original typed source input is executed from otherwise blank source ports.
Both coordinates, p, the sampler record and private vote are derived by parsing;
the complete original input is retained privately and every work port clears. -/
theorem run {p q : Nat} [NeZero p] [NeZero q]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    ∃ used ≤ clock (input g pk slack vote saved),
      tick^[used] (start (input g pk slack vote saved)) =
      result p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        (SamplerOperands.input slack q []) (input g pk slack vote saved) vote := by
  rw [input_encoded]
  exact run_encoded p (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    (SamplerOperands.input slack q []) vote saved

/-- Unused analytical clock is spent only after the initializer has halted. -/
theorem padded_run {p q : Nat} [NeZero p] [NeZero q]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    tick^[clock (input g pk slack vote saved)] (start (input g pk slack vote saved)) =
      result p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        (SamplerOperands.input slack q []) (input g pk slack vote saved) vote := by
  obtain ⟨u,hu,he⟩ := run g pk slack vote saved
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

/-- Finite instruction audit includes nested headers and all rejection branches. -/
theorem local_cost (l : Fin 97) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Derived charged execution for the original typed startup word. -/
theorem charged {p q : Nat} [NeZero p] [NeZero q]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    ∃ charge ≤ 32*clock (input g pk slack vote saved),
      BitOracleMachine.run code (clock (input g pk slack vote saved))
        (start (input g pk slack vote saved)) =
      pure (result p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        (SamplerOperands.input slack q []) (input g pk slack vote saved) vote,charge) := by
  obtain ⟨c,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock (input g pk slack vote saved)) (start (input g pk slack vote saved))
  refine ⟨c,hc,?_⟩
  change BitOracleMachine.run code (clock (input g pk slack vote saved))
    (start (input g pk slack vote saved)) =
    pure (tick^[clock (input g pk slack vote saved)] (start (input g pk slack vote saved)),c) at he
  rw [he,padded_run g pk slack vote saved]

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine
