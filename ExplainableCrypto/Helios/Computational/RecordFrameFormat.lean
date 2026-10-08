import ExplainableCrypto.Helios.Computational.ArchivedFieldMachine

/-! The complete original record reader, expressed through its field operation.
These are proof interfaces to the existing codec; its algorithm is unchanged. -/
namespace ExplainableCrypto.Helios.Computational

/-- Successful field parsing supplies exactly the original length framing. -/
theorem fieldDecode_exact (word bs suffix : List Bool)
    (h : FieldPrefixMachine.decode word = some (bs,suffix)) :
    word = uniformNatEncode bs.length ++ (bs++suffix) := by
  unfold FieldPrefixMachine.decode at h
  cases hn : uniformNatRead word with
  | none => simp [hn] at h
  | some pair =>
    rcases pair with ⟨n,rest⟩
    simp only [hn] at h
    dsimp only [Bind.bind,Option.bind] at h
    split at h
    · rename_i hl
      cases Option.some.inj h
      rw [List.take_append_drop,List.length_take_of_le hl]
      exact uniformNatRead_exact word n rest hn
    · cases h

/-- One recursive step of the original reader uses the checked field operation. -/
theorem bitFramesRead_field (n : Nat) (word : List Bool) :
    bitFramesRead (n+1) word = (do
      let (b,rest) ← FieldPrefixMachine.decode word
      let (bs,suffix) ← bitFramesRead n rest
      some (b::bs,suffix)) := by
  rw [bitFramesRead]
  unfold FieldPrefixMachine.decode
  cases hn : uniformNatRead word with
  | none => simp
  | some pair =>
    rcases pair with ⟨size,rest⟩
    by_cases h : size ≤ rest.length <;> simp [h]

/-- Internal loop specification: the original reader must consume all input;
accepted output is the original archived prefix followed by this input. -/
def recordBodyResult (n : Nat) (word archive : List Bool) : Option (List Bool) := do
  let (_,rest) ← bitFramesRead n word
  if rest = [] then some (archive.reverse++word) else none

theorem recordBodyResult_zero (word archive : List Bool) :
    recordBodyResult 0 word archive =
      if word = [] then some (archive.reverse++word) else none := rfl

theorem recordBodyResult_reject (n : Nat) (word archive : List Bool)
    (h : FieldPrefixMachine.decode word = none) :
    recordBodyResult (n+1) word archive = none := by
  simp [recordBodyResult,bitFramesRead_field,h]

theorem recordBodyResult_next (n : Nat) (word bs rest archive : List Bool)
    (h : FieldPrefixMachine.decode word = some (bs,rest)) :
    recordBodyResult (n+1) word archive =
      recordBodyResult n rest ((uniformNatEncode bs.length++bs).reverse++archive) := by
  have hw := fieldDecode_exact word bs rest h
  simp only [recordBodyResult,bitFramesRead_field,h]
  dsimp only [Bind.bind,Option.bind]
  cases hr : bitFramesRead n rest with
  | none => simp
  | some pair =>
    rcases pair with ⟨fields,suffix⟩
    simp [hw,List.append_assoc]

theorem recordBodyResult_original (word : List Bool) (n : Nat) (rest : List Bool)
    (h : uniformNatRead word = some (n,rest)) :
    recordBodyResult n rest (uniformNatEncode n).reverse =
      (bitFieldsDecode word).map (fun _ => word) := by
  have hw := uniformNatRead_exact word n rest h
  simp only [recordBodyResult,bitFieldsDecode,h]
  dsimp only [Bind.bind,Option.bind]
  cases hr : bitFramesRead n rest with
  | none => simp
  | some pair =>
    rcases pair with ⟨fields,suffix⟩
    by_cases hs : suffix = [] <;> simp [hs,hw]

#print axioms bitFramesRead_encode
#print axioms bitFramesRead_exact
#print axioms fieldDecode_exact
#print axioms bitFramesRead_field
#print axioms recordBodyResult_zero
#print axioms recordBodyResult_reject
#print axioms recordBodyResult_next
#print axioms recordBodyResult_original
end ExplainableCrypto.Helios.Computational
