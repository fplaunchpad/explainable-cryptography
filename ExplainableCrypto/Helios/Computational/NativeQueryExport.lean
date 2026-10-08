import ExplainableCrypto.Helios.Computational.BitTapeCoverage

/-! Preserving contiguous-word extraction from the existing tagged cell encoding.
This core receives an encoded cell list. Its enclosing adapter must execute the
head-register preparation before claiming a BitTapeCoverage.present entry.
The blank cell and every later encoded bit are left untouched by the scan. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryExport
open Turing.TM2 OracleComp OracleSpec
abbrev Cell := Option Bool
abbrev Config := BitOracleMachine.Config 3 2 3
abbrev Statement := Stmt (fun _ : Fin 3 => Bool) (Fin 2) (Fin 3)

/-- Contiguous native word, ending at the first blank cell. -/
def wordPrefix : List Cell → List Bool
  | [] | none::_ => []
  | some b::rest => b::wordPrefix rest

/-- Collect only nonblank payloads, then restore their original tagged cells
while reversing the same payloads into the output word. -/
def program : Fin 2 → Statement := fun label => if label = 0 then
    .peek 0 (fun _ b => BitTapeCoverage.cellCode b)
      (.branch (fun v => v = 2)
        (.pop 0 (fun v _ => v)
          (.pop 0 (fun _ b => BitTapeCoverage.cellCode b)
            (.push 2 (fun v => v = 2) (.goto (fun _ => 0)))))
        (.goto (fun _ => 1)))
  else
    .pop 2 (fun _ b => BitTapeCoverage.cellCode b)
      (.branch (fun v => v ≠ 0)
        (.push 0 (fun v => v = 2)
          (.push 0 (fun _ => true)
            (.push 1 (fun v => v = 2) (.goto (fun _ => 1)))))
        (.load (fun _ => 0) .halt))

def code : BitOracleMachine.Code 3 2 3 := fun label => .compute (program label)

def state (label : Option (Fin 2)) (source output scratch : List Bool) (v : Fin 3 := 0) : Config :=
  ⟨label,v,![source,output,scratch]⟩

def start (word : List Cell) (suffix : List Bool := []) (v : Fin 3 := 0) : Config :=
  state (some 0) (BitTapeCoverage.cells word) suffix [] v

def result (word : List Cell) (suffix : List Bool := []) : Config :=
  state none (BitTapeCoverage.cells word) (wordPrefix word++suffix) []

def clock (word : List Cell) : Nat := 2*word.length+2

def cost (word : List Cell) : Nat := 6*clock word

/-- Syntactic local charge includes both branches, even the stopping branch. -/
theorem local_cost (label : Fin 2) : BitOracleMachine.localCost (program label) = 6 := by
  fin_cases label <;> rfl

abbrev tick := TM2ReturnLink.tick program

private def stopTail : List Cell → List Cell
  | [] => []
  | none::rest => none::rest
  | some _::rest => stopTail rest

private theorem word_decomposition (word : List Cell) :
    (wordPrefix word).map some ++ stopTail word = word := by
  induction word with
  | nil => rfl
  | cons c rest ih => cases c with
    | none => rfl
    | some b => simpa only [wordPrefix,stopTail,List.map_cons,List.cons_append] using congrArg (List.cons (some b)) ih

private theorem cells_append (xs ys : List Cell) :
    BitTapeCoverage.cells (xs++ys) = BitTapeCoverage.cells xs ++ BitTapeCoverage.cells ys := by
  induction xs with
  | nil => rfl
  | cons c rest ih => simp only [List.cons_append,BitTapeCoverage.cells,ih]

private theorem scan_some (b : Bool) (word : List Cell) (out rev : List Bool) (v : Fin 3) :
    tick (state (some 0) (BitTapeCoverage.cells (some b::word)) out rev v) =
      state (some 0) (BitTapeCoverage.cells word) out (b::rev) (BitTapeCoverage.cellCode (some b)) := by
  cases b <;>
    apply congrArg (fun words : Fin 3 → List Bool =>
      (⟨some 0,_,words⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem scan_stop (tail : List Cell) (out rev : List Bool) (v : Fin 3) :
    tick (state (some 0) (BitTapeCoverage.cells (none::tail)) out rev v) =
      state (some 1) (BitTapeCoverage.cells (none::tail)) out rev 1 := rfl

private theorem scan_empty (out rev : List Bool) (v : Fin 3) :
    tick (state (some 0) [] out rev v) = state (some 1) [] out rev := rfl

private theorem restore_some (source out rev : List Bool) (b : Bool) (v : Fin 3) :
    tick (state (some 1) source out (b::rev) v) =
      state (some 1) (true::b::source) (b::out) rev (BitTapeCoverage.cellCode (some b)) := by
  cases b <;>
    apply congrArg (fun words : Fin 3 → List Bool =>
      (⟨some 1,_,words⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem restore_empty (source out : List Bool) (v : Fin 3) :
    tick (state (some 1) source out [] v) = state none source out [] := by
  apply congrArg (fun words : Fin 3 → List Bool => (⟨none,0,words⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem scan_run (word : List Cell) (out rev : List Bool) (v : Fin 3) :
    tick^[ (wordPrefix word).length+1 ]
      (state (some 0) (BitTapeCoverage.cells word) out rev v) =
    state (some 1) (BitTapeCoverage.cells (stopTail word)) out
      ((wordPrefix word).reverse++rev)
      (BitTapeCoverage.cellCode (BitTapeCoverage.cells (stopTail word)).head?) := by
  induction word generalizing rev v with
  | nil => exact scan_empty out rev v
  | cons c rest ih => cases c with
    | none => exact scan_stop rest out rev v
    | some b =>
      simp only [wordPrefix,List.length_cons]
      rw [Nat.add_assoc,Function.iterate_succ_apply,scan_some,ih]
      simp only [stopTail,List.reverse_cons,List.append_assoc,List.singleton_append]

private theorem restore_run (source out rev : List Bool) (v : Fin 3) :
    tick^[rev.length+1] (state (some 1) source out rev v) =
      state none (BitTapeCoverage.cells (rev.reverse.map some)++source) (rev.reverse++out) [] := by
  induction rev generalizing source out v with
  | nil => exact restore_empty source out v
  | cons b rest ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,restore_some,ih]
    simp only [List.reverse_cons,List.map_append,cells_append,List.append_assoc,
      List.map_cons,List.map_nil,BitTapeCoverage.cells,List.nil_append,List.cons_append]
    rfl

private theorem prefix_length (word : List Cell) : (wordPrefix word).length ≤ word.length := by
  induction word with
  | nil => rfl
  | cons c rest ih => cases c with
    | none => exact Nat.zero_le _
    | some b => simpa only [wordPrefix,List.length_cons] using Nat.succ_le_succ ih

/-- The scanner stops before consuming the first blank cell; restoration then
reconstructs exactly the consumed canonical nonblank prefix. -/
theorem exact_run (word : List Cell) (suffix : List Bool) (v : Fin 3) :
    tick^[2*(wordPrefix word).length+2] (start word suffix v) = result word suffix := by
  rw [show 2*(wordPrefix word).length+2 =
      ((wordPrefix word).length+1)+((wordPrefix word).length+1) by omega,
    Function.iterate_add_apply]
  unfold start
  rw [scan_run]
  simp only [List.append_nil]
  have hr := restore_run (BitTapeCoverage.cells (stopTail word)) suffix (wordPrefix word).reverse
    (BitTapeCoverage.cellCode (BitTapeCoverage.cells (stopTail word)).head?)
  simp only [List.length_reverse,List.reverse_reverse] at hr
  rw [←cells_append,word_decomposition] at hr
  exact hr

/-- Uniform clock from the actual finite cell representation, padded only after
the exact restored halt. All suffix cells and output suffix bytes are retained. -/
theorem run (word : List Cell) (suffix : List Bool) (v : Fin 3) :
    tick^[clock word] (start word suffix v) = result word suffix := by
  have hlen := prefix_length word
  have hc : 2*(wordPrefix word).length+2 ≤ clock word := by unfold clock; omega
  rw [show clock word = (clock word-(2*(wordPrefix word).length+2))+
    (2*(wordPrefix word).length+2) by omega,Function.iterate_add_apply,exact_run]
  exact Function.iterate_fixed (show tick (result word suffix) = result word suffix from rfl) _

/-- Cost follows from the actual fixed program and its six-operation statement
bound. It is not supplied as a source or caller certificate. -/
theorem charged (word : List Cell) (suffix : List Bool) (v : Fin 3) :
    ∃ charge ≤ cost word,
      BitOracleMachine.run code (clock word) (start word suffix v) =
        pure (result word suffix,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 6
    (fun label => (local_cost label).le) (clock word) (start word suffix v)
  rw [run] at he
  exact ⟨charge,hc,he⟩

end ExplainableCrypto.Helios.Computational.NativeQueryExport
