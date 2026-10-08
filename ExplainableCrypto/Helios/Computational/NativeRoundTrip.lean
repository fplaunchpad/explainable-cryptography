import ExplainableCrypto.Helios.Computational.NativeRoundTripMemory
import ExplainableCrypto.Helios.Computational.NativeAnswerImport
import ExplainableCrypto.Helios.Computational.NativeQueryExportAdapter
import ExplainableCrypto.Helios.Computational.NativeOracleTape

/-! Finite native oracle-call controller. Native entry labels inspect the original
three heads before selecting a fixed call block. The block preserves those
heads while local code exports the query and imports the replacement answer,
then actually jumps to the selected native entry with restored head memory. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)
open NativeRoundTripMemory (pack unpack)
set_option maxRecDepth 32768
set_option maxHeartbeats 700000
abbrev Labels (l : Nat) := l+(l*2)*13
abbrev Config (l : Nat) := BitOracleMachine.Config 8 (Labels l) 81
abbrev Statement (l : Nat) := TM2.Stmt (fun _ : Fin 8 => Bool) (Fin (Labels l)) (Fin 81)

def headsCode (h : Fin 3 → Cell) : Fin 27 :=
  finProdFinEquiv (cellCode (h 0),finProdFinEquiv (cellCode (h 1),cellCode (h 2)))
def heads (v : Fin 27) : Fin 3 → Cell :=
  let x : Fin 3 × Fin 9 := finProdFinEquiv.symm v
  let y : Fin 3 × Fin 3 := finProdFinEquiv.symm x.2
  ![readCell x.1,readCell y.1,readCell y.2]
def memory (h : Fin 3 → Cell) : Fin 81 := pack (headsCode h) (0 : Fin 3)
def currentHeads (v : Fin 81) : Fin 3 → Cell := heads ((unpack v : Fin 27 × Fin 3).1)
def localMemory (v : Fin 81) : Fin 3 := (unpack v : Fin 27 × Fin 3).2

def entryLabel {l : Nat} (q : Fin l) : Fin (Labels l) := finSumFinEquiv (.inl q)
def blockLabel {l : Nat} (next : Fin l) (kind : Fin 2) (phase : Fin 13) : Fin (Labels l) :=
  finSumFinEquiv (.inr (finProdFinEquiv (finProdFinEquiv (next,kind),phase)))
def kindIndex : OracleTapeDispatch.Kind → Fin 2 | .hash => 0 | .coin => 1

def exportLayout : Fin 3 ⊕ Fin 5 ≃ Fin 8 where
  toFun | .inl i => ![3,6,7] i | .inr i => ![0,1,2,4,5] i
  invFun i := ![.inr 0,.inr 1,.inr 2,.inl 0,.inr 3,.inr 4,.inl 1,.inl 2] i
  left_inv x := by cases x with | inl i => fin_cases i <;> rfl | inr i => fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def importLayout : Fin 3 ⊕ Fin 5 ≃ Fin 8 where
  toFun | .inl i => ![4,5,6] i | .inr i => ![0,1,2,3,7] i
  invFun i := ![.inr 0,.inr 1,.inr 2,.inr 3,.inl 0,.inl 1,.inl 2,.inr 4] i
  left_inv x := by cases x with | inl i => fin_cases i <;> rfl | inr i => fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def exportProgram (q : Fin 4) := NativeRoundTripMemory.stmt (saved := 27)
  (TM2StackFrame.relocate exportLayout (NativeQueryExportAdapter.program q))
def importProgram (q : Fin 5) := NativeRoundTripMemory.stmt (saved := 27)
  (TM2StackFrame.relocate importLayout (NativeAnswerImport.program q))
def exportLabel {l : Nat} (next : Fin l) (kind : Fin 2) (q : Fin 4) :=
  blockLabel next kind (⟨q.val+1,by omega⟩ : Fin 13)
def importLabel {l : Nat} (next : Fin l) (kind : Fin 2) (q : Fin 5) :=
  blockLabel next kind (⟨q.val+7,by omega⟩ : Fin 13)

def block {l : Nat} (next : Fin l) (kind : Fin 2) : Fin 13 → BitOracleMachine.Command 8 (Labels l) 81 :=
  ![.compute (.load (fun v => pack ((unpack v : Fin 27 × Fin 3).1) (cellCode (currentHeads v 1)))
        (.goto (fun _ => blockLabel next kind 1))),
    .compute (TM2ReturnLink.redirect (exportLabel next kind) (blockLabel next kind 5) (exportProgram 0)),
    .compute (TM2ReturnLink.redirect (exportLabel next kind) (blockLabel next kind 5) (exportProgram 1)),
    .compute (TM2ReturnLink.redirect (exportLabel next kind) (blockLabel next kind 5) (exportProgram 2)),
    .compute (TM2ReturnLink.redirect (exportLabel next kind) (blockLabel next kind 5) (exportProgram 3)),
    if kind = 0 then .hash 6 5 (blockLabel next kind 6) else .coin 5 (blockLabel next kind 6),
    .compute (.load (fun v => pack ((unpack v : Fin 27 × Fin 3).1) (0 : Fin 3))
        (.goto (fun _ => blockLabel next kind 7))),
    .compute (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram 0)),
    .compute (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram 1)),
    .compute (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram 2)),
    .compute (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram 3)),
    .compute (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram 4)),
    .compute (.load (fun v => memory ![currentHeads v 0,currentHeads v 1,readCell (localMemory v)])
        (.goto (fun _ => entryLabel next)))]

def entry {l : Nat} (native : NativeOracleTape.Code l) (q : Fin l) : Statement l :=
  .branch (fun v => match native q (currentHeads v) with | .oracle _ _ => true | _ => false)
    (.goto (fun v => match native q (currentHeads v) with
      | .oracle kind next => blockLabel next (kindIndex kind) 0
      | _ => entryLabel q)) .halt

def code {l : Nat} (native : NativeOracleTape.Code l) : BitOracleMachine.Code 8 (Labels l) 81 := fun q =>
  match finSumFinEquiv.symm q with
  | .inl q => .compute (entry native q)
  | .inr i =>
    let x : Fin (l*2) × Fin 13 := finProdFinEquiv.symm i
    let y : Fin l × Fin 2 := finProdFinEquiv.symm x.1
    block y.1 y.2 x.2

def words (before after : Fin 3 → List Cell) : Fin 8 → List Bool :=
  ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),
    cells (before 2),cells (after 2),[],[]]
def initial {l : Nat} (q : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) : Config l :=
  ⟨some (entryLabel q),memory h,words before after⟩
def result {l : Nat} (next : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply : List Bool) : Config l :=
  ⟨some (entryLabel next),memory ![h 0,h 1,reply.head?],
    ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),[],
      cells (reply.tail.map some),[],[]]⟩
def nativeState {l : Nat} (q : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) : NativeOracleTape.Config l :=
  ⟨some q,BitTapeCoverage.tape (l := 0) ⟨none,h 0,before 0,after 0⟩,
    BitTapeCoverage.tape (l := 0) ⟨none,h 1,before 1,after 1⟩,
    BitTapeCoverage.tape (l := 0) ⟨none,h 2,before 2,after 2⟩⟩

def atNative {l : Nat} (q : Fin (Labels l)) : Bool :=
  match finSumFinEquiv.symm q with | .inl _ => true | .inr _ => false

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
