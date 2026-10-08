import ExplainableCrypto.OneTimePad.MutationTesting
import ProofWidgets.Component.HtmlDisplay

/-!
# Visual witnesses for the one-time-pad attacks

Place the cursor on either `#html` command at the end of this file. Lean's
InfoView will display the attack as an exact probability table.

The pictures do not maintain a second, informal copy of the probabilities.
They call the computable key-counting functions below, while
`uniform_probability_eq_count` proves that those counts denote the PMF
probabilities used by the security definition.
-/

open scoped ProofWidgets.Jsx
open ProofWidgets

namespace ExplainableCrypto.OneTimePad.Visuals

/-! ## Computable tables and checked cells -/

def cleartextEncrypt {n : Nat} : Block n → Block n → Block n := fun _ m => m

def reuseMatchingKeyCount {n : Nat}
    (messages ciphertexts : Block n × Block n) : Nat :=
  (Finset.univ.filter fun k =>
    (k ^^^ messages.1, k ^^^ messages.2) = ciphertexts).card

theorem cleartext_observed_left :
    matchingKeyCount (@cleartextEncrypt 1) 0 0 = 2 := by decide

theorem cleartext_observed_right :
    matchingKeyCount (@cleartextEncrypt 1) 1 0 = 0 := by decide

theorem reuse_observed_left :
    reuseMatchingKeyCount ((0, 0) : Block 2 × Block 2) (0, 0) = 1 := by decide

theorem reuse_observed_right :
    reuseMatchingKeyCount ((0, 3) : Block 2 × Block 2) (0, 0) = 0 := by decide

/-! ## Presentation helpers -/

def blockLabel (n : Nat) (x : Block n) : String :=
  String.ofList <| (List.range n).reverse.map fun i =>
    if x.getLsbD i then '1' else '0'

def probabilityLabel (count total : Nat) : String :=
  if count = 0 then "0"
  else if count = total then "1"
  else s!"{count}/{total}"

def borderStyle : String := "1px solid var(--vscode-editorWidget-border)"

def baseCellStyle : Lean.Json := json% {
  padding: "0.4rem 0.55rem",
  textAlign: "center",
  border: $(borderStyle),
  minWidth: "2.4rem",
  fontVariantNumeric: "tabular-nums"
}

def headerStyle : Lean.Json := json% {
  padding: "0.4rem 0.55rem",
  textAlign: "center",
  border: $(borderStyle),
  fontWeight: "600",
  background: "var(--vscode-editor-inactiveSelectionBackground)"
}

def observedPositiveStyle : Lean.Json := json% {
  padding: "0.4rem 0.55rem",
  textAlign: "center",
  border: "2px solid var(--vscode-charts-green)",
  background: "color-mix(in srgb, var(--vscode-charts-green) 18%, transparent)",
  fontWeight: "700"
}

def observedZeroStyle : Lean.Json := json% {
  padding: "0.4rem 0.55rem",
  textAlign: "center",
  border: "2px solid var(--vscode-charts-red)",
  background: "color-mix(in srgb, var(--vscode-charts-red) 15%, transparent)",
  fontWeight: "700"
}

def countCell (count total : Nat) (observed : Bool := false) : Html :=
  let style := if observed then
      if count = 0 then observedZeroStyle else observedPositiveStyle
    else baseCellStyle;
  <td style={style}>{.text (probabilityLabel count total)}</td>

def tableStyle : Lean.Json := json% {
  borderCollapse: "collapse",
  margin: "0.35rem 0 0.65rem 0"
}

def panelStyle : Lean.Json := json% {
  border: $(borderStyle),
  padding: "0.75rem",
  margin: "0.5rem 0",
  background: "var(--vscode-editor-background)",
  color: "var(--vscode-editor-foreground)"
}

def pairStyle : Lean.Json := json% {
  display: "flex",
  flexWrap: "wrap",
  gap: "1rem",
  alignItems: "flex-start"
}

/-! ## Cleartext-encryption attack -/

def cleartextRow (m : Block 1) : Html :=
  let count0 := matchingKeyCount (@cleartextEncrypt 1) m 0
  let count1 := matchingKeyCount (@cleartextEncrypt 1) m 1;
  <tr>
    <th style={headerStyle}>{.text (s!"m = {blockLabel 1 m}")}</th>
    {countCell count0 2 true}
    {countCell count1 2 false}
  </tr>

def cleartextAttackView : Html :=
  <div style={panelStyle}>
    <h3 style={json% {margin: "0 0 0.25rem 0"}}>Cleartext encryption reveals the message</h3>
    <div>Observed ciphertext: <b>0</b>. The highlighted probabilities differ.</div>
    <table style={tableStyle}>
      <thead><tr>
        <th style={headerStyle}>message</th>
        <th style={headerStyle}>c = 0</th>
        <th style={headerStyle}>c = 1</th>
      </tr></thead>
      <tbody>
        {cleartextRow 0}
        {cleartextRow 1}
      </tbody>
    </table>
    <div><b>Checked witness:</b> Pr[c = 0 | m = 0] = 1, but Pr[c = 0 | m = 1] = 0.</div>
  </div>

/-! ## Reused-pad attack -/

def blocks2 : Array (Block 2) := #[0, 1, 2, 3]

def reuseGridRow (messages : Block 2 × Block 2) (c₀ : Block 2) : Html :=
  let cells := blocks2.map fun c₁ =>
    let count := reuseMatchingKeyCount messages (c₀, c₁)
    countCell count 4 (c₀ == 0 && c₁ == 0);
  <tr>
    <th style={headerStyle}>{.text (blockLabel 2 c₀)}</th>
    {...cells}
  </tr>

def reuseGrid (title : String) (messages : Block 2 × Block 2) : Html :=
  let headers := blocks2.map fun c =>
    <th style={headerStyle}>{.text (blockLabel 2 c)}</th>
  let rows := blocks2.map fun c => reuseGridRow messages c;
  <div>
    <b>{.text title}</b>
    <table style={tableStyle}>
      <thead><tr>
        <th style={headerStyle}>c₀ / c₁</th>
        {...headers}
      </tr></thead>
      <tbody>{...rows}</tbody>
    </table>
  </div>

def reuseAttackView : Html :=
  <div style={panelStyle}>
    <h3 style={json% {margin: "0 0 0.25rem 0"}}>Reusing a two-bit pad leaks a relation</h3>
    <div>Each cell is the exact probability of a ciphertext pair. The highlighted pair is (00, 00).</div>
    <div style={pairStyle}>
      {reuseGrid "messages (00, 00)" (0, 0)}
      {reuseGrid "messages (00, 11)" (0, 3)}
    </div>
    <div><b>Checked witness:</b> Pr[(00, 00) | (00, 00)] = 1/4, but
      Pr[(00, 00) | (00, 11)] = 0.</div>
  </div>

/-!
Put the cursor on a command to display that checked witness in the InfoView.
-/

#html cleartextAttackView
#html reuseAttackView

end ExplainableCrypto.OneTimePad.Visuals
