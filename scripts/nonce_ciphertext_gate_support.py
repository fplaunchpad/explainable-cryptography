"""Test-only identity adapters for the native nonce/ciphertext gates.

The generated Lean driver proves both adapters equal to the original objects.
Kernel campaigns do not use either adapter. No production definition is replaced.
"""
NATIVE_SNAPSHOT = r'''
namespace ExplainableCrypto.Helios.Computational
def routingSnapshot {s l m : Nat} (cfg : BitOracleMachine.Config s l m) :
    BitOracleMachine.Config s l m :=
  let words := Array.ofFn cfg.stk
  ⟨cfg.l,cfg.var,fun k => words[k.val]'(by simp [words])⟩
theorem routingSnapshot_eq {s l m : Nat} (cfg : BitOracleMachine.Config s l m) :
    routingSnapshot cfg = cfg := by
  cases cfg
  simp [routingSnapshot]
#print axioms routingSnapshot_eq
def routingProgramTable {l : Nat} {α : Type} (program : Fin l → α) :=
  let table := Array.ofFn program
  fun k : Fin l => table[k.val]'(by simp [table])
theorem routingProgramTable_eq {l : Nat} {α : Type} (program : Fin l → α) :
    routingProgramTable program = program := by
  funext k
  simp [routingProgramTable]
#print axioms routingProgramTable_eq
end ExplainableCrypto.Helios.Computational
'''
