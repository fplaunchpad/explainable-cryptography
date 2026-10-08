import CatCryptCore.Examples.ElGamalDDH
import CatCryptCore.Examples.ChaumPedersen

/-! Interface validation against the pinned CatCrypt release. These adapters
connect existing algebraic APIs; they do not assert Helios security. -/

namespace HeliosLibraryProbe

open CatCrypt.Examples
open CatCryptCore.Examples.CyclicGroupDDH

@[reducible] def groupParamCyclic (gp : GroupParam) : CyclicGroup gp.G where
  Exp := gp.Scalar
  finG := gp.finG
  neG := gp.neG
  finExp := gp.finScalar
  neExp := gp.neScalar
  gen := gp.generator
  pow := gp.exp
  mul := gp.groupMul
  inv := gp.groupInv
  expMul := gp.scalarMul
  expNeg := gp.scalarNeg
  one := gp.identity
  pow_comm := fun a b => congrArg gp.exp (gp.scalarMul_comm a b)
  mul_assoc := gp.groupMul_assoc
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := gp.exp_surj x
    obtain ⟨b, rfl⟩ := gp.exp_surj y
    rw [← gp.exp_add, ← gp.exp_add, gp.scalarAdd_comm]
  mul_inv := gp.groupMul_inv
  mul_one := gp.groupMul_identity
  pow_bij := ⟨fun _ _ h => gp.exp_inj _ _ h, gp.exp_surj⟩

/-- The ElGamal interface's choice-based exponentiation agrees with the
explicit operation supplied to Chaum–Pedersen. No discrete-log algorithm is
needed to implement this operation once this equality is used. -/
theorem elemPow_eq_groupExp (gp : GroupParam) (x : gp.G) (r : gp.Scalar) :
    @CyclicGroup.elemPow gp.G (groupParamCyclic gp) x r = gp.groupExp x r := by
  obtain ⟨a, rfl⟩ := gp.exp_surj x
  exact (CyclicGroup.elemPow_pow (CG := groupParamCyclic gp) a r).trans
    (gp.groupExp_exp a r).symm

#print axioms groupParamCyclic
#print axioms elemPow_eq_groupExp
#print axioms CatCryptCore.Examples.ElGamalDDH.elgamal_correct
#print axioms CatCryptCore.Examples.ElGamalDDH.elgamal_indcpa_security
#print axioms CatCryptCore.Examples.ChaumPedersen.chaumPedersen_complete
#print axioms CatCryptCore.Examples.ChaumPedersen.chaumPedersen_special_soundness
#print axioms CatCryptCore.Examples.ChaumPedersen.cp_real_vis_eq_sim

end HeliosLibraryProbe
