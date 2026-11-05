module

public import PaperVerification.AlternatingSectionImageIdeal
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The genuine equation ideal in row coordinates

An alternating form restricted along a matrix of row vectors gives a
functional on the exterior square of the coefficient module.  Its image
ideal is exactly the ideal of all row-pairing equations, over any
commutative ring.  Independence of the rows is not required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingSectionRowIdeal

variable {R I N : Type*} [CommRing R] [Fintype I]

/-- Restriction to the coefficient module of the prescribed row matrix. -/
def rowForm (f : AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R) :
    AlternatingMap R (I → R) R (Fin 2) :=
  f.compLinearMap A.vecMulLinear

/-- A pair of coordinate basis vectors maps to exactly the selected rows. -/
theorem rowForm_basis_pair (f : AlternatingMap R (N → R) R (Fin 2))
    (A : Matrix I N R) (i j : I) :
    rowForm f A ![Pi.basisFun R I i, Pi.basisFun R I j] = f ![A i, A j] := by
  classical
  change f (fun k ↦ A.vecMulLinear (![Pi.basisFun R I i, Pi.basisFun R I j] k)) = _
  congr 1
  funext k
  fin_cases k
  · change Matrix.vecMul (Pi.basisFun R I i) A = A i
    simp only [Pi.basisFun_apply, Matrix.single_vecMul, one_smul]
    rfl
  · change Matrix.vecMul (Pi.basisFun R I j) A = A j
    simp only [Pi.basisFun_apply, Matrix.single_vecMul, one_smul]
    rfl

/-- The original row-pairing ideal is the image of the universal exterior
functional.  The equality is at the level of ideals, not only zero sets. -/
theorem range_rowExteriorFunctional_eq_ideal
    (f : AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R) :
    LinearMap.range (exteriorPower.alternatingMapLinearEquiv (rowForm f A)) =
      Ideal.span (Set.range fun ij : I × I ↦ f ![A ij.1, A ij.2]) := by
  simpa only [rowForm_basis_pair] using
    AlternatingSectionImageIdeal.range_exteriorFunctional_eq_basis_ideal
      (Pi.basisFun R I) (rowForm f A)

end PaperVerification.AlternatingSectionRowIdeal
