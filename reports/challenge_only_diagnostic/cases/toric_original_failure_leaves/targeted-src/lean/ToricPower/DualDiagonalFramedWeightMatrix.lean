module

public import ToricPower.DualDiagonalFramedCoefficients

/-!
# The full weight matrix of the genuine dual diagonal module complex

The computed polynomial transpose is transported through its actual
Cartier frames. The resulting matrix is zero between different total
characters and equals the original translated cellular incidence within
each character. No cohomology-level comparison is used in this step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  {S T : Set (Fin s)} {d : ℕ}

namespace DiagonalCellFrames

variable (F : DiagonalCellFrames A S T d)

/-- Actual coefficient extraction after expanding the dual frame. -/
theorem dualCoefficientEquiv_apply (v : NormalizedCell A d →₀ DiagonalChartRing k A S T)
    (j : NormalizedCell A d) (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    F.dualCoefficientEquiv k v (F.dualCell j p) = (v j).coeff p := by
  change Finsupp.equivMapDomain F.dualCellEquiv
      (Finsupp.uncurry (Finsupp.mapRange
        (fun x => (AddMonoidAlgebra.coeffLinearEquiv k) x) (by rfl) v))
      (F.dualCellEquiv (j, p)) = _
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  rfl

/-- The inverse basis identification uses the literal polynomial
monomial in the specified dual Cartier frame. -/
theorem dualCoefficientEquiv_symm_single (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    (F.dualCoefficientEquiv k).symm (Finsupp.single (F.dualCell j p) r) =
      Finsupp.single j (AddMonoidAlgebra.single p r) := by
  apply (F.dualCoefficientEquiv k).injective
  rw [LinearEquiv.apply_symm_apply, F.dualCoefficientEquiv_single]

end DiagonalCellFrames

variable (S T : Set (Fin s)) (frames : ∀ q, DiagonalCellFrames A S T q)

local notation "R" => DiagonalChartRing k A S T

/-- Scalar coordinates of the genuine dual recover the actual
polynomial coefficient in the dual free module. -/
theorem diagonalFramedDualScalarCoordinates_apply (q : ℕ)
    (v : (diagonalFramedDualScalarComplex k A S T frames).X q)
    (j : NormalizedCell A q) (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    diagonalFramedDualScalarCoordinates k A S T frames q v ((frames q).dualCell j p) =
      (diagonalFramedDualCoordinates k A S T frames q v j).coeff p :=
  (frames q).dualCoefficientEquiv_apply k A _ j p

/-- The full scalar basis generator is the actual ring-linear dual
basis vector with the specified polynomial coefficient. -/
theorem diagonalFramedDualScalarCoordinates_symm_single (q : ℕ)
    (j : NormalizedCell A q) (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    (diagonalFramedDualScalarCoordinates k A S T frames q).symm
      (Finsupp.single ((frames q).dualCell j p) r) =
    (diagonalFramedDualCoordinates k A S T frames q).symm
      (Finsupp.single j (AddMonoidAlgebra.single p r)) := by
  apply (diagonalFramedDualScalarCoordinates k A S T frames q).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = (frames q).dualCoefficientEquiv k
    (diagonalFramedDualCoordinates k A S T frames q
      ((diagonalFramedDualCoordinates k A S T frames q).symm
        (Finsupp.single j (AddMonoidAlgebra.single p r))))
  rw [LinearEquiv.apply_symm_apply, (frames q).dualCoefficientEquiv_single]

/-- Every actual Laurent matrix entry, first in its ordinary polynomial
frame coordinates. -/
theorem diagonalFramedDualScalarCoordinates_d_frame (q : ℕ)
    (i : NormalizedCell A q) (j : NormalizedCell A (q+1))
    (p t : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    diagonalFramedDualScalarCoordinates k A S T frames (q+1)
      ((diagonalFramedDualScalarComplex k A S T frames).d q (q+1)
        ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
          (Finsupp.single ((frames q).dualCell i p) r)))
      ((frames (q+1)).dualCell j t) =
    if (frames q).dualWeight i p = (frames (q+1)).dualWeight j t then
      diagonalGlobalColumn k A q j
        (i, dualFramedDisplacement A (frames q) (frames (q+1)) i j p t) * r else 0 := by
  rw [diagonalFramedDualScalarCoordinates_symm_single,
    diagonalFramedDualScalarCoordinates_apply]
  change (diagonalFramedDualCoordinates k A S T frames (q+1)
    ((diagonalFramedDualComplex k A S T frames).d q (q+1)
      ((diagonalFramedDualCoordinates k A S T frames q).symm
        (Finsupp.single i (AddMonoidAlgebra.single p r)))) j).coeff t = _
  rw [diagonalFramedDualCoordinates_d_generator]
  exact diagonalFramedGlobalColumn_mul_coeff k A (frames q) (frames (q+1)) i j p t r

/-- The exact complete matrix in all Laurent weights. This identifies
the actual ring-linear dual with the original fixed-weight cellular
complexes, including the zero entries between distinct weights. -/
theorem diagonalFramedDualScalarCoordinates_d_generator (q : ℕ)
    (x : DualDiagonalAllWeightIndex A S T q)
    (y : DualDiagonalAllWeightIndex A S T (q+1)) (r : k) :
    diagonalFramedDualScalarCoordinates k A S T frames (q+1)
      ((diagonalFramedDualScalarComplex k A S T frames).d q (q+1)
        ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
          (Finsupp.single x r))) y =
      if x.1 = y.1 then
        diagonalGlobalColumn k A q y.2.1 (x.2.1, y.2.2.val - x.2.2.val) * r
      else 0 := by
  obtain ⟨⟨i, p⟩, rfl⟩ := (frames q).dualCellEquiv.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (frames (q+1)).dualCellEquiv.surjective y
  exact diagonalFramedDualScalarCoordinates_d_frame k A S T frames q i j p t r

end ToricPower.IntegralArrangement
