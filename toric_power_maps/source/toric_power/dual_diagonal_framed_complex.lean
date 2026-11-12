module

public import ToricPower.FiniteFreeModuleDual
public import ToricPower.DiagonalFramedModuleResolution
public import ToricPower.DualDiagonalCellFrames

/-!
# The actual ring-linear dual of the affine diagonal complex

The dual is taken over the actual product-chart coordinate ring. The
finite dual frame and its complete scalar Laurent coordinates are
constructed explicitly. In particular, the scalar weight decomposition
below is attached to a genuine module complex over the chart ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (frames : ∀ q, DiagonalCellFrames A S T q)

local notation "R" => DiagonalChartRing k A S T

local instance dualScalarModule (M : ModuleCat.{0} R) : Module k M :=
  Module.restrictScalars k R M

local instance dualScalarTower (M : ModuleCat.{0} R) : IsScalarTower k R M :=
  IsScalarTower.restrictScalars k R M

/-- The literal `R`-linear dual of the already constructed finite free
diagonal complex, with its actual transposed differential. -/
def diagonalFramedDualComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  moduleDualComplex R (diagonalFramedComplex k A S T frames)

/-- Dual frame coordinates over the actual chart ring. -/
def diagonalFramedDualCoordinates (q : ℕ) :
    (diagonalFramedDualComplex k A S T frames).X q ≃ₗ[R]
      (NormalizedCell A q →₀ R) :=
  finiteFreeModuleDualEquiv R (NormalizedCell A q)

/-- Every entry of the differential is the literal transpose of the
actual global monomial column in the ordinary Cartier frames. -/
theorem diagonalFramedDualCoordinates_differential (q : ℕ)
    (v : (diagonalFramedDualComplex k A S T frames).X q)
    (j : NormalizedCell A (q+1)) :
    diagonalFramedDualCoordinates k A S T frames (q+1)
        ((diagonalFramedDualComplex k A S T frames).d q (q+1) v) j =
      (diagonalFramedGlobalColumn k A (frames q) (frames (q+1)) j).sum
        (fun i r => r * diagonalFramedDualCoordinates k A S T frames q v i) := by
  change (ModuleCat.of R (NormalizedCell A q →₀ R) ⟶ ModuleCat.of R R) at v
  change v ((diagonalFramedComplex k A S T frames).d (q+1) q
    (Finsupp.single j 1)) = _
  rw [diagonalFramedComplex_d]
  change v (diagonalFramedBoundary k A (frames q) (frames (q+1))
    (Finsupp.single j 1)) = _
  rw [diagonalFramedBoundary, Finsupp.linearCombination_single, one_smul]
  exact finiteFreeModuleDualEquiv_evaluate R (NormalizedCell A q) v _

/-- A free generator is sent by the genuine transposed matrix to the
specified polynomial entry, over `R` itself. -/
theorem diagonalFramedDualCoordinates_d_generator (q : ℕ)
    (i : NormalizedCell A q) (j : NormalizedCell A (q+1)) (r : R) :
    diagonalFramedDualCoordinates k A S T frames (q+1)
        ((diagonalFramedDualComplex k A S T frames).d q (q+1)
          ((diagonalFramedDualCoordinates k A S T frames q).symm
            (Finsupp.single i r))) j =
      diagonalFramedGlobalColumn k A (frames q) (frames (q+1)) j i * r := by
  rw [diagonalFramedDualCoordinates_differential, LinearEquiv.apply_symm_apply]
  change Finsupp.linearCombination R (Pi.single i r)
    (diagonalFramedGlobalColumn k A (frames q) (frames (q+1)) j) = _
  apply Finsupp.linearCombination_single_index

/-- The underlying scalar complex of the actual ring-linear dual. -/
def diagonalFramedDualScalarComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (diagonalFramedDualComplex k A S T frames)

/-- Complete, unrestricted Laurent coordinates of the actual dual
complex. Each coordinate retains its total character and normalized cell. -/
def diagonalFramedDualScalarCoordinates (q : ℕ) :
    (diagonalFramedDualScalarComplex k A S T frames).X q ≃ₗ[k]
      (DualDiagonalAllWeightIndex A S T q →₀ k) :=
  ((diagonalFramedDualCoordinates k A S T frames q).restrictScalars k).trans
    ((frames q).dualCoefficientEquiv k)

end ToricPower.IntegralArrangement
