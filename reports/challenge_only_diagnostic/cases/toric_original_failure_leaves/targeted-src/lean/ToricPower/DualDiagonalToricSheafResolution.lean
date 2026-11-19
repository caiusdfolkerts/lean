module

public import ToricPower.AffineFiniteFreeDualComplex
public import ToricPower.DualDiagonalToricResolution
public import ToricPower.DiagonalFramedResolution
public import ToricPower.SingleComplexQuasiIso

/-!
# Exactness of the actual affine internal-dual sheaf complex

The actual sheaf internal dual of the original free diagonal complex is
identified, including its complete differential, with the tilde of the
actual ring-linear dual. The proved module augmentation therefore gives
a genuine sheaf quasi-isomorphism to the boundary-weight sheaf in ambient
degree. The target carries its independently defined product-ring action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "U" => Spec (CommRingCat.of R)
local notation "F" => toricDiagonalCellFrames fan regular basis rays σ τ
local notation "K" => toricDiagonalFramedSheafComplex fan regular basis rays σ τ

local instance dualToricSheafCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

/-- The full canonical transpose comparison for the actual free sheaf
complex, proved from naturality for every original module matrix. -/
def toricDiagonalFramedDualInternalIso :
    (affineTildeCochainFunctor (CommRingCat.of R)).obj (toricDiagonalFramedDualComplex fan regular basis rays σ τ) ≅
      internalDualComplex (U).Modules K :=
  affineFiniteFreeDualComplexIso (CommRingCat.of R) (NormalizedCell A)
    (fun q => ModuleCat.ofHom (diagonalFramedBoundary ℂ A (F q) (F (q+1))))
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact DFunLike.congr_fun (diagonalFramedBoundary_square ℂ A S T F q) v)

/-- The actual top quotient of the internal-dual affine sheaf complex,
with its independently constructed boundary-weight target. -/
def toricDiagonalInternalDualBoundaryAugmentation :
    internalDualComplex (U).Modules K ⟶
      (HomologicalComplex.single (U).Modules (.up ℕ) n).obj
        (tilde (dualDiagonalBoundaryModule A S T ℂ)) :=
  (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).inv ≫
    (affineTildeCochainFunctor (CommRingCat.of R)).map (diagonalFramedDualAugmentation ℂ A S T F) ≫
      (affineTildeSingleIso (CommRingCat.of R)
        (dualDiagonalBoundaryModule A S T ℂ) n).hom

/-- Genuine affine sheaf exactness follows from exact tilde and the
independent complete ring-linear dual calculation. -/
theorem toricDiagonalInternalDualBoundaryAugmentation_quasiIso :
    QuasiIso (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) := by
  letI := diagonalFramedDualAugmentation_quasiIso ℂ A S T F
  unfold toricDiagonalInternalDualBoundaryAugmentation
  infer_instance

/-- Actual affine internal-dual homology vanishes in every degree
other than the full ambient lattice rank. -/
theorem toricDiagonalInternalDual_isZero_homology (q : ℕ) (different : q ≠ n) :
    IsZero ((internalDualComplex (U).Modules K).homology q) := by
  letI := toricDiagonalInternalDualBoundaryAugmentation_quasiIso fan regular basis rays σ τ
  exact isZeroHomologyOfQuasiIsoToSingle
    (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) q different

/-- The actual top sheaf homology is the independently specified
boundary-weight module after affine sheafification. -/
def toricDiagonalInternalDualTopIso :
    (internalDualComplex (U).Modules K).homology n ≅
      tilde (dualDiagonalBoundaryModule A S T ℂ) := by
  letI := toricDiagonalInternalDualBoundaryAugmentation_quasiIso fan regular basis rays σ τ
  exact homologyIsoOfQuasiIsoToSingle
    (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ)

end ToricPower
