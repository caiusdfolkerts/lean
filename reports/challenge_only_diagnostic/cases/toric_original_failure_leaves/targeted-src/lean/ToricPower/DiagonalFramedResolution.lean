module

public import ToricPower.DiagonalFramedModuleResolution
public import ToricPower.SheafDuality
public import ToricPower.AffineSplitting
public import ToricPower.AffineTildeComplex

/-!
# The sheafified affine diagonal resolution

Exact affine sheafification sends the independently checked finite free
module resolution to the actual affine diagonal direct image. Its target
and its augmentation are specified by actual sheaf and complex maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "B" => affineCoordinateRing fan.lattice (σ.val ⊓ τ.val)

/-- Sheafification of the actual finite local matrix. -/
def toricDiagonalFramedSheafComplex : ChainComplex (Spec (CommRingCat.of R)).Modules ℕ :=
  (affineTildeChainFunctor (CommRingCat.of R)).obj
    (toricDiagonalFramedComplex fan regular basis rays σ τ)

/-- The target is the literal direct image along the actual affine
diagonal ring map, already identified with the scheme-diagonal pullback. -/
def toricDiagonalChartDirectImage : (Spec (CommRingCat.of R)).Modules :=
  (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)))).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)

def toricDiagonalChartTargetIso :
    tilde (diagonalIntersectionModule fan basis rays σ τ) ≅
      toricDiagonalChartDirectImage fan basis rays σ τ :=
  (affinePushforwardStructureIso
    (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))).symm

/-- The genuinely sheafified augmentation to the actual affine diagonal
direct image, with both degree-zero and ring-to-sheaf comparisons explicit. -/
def toricDiagonalFramedSheafAugmentation :
    toricDiagonalFramedSheafComplex fan regular basis rays σ τ ⟶
      (ChainComplex.single₀ (Spec (CommRingCat.of R)).Modules).obj
        (toricDiagonalChartDirectImage fan basis rays σ τ) :=
  (affineTildeChainFunctor (CommRingCat.of R)).map
      (toricDiagonalFramedAugmentation fan regular basis rays σ τ) ≫
    (affineTildeSingleZeroIso (CommRingCat.of R)
      (diagonalIntersectionModule fan basis rays σ τ)).hom ≫
    (ChainComplex.single₀ (Spec (CommRingCat.of R)).Modules).map
      (toricDiagonalChartTargetIso fan basis rays σ τ).hom

/-- Exactness survives the actual affine sheafification: the local
finite Cartier matrix resolves the literal affine diagonal direct image. -/
theorem toricDiagonalFramedSheafAugmentation_quasiIso :
    QuasiIso (toricDiagonalFramedSheafAugmentation fan regular basis rays σ τ) := by
  letI := toricDiagonalFramedAugmentation_quasiIso fan regular basis rays σ τ
  unfold toricDiagonalFramedSheafAugmentation
  infer_instance

end ToricPower
