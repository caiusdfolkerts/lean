module

public import ToricPower.DiagonalGlobalAugmentation
public import ToricPower.DiagonalFramedResolution
public import ToricPower.PowerSheafCore
public import ToricPower.OpenBaseChangeNaturality

/-!
# The actual diagonal structure sheaf on a product chart

The geometric square is an actual scheme pullback. Its inverse-image open
is therefore precisely the actual overlap chart. Ordinary module-sheaf
restriction of direct image, followed by the genuine unit-sheaf comparison,
identifies the restricted global diagonal structure sheaf with the actual
affine diagonal direct image used by the local cellular calculation.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "δ" => toricDiagonal fan
local notation "g" => Spec.map (CommRingCat.ofHom
  (diagonalChartToIntersection fan basis rays σ τ))

/-- The open preimage of a product chart under the actual diagonal is
exactly the ordinary overlap chart, as equality of actual scheme opens. -/
theorem diagonalChart_preimage_opensRange :
    δ ⁻¹ᵁ (chart).opensRange = (overlap).opensRange := by
  let h := diagonalProductChart_isPullback fan basis rays σ τ
  calc
    δ ⁻¹ᵁ (chart).opensRange = (pullback.fst δ chart).opensRange :=
      (Scheme.Hom.opensRange_pullbackFst chart δ).symm
    _ = (h.isoPullback.hom ≫ pullback.fst δ chart).opensRange :=
      (Scheme.Hom.opensRange_comp_of_isIso _ _).symm
    _ = (overlap).opensRange := by
      simp only [h.isoPullback_hom_fst]

/-- The literal chart restriction of the global diagonal structure sheaf
is the literal direct image along the previously identified affine
diagonal ring map. -/
def diagonalStructureChartIso :
    (Scheme.Modules.pullback chart).obj (diagonalStructureSheaf fan) ≅
      toricDiagonalChartDirectImage fan basis rays σ τ :=
  ((Scheme.Modules.restrictFunctorIsoPullback chart).app
      (diagonalStructureSheaf fan)).symm ≪≫
    pushforwardRestrictionIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w
      (diagonalChart_preimage_opensRange fan basis rays σ τ).le
      (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward g).mapIso (Scheme.Modules.restrictUnitIso overlap)

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

/-- The global diagonal augmentation on the literal affine chart is the
adjunct of its actual restricted multiplication map. The comparison of
adjunctions and open base change is proved, not assumed. -/
@[reassoc]
theorem diagonalProductAugmentation_chart_adjunct {d : ℕ}
    (c : NormalizedCell A d) :
    (Scheme.Modules.pullback chart).map
        (diagonalProductAugmentation fan nonempty regular basis rays c) ≫
        (diagonalStructureChartIso fan basis rays σ τ).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso δ g overlap chart
          (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
            (diagonalProductSheaf fan nonempty regular basis rays c) ≫
          (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
            ((Scheme.Modules.pullback δ).obj
              (diagonalProductSheaf fan nonempty regular basis rays c)) ≫
          (Scheme.Modules.restrictFunctor overlap).map
            (diagonalPullbackProductMap fan nonempty regular basis rays c ≫
              diagonalTensorToStructure fan nonempty regular basis rays c) ≫
          (Scheme.Modules.restrictUnitIso overlap).hom) := by
  exact pullback_pushforwardRestrictionIso_unit_homEquiv δ g overlap chart
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    (diagonalChart_preimage_opensRange fan basis rays σ τ).le _

end ToricPower
