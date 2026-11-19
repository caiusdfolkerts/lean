module

public import ToricPower.ReconstructionCompletionGeometricAugmentation
public import ToricPower.SchemeAdjunctUnitSections
public import ToricPower.ArrangementOriginalAffineUnitHom

/-!
# Actual affine coefficients of geometric reconstruction

The Hom diagram of the affine direct image of the unit is expressed on
the actual pulled-back inverse labels. Each coefficient is the literal
normalized adjunct of its original projection-formula image. This fixes
the map used by the exterior-section comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

universe u

section ActualAdjunct

variable (k : Type u) [Field k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]

/-- The actual normalized adjunct represents exactly the original
global direct-image section, including its specified scalar structure. -/
theorem reconstruction_normalizedAdjunct_globalSection (M : U.Modules)
    (a : 𝟙_ X.Modules ⟶ (Scheme.Modules.pushforward j).obj M) :
    moduleUnitActualSectionsLinearEquiv k U M
        ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ M).symm a) =
      (pushforwardGlobalBaseSectionsIso k j).hom.app M
        (moduleUnitActualSectionsLinearEquiv k X ((Scheme.Modules.pushforward j).obj M) a) :=
  normalizedUnitAdjunct_section j M a ⊤

end ActualAdjunct

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "I" => quasicoherentInclusion X
local notation "R" => arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Rs" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "U" => Spec (CommRingCat.of (affineCoordinateRing fan.lattice τ.val))
local notation "j" => fan.affineToricChartι τ
local notation "E" => quasicoherentAffineUnitImage j
local notation "F" => Scheme.Modules.pullback j
local notation "G" => Scheme.Modules.pushforward j
local notation "ΓX" => FiniteCover.schemeBaseSections ℂ X ⊤
local notation "ΓU" => FiniteCover.schemeBaseSections ℂ U ⊤

local instance reconstructionAffineCoefficientAffine : IsAffineHom j :=
  toricChartInclusion_isAffineHom fan τ

/-- The complete original Hom diagram is the complete section diagram
of the inverse-right labels on the actual affine chart. -/
def reconstructionAffineCoefficientIso :
    (Cellular.homDiagram ℂ P₀).obj E ≅ (Rs ⋙ F) ⋙ ΓU :=
  (reconstructionOriginalUnitHomIso fan nonempty regular basis rays).app E ≪≫
    Functor.isoWhiskerLeft (R ⋙ tensorRight E)
      (reconstructionQuasicoherentUnitHomSectionsIso ℂ X) ≪≫
    Functor.isoWhiskerRight
      (schemeProjectionInvertibleDiagramIso j (R ⋙ I)
        (arrangementDualRightQuasicoherentDiagram_invertible fan nonempty regular basis rays)) ΓX ≪≫
    Functor.isoWhiskerLeft (R ⋙ I ⋙ F) (pushforwardGlobalBaseSectionsIso ℂ j) ≪≫
    Functor.isoWhiskerRight
      (arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays)
      (F ⋙ ΓU)

/-- The coefficient section is exactly the normalized pullback adjunct
of the original inverse-twist unit map and original projection map. -/
theorem reconstructionAffineCoefficientIso_apply (c : C)
    (h : (P₀).obj (op c) ⟶ E) :
    (reconstructionAffineCoefficientIso fan nonempty regular basis rays τ).hom.app c h =
      (ΓU).map ((F).map
        ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).hom.app c))
        (moduleUnitActualSectionsLinearEquiv ℂ U ((F).obj (((R).obj c).obj))
          ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
            ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
              ((((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app c h).hom ≫
                BondalThomsen.schemeProjectionFormulaMap j (((R).obj c).obj)))) := by
  let x := (((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app c h).hom
  let a := x ≫ BondalThomsen.schemeProjectionFormulaMap j (((R).obj c).obj)
  change (ΓU).map ((F).map
      ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).hom.app c))
      ((pushforwardGlobalBaseSectionsIso ℂ j).hom.app ((F).obj (((R).obj c).obj))
        (moduleUnitActualSectionsLinearEquiv ℂ X ((G).obj ((F).obj (((R).obj c).obj))) a)) = _
  rw [← reconstruction_normalizedAdjunct_globalSection]

end ToricPower

end
