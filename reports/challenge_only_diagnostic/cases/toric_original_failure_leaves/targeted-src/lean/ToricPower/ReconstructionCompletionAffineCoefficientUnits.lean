module

public import ToricPower.ReconstructionCompletionAffineCoefficients
public import ToricPower.SchemeExternalSections
public import ToricPower.SchemeProjectionNaturality

/-! # The affine coefficient as its original normalized unit map

The inverse-label comparison retains the original unit-source map,
including the genuine projection map and the genuine pullback unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

section Naturality

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The normalized projection adjunct retains every original label map. -/
theorem reconstruction_normalizedProjectionAdjunct_naturality
    {M M' : X.Modules} (f : M ⟶ M')
    (x : 𝟙_ X.Modules ⟶ M ⊗ (Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) :
    ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
          (x ≫ BondalThomsen.schemeProjectionFormulaMap j M)) ≫
        (Scheme.Modules.pullback j).map f =
      (Scheme.Modules.pullbackObjUnitIso j).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
          ((x ≫ f ▷ (Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) ≫
            BondalThomsen.schemeProjectionFormulaMap j M') := by
  have natural :
      f ▷ (Scheme.Modules.pushforward j).obj (𝟙_ U.Modules) ≫
        BondalThomsen.schemeProjectionFormulaMap j M' =
      BondalThomsen.schemeProjectionFormulaMap j M ≫
        (Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map f) :=
    schemeProjectionFormulaMap_natural j f
  simp only [Category.assoc]
  rw [natural]
  rw [← Category.assoc x]
  rw [(Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv_naturality_right_symm]

end Naturality

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "R" => arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Rs" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "U" => Spec (CommRingCat.of (affineCoordinateRing fan.lattice τ.val))
local notation "j" => fan.affineToricChartι τ
local notation "E" => quasicoherentAffineUnitImage j
local notation "F" => Scheme.Modules.pullback j
local notation "G" => Scheme.Modules.pushforward j

local instance : IsAffineHom j := toricChartInclusion_isAffineHom fan τ

/-- The original Hom coefficient as an actual structure-sheaf map into
its original underlying inverse-right label. -/
def reconstructionAffineCoefficientUnit (c : C) (h : (P₀).obj (op c) ⟶ E) :
    𝟙_ (X).Modules ⟶ (Rs).obj c ⊗ (G).obj (𝟙_ (U).Modules) :=
  (((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app c h).hom ≫
    ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).hom.app c) ▷
      (G).obj (𝟙_ (U).Modules)

/-- No scalar or finite-basis choice intervenes: the coefficient's unit
map is the normalized adjunct of that same original inverse-twist map. -/
theorem reconstructionAffineCoefficientIso_unit (c : C) (h : (P₀).obj (op c) ⟶ E) :
    (moduleUnitActualSectionsLinearEquiv ℂ U ((F).obj ((Rs).obj c))).symm
      ((reconstructionAffineCoefficientIso fan nonempty regular basis rays τ).hom.app c h) =
      (Scheme.Modules.pullbackObjUnitIso j).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
          (reconstructionAffineCoefficientUnit fan nonempty regular basis rays τ c h ≫
            BondalThomsen.schemeProjectionFormulaMap j ((Rs).obj c)) := by
  rw [reconstructionAffineCoefficientIso_apply,
    moduleUnitActualSectionsLinearEquiv_symm_naturality]
  erw [LinearEquiv.symm_apply_apply]
  exact reconstruction_normalizedProjectionAdjunct_naturality j
    ((arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays).hom.app c)
    (((reconstructionOriginalUnitHomIso fan nonempty regular basis rays).hom.app E).app c h).hom

end ToricPower

end
