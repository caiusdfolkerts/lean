module

public import ToricPower.ArrangementRepresentedTopNaturality
public import ToricPower.ArrangementInverseRightTensor
public import ToricPower.ParametricTensorComplexMate
public import ToricPower.ComplexAdjunctionQuasiIso

/-!
# The original source-natural represented augmentation

The actual cellular top quotient is transposed through its actual
inverse-right line. The target is the original right Cartier diagram
tensored with the genuine top line `J`. Naturality retains every
translated incidence, before localization.

The conditional quasi-isomorphism lemma below only transports the
separate geometric calculation of the specified top quotient; it does
not assume that calculation as part of any functor's definition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightCartierDiagram fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "Φ" => Cellular.representableFunctor ℂ (C := Cells) ⋙
  arrangementCellularSheafRealization fan nonempty regular basis rays
local notation "Z" => Functor.obj (HomologicalComplex.single (Scheme.Modules X) (ComplexShape.up ℕ) n) J

/-- The specified original top quotient, transposed naturally on all
representables to the original right-label target. -/
def arrangementRepresentedAugmentation :
    Φ ⟶ P₀ ⋙ (tensoringRight (X).Modules).obj J ⋙
      HomologicalComplex.single (X).Modules (.up ℕ) n :=
  parametricTensorComplexMate R Z Φ
      (arrangementRepresentedTopAugmentation fan nonempty regular basis rays)
      (fun f => arrangementRepresentedTopAugmentation_source fan nonempty regular basis rays f) ≫
    (internalHomComplexSingleIso R J n).hom ≫
    Functor.whiskerRight
      (arrangementInverseRightInternalHomAtIso fan basis rays nonempty regular J).hom
      (HomologicalComplex.single (X).Modules (.up ℕ) n)

/-- Each actual inverse-right line has its genuine exact tensor
inverse; this follows from its constructed Cartier divisor. -/
theorem arrangementInverseRightTensor_isEquivalence (c : Cells) :
    (tensorLeft ((R).obj c)).IsEquivalence := by
  letI := toricSchemeIntegral fan nonempty
  exact (cartierTensorEquivalence (invariantCartierDivisor fan nonempty regular
    (arrangementDualRightCoefficients fan basis rays c))).isEquivalence_functor

/-- The actual adjunction transports a proved geometric top quotient
without changing its source map or its target normalization. -/
theorem arrangementRepresentedAugmentation_quasiIso_of_top (c : Cells)
    [QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)] :
    QuasiIso ((arrangementRepresentedAugmentation fan nonempty regular basis rays).app (op c)) := by
  letI := arrangementInverseRightTensor_isEquivalence fan nonempty regular basis rays c
  haveI : QuasiIso
      ((parametricTensorComplexMate R Z Φ
        (arrangementRepresentedTopAugmentation fan nonempty regular basis rays)
        (fun f => arrangementRepresentedTopAugmentation_source
          fan nonempty regular basis rays f)).app (op c)) := by
    exact complexAdjunction_homEquiv_quasiIso (ihom.adjunction ((R).obj c)) (.up ℕ)
      ((Φ).obj (op c)) Z
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight ((R).obj c))
        (.up ℕ)).hom.app ((Φ).obj (op c)) ≫
          arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)
  unfold arrangementRepresentedAugmentation
  change QuasiIso (_ ≫ _ ≫ _)
  infer_instance

end ToricPower

end
