module

public import ToricPower.ArrangementInverseExteriorLabels
public import ToricPower.DiagonalTopQuotient

/-!
# Canonical top-quotient map for actual represented cellular realization

Each actual incidence `c ⟶ d` supplies the map from `Q(d) ⊗ R(c)`
to `Q(d) ⊗ R(d)`. Applying the genuine cellular cochain functor and the
proved complete diagonal coefficient comparison gives a map to the
ordinary pullback of the dual diagonal complex. Its genuine top quotient
then gives a specified map to the actual diagonal line in degree `n`.

These are maps of actual module-sheaf complexes. Their construction does
not assume that diagonal pullback is exact, that the map is a
quasi-isomorphism, or that the resulting line has been identified with
the boundary Cartier line. Those are independent local computations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays

local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The represented cellular complex is evaluated in the actual pulled
dual kernel by its literal incidence maps and its actual finite
cellular differentials. -/
def arrangementRepresentedTensorEvaluation (c : C) :
    ((((tensoringRight (X).Modules).obj ((R).obj c)).mapHomologicalComplex (.up ℕ)).obj
      ((arrangementCellularSheafRealization fan nonempty regular basis rays).obj
        (Cellular.representable ℂ c))) ⟶
      (((Scheme.Modules.pullback (toricDiagonal fan)).mapHomologicalComplex (.up ℕ)).obj K) :=
  (cellularCoefficientComplexIso A ℂ ((tensoringRight (X).Modules).obj ((R).obj c))
      (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c))).hom ≫
    (arrangementCellularCochainFunctor A ℂ).map
      (Cellular.representedTensorEvaluationDiagram ℂ Q R c) ≫
    (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv

/-- The specified top-quotient augmentation, before its local
quasi-isomorphism calculation. Every component is `O_X`-linear. -/
def arrangementRepresentedTopAugmentation (c : C) :
    ((((tensoringRight (X).Modules).obj ((R).obj c)).mapHomologicalComplex (.up ℕ)).obj
      ((arrangementCellularSheafRealization fan nonempty regular basis rays).obj
        (Cellular.representable ℂ c))) ⟶
      (HomologicalComplex.single (X).Modules (.up ℕ) n).obj J :=
  arrangementRepresentedTensorEvaluation fan nonempty regular basis rays c ≫
    dualDiagonalPulledTopAugmentation fan nonempty regular basis rays

end ToricPower

end
