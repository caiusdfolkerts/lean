module

public import ToricPower.ArrangementAffineEvaluationComplex
public import ToricPower.DiagonalCellularInclusions
public import ToricPower.DiagonalTopQuotient

/-! # The complete diagonal quotient on exterior generators

These formulas retain the original inverse-cell inclusion and the
original top quotient through the full scalar complex isomorphism.
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
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "E" => exteriorLabelDiagram fan Q R
local notation "M" => diagonalExteriorDualDiagram fan nonempty regular basis rays
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays

local instance reconstructionDiagonalGeneratorsBiproducts : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionDiagonalGeneratorsCells (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- The genuine top-cell map expressed on its original two exterior
Cartier factors. -/
def reconstructionDiagonalExternalTop (d : NormalizedCell A n) :
    (E).obj ⟨n,d⟩ ⟶ H :=
  (diagonalExteriorCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
    diagonalInverseCellTopQuotient fan nonempty regular basis rays d

/-- Every inverse cellular label keeps its original inclusion under
the full exterior cochain comparison. -/
@[reassoc]
theorem reconstructionDiagonalExterior_inclusion (q : ℕ) (d : NormalizedCell A q) :
    arrangementCellularCochainInclusion A ℂ E q d ≫
        (diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays).inv.f q =
      (diagonalExteriorCoefficientIso fan nonempty regular basis rays).inv.app ⟨q,d⟩ ≫
        biproduct.ι (fun c : NormalizedCell A q =>
          diagonalInverseProductSheaf fan nonempty regular basis rays c) d ≫
        (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom := by
  change _ ≫ ((arrangementCellularCochainFunctor A ℂ).map
      (diagonalExteriorCoefficientIso fan nonempty regular basis rays).inv).f q ≫
    (diagonalExteriorDualComplexIso fan nonempty regular basis rays).inv.f q = _
  rw [cellularCochainMap_inclusion_assoc, diagonalExteriorDualComplexIso_inclusion]

/-- The full cochain comparison retains the specified original top quotient. -/
@[reassoc]
theorem reconstructionDiagonalExterior_top (d : NormalizedCell A n) :
    arrangementCellularCochainInclusion A ℂ E n d ≫
        (diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays).inv.f n ≫
        dualDiagonalTopQuotient fan nonempty regular basis rays =
      reconstructionDiagonalExternalTop fan nonempty regular basis rays d := by
  rw [reconstructionDiagonalExterior_inclusion_assoc]
  rfl

end ToricPower

end
