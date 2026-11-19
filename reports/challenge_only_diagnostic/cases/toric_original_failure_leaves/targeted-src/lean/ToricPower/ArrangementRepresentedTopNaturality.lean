module

public import ToricPower.ArrangementRepresentableTopAugmentation
public import ToricPower.ArrangementRepresentedSource

/-!
# Source naturality of the specified represented top quotient

The original top map has the actual incidence compatibility needed to
transpose it through the inverse-line adjunction. This is an equality
of entire sheaf-complex maps, before passing to homology or localization.
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
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementCellularSheafRealization fan nonempty regular basis rays

local instance representedTopNaturalityBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The literal source-incidence square for the genuine augmentation. -/
theorem arrangementRepresentedTopAugmentation_source
    {c d : C} (f : c ⟶ d) :
    (((tensoringRight (X).Modules).obj ((R).obj c)).mapHomologicalComplex (.up ℕ)).map
        ((Φ).map (Cellular.representablePrecompose ℂ f)) ≫
      arrangementRepresentedTopAugmentation fan nonempty regular basis rays c =
    (((tensoringRight (X).Modules).map ((R).map f)).mapHomologicalComplex (.up ℕ)).app
        ((Φ).obj (Cellular.representable ℂ d)) ≫
      arrangementRepresentedTopAugmentation fan nonempty regular basis rays d := by
  unfold arrangementRepresentedTopAugmentation arrangementRepresentedTensorEvaluation
    arrangementCellularSheafRealization
  simpa only [cellularRepresentedTensorEvaluation, Category.assoc] using congrArg (fun g => g ≫
      (diagonalPulledCellularComplexIso fan nonempty regular basis rays).inv ≫
        dualDiagonalPulledTopAugmentation fan nonempty regular basis rays)
    (cellularRepresentedTensorEvaluation_source A ℂ Q R f)

end ToricPower

end
