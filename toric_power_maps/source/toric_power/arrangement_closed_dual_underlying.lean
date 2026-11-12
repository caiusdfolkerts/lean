module

public import ToricPower.ArrangementClosedDualFunctor
public import ToricPower.ArrangementCellularChainCoefficientFunctor
public import ToricPower.ClosedContravariantCoefficient

/-! # The literal module sheaves underlying the closed dual chain

This comparison passes the original finite biproducts through the full
quasicoherent inclusion and then uses the actual inverse Cartier tensor
isomorphism. Every boundary map is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedDualUnderlyingIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedDualUnderlyingQBiproducts : HasFiniteBiproducts (QCoh fan.algebraicRealization) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedDualUnderlyingMBiproducts : HasFiniteBiproducts fan.algebraicRealization.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "line" b => quasicoherentCartierObject X (invariantCartierDivisor fan nonempty regular b)

theorem arrangementDualInverseTensorUnderlying_eq (b : fan.Ray → ℤ) :
    ((arrangementDualInverseTensorFunctor fan regular basis rays).flip.obj (line b)) ⋙
      quasicoherentInclusion X =
        arrangementDualInverseTensorCoefficientDiagram fan regular basis rays b := rfl

def arrangementDualInverseTensorUnderlyingIso (b : fan.Ray → ℤ) :
    ((arrangementDualInverseTensorFunctor fan regular basis rays).flip.obj (line b)) ⋙
      quasicoherentInclusion X ≅
        arrangementDualDifferenceCoefficientDiagram fan regular basis rays b :=
  eqToIso (arrangementDualInverseTensorUnderlying_eq fan regular basis rays b) ≪≫
    arrangementDualInverseTensorCoefficientIso fan regular basis rays b

/-- The source of the geometric augmentation is the original chain of
inverse Cartier tensors in the actual quasicoherent category. -/
def arrangementClosedDualUnderlyingIso (selected : Set (Fin s ⊕ Fin n)) (b : fan.Ray → ℤ) :
    ((quasicoherentInclusion X).mapHomologicalComplex (.down ℕ)).obj
      ((arrangementClosedDualFunctor fan regular basis rays selected).obj (line b)) ≅
    arrangementCellularChainComplex A ℂ
      (Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected)
        (arrangementDualDifferenceCoefficientDiagram fan regular basis rays b)) :=
  cellularChainCoefficientComplexIso A ℂ (quasicoherentInclusion X)
      ((arrangementClosedDualCoefficientFunctor fan regular basis rays selected).obj (line b)) ≪≫
    (arrangementCellularChainFunctor A ℂ).mapIso
      (Cellular.closedContravariantCoefficientIso (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected) (quasicoherentInclusion X)
        ((arrangementDualInverseTensorFunctor fan regular basis rays).flip.obj (line b))) ≪≫
    (arrangementCellularChainFunctor A ℂ).mapIso
      ((Cellular.closedContravariantLabelEndofunctor (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected)).mapIso
          (arrangementDualInverseTensorUnderlyingIso fan regular basis rays b))

end ToricPower

end
