module

public import ToricPower.ArrangementAffineMorseFunctor
public import ToricPower.AffineInvertibleMorseFunctor

/-! # Actual affine modules have the required Morse vanishing

The original rank-one theta comparison is extended through exact
sequences and unrestricted free modules, without a finiteness assumption
on the affine coefficient module.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (cone : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => UniversalIncidenceObject A
local notation "ChartRing" => affineCoordinateRing fan.lattice cone.val

/-- The actual affine direct-image Hom diagram has vanishing local
Morse fiber outside its genuine fan face, for every coefficient module. -/
theorem universalAffineCoefficient_localMorse_acyclic
    (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
    (neighborhood : Set (Fin n → ℝ)) (ξ : Module.Dual ℝ (Fin n → ℝ))
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆ localStar (augmentedForms A)
      (cellCenter (augmentedForms A) c.2))
    (outside : (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
      fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone)
    (M : ModuleCat.{0} (affineCoordinateRing fan.lattice cone.val)) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (Cells ⥤ ModuleCat ℂ) 0).obj
        ((universalAffineCoefficientDiagram fan nonempty regular basis rays cone).obj M))).Acyclic := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricChartInclusion_isAffineHom fan cone
  exact affineOpenInvertible_localMorse_acyclic_of_functor A c
    (universalNegativeHalf A c neighborhood ξ) ChartRing
    fan.algebraicRealization (fan.affineToricChartι cone)
    (universalCartierQuasicoherentSources fan nonempty regular basis rays)
    (universalCartierQuasicoherentSources_invertible fan nonempty regular basis rays)
    (universalAffineCoefficientDiagram fan nonempty regular basis rays cone)
    (universalAffineCoefficientDiagram_eq fan nonempty regular basis rays cone)
    (universalCartierChartSections fan basis rays cone regular)
    (universalAffineUnitHomThetaIso fan nonempty regular basis rays cone)
    (universalCartierChartSections_localMorse_acyclic fan basis rays regular cone c
      neighborhood ξ convex openNeighborhood center inside outside) M

end ToricPower

end
