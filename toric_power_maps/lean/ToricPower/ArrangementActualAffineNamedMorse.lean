module

public import ToricPower.ArrangementAffineMorseCoefficients
public import ToricPower.ArrangementActualAffineModel
public import ToricPower.ArrangementMorseCompositeTransport

/-! # Local Morse vanishing for the actual normalized affine model

The genuine affine tilde equivalence and open-image isomorphism remove
all coefficient-presentation hypotheses. The finite affine coresolution
then gives the calculation on arbitrary unbounded quasicoherent inputs.
The universal comparison retains the actual deck and incidence maps.
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

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "H" => Cellular.homDiagram ℂ
  (universalCartierQuasicoherentSources fan nonempty regular basis rays)

local instance actualMorseAffineChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

variable (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
  (neighborhood : Set (Fin n → ℝ)) (ξ : Module.Dual ℝ (Fin n → ℝ))
  (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
  (center : cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2 ∈ neighborhood)
  (inside : neighborhood ⊆ localStar (augmentedForms (fanArrangementMatrix fan basis rays))
    (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2))

include convex openNeighborhood center inside

/-- Every actual quasicoherent affine coefficient is admitted by the
whole named chart model, before exposing its pushforward composite. -/
theorem universalAffineQuasicoherentDiagram_localMorse_acyclic (cone : fan.cones)
    (outside : (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
      fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone)
    (M : QCoh (fan.affineToricChart cone)) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
        ((universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone).obj M))).Acyclic :=
  universalLocalMorse_single_acyclic_of_equivalence_functor_complex A c
    (universalNegativeHalf A c neighborhood ξ) (toricChartTildeEquivalence fan cone)
    (universalAffineCoefficientDiagram fan nonempty regular basis rays cone)
    (universalAffineQuasicoherentDiagram fan nonempty regular basis rays cone)
    (universalAffineCoefficientDiagram_chart_eq fan nonempty regular basis rays cone)
    (fun coefficient => universalAffineCoefficient_localMorse_acyclic fan nonempty regular
      basis rays cone c neighborhood ξ convex openNeighborhood center inside outside coefficient) M

end ToricPower

end

