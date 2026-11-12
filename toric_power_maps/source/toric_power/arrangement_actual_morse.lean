module

public import ToricPower.ArrangementActualAffineMorse
public import ToricPower.ArrangementUniversalNormalizedPresentation
public import ToricPower.ArrangementMorseHomIso

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
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
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

local instance actualNormalizedMorseAffineChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

variable (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
  (neighborhood : Set (Fin n → ℝ)) (ξ : Module.Dual ℝ (Fin n → ℝ))
  (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
  (center : cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2 ∈ neighborhood)
  (inside : neighborhood ⊆ localStar (augmentedForms (fanArrangementMatrix fan basis rays))
    (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2))

include convex openNeighborhood center inside


/-- The same vanishing for the literal universal pullback of the
normalized Hom diagram on the genuine affine replacement. The comparison
includes all deck characters and coefficient morphisms. -/
theorem normalizedUniversalAffineModel_localMorse_acyclic
    (outside : ∀ cone : fan.cones,
      (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
        fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone)
    (K : CochainComplex (QCoh fan.algebraicRealization) ℤ) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      (((Cellular.homDiagram ℂ
          (normalizedCartierQuasicoherentSources fan nonempty regular basis rays) ⋙
          (Functor.whiskeringLeft U (IncidenceObject A) (ModuleCat ℂ)).obj
            (universalCoverProjection A)).mapHomologicalComplex (.up ℤ)).obj
        ((affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)).obj K))).Acyclic := by
  have vanishes := universalCartierAffineModel_localMorse_acyclic fan nonempty regular basis rays
    c neighborhood ξ convex openNeighborhood center inside outside K
  have transported := universalLocalMorse_homPrecomposition_acyclic_of_iso A c
    (universalNegativeHalf A c neighborhood ξ)
    (universalCartierQuasicoherentSources fan nonempty regular basis rays)
    (normalizedCartierQuasicoherentSources fan nonempty regular basis rays)
    (universalCoverProjection A)
    (universalNormalizedHomDiagram_standardIso fan nonempty regular basis rays)
    ((affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)).obj K)
    vanishes
  exact transported


end ToricPower

end
