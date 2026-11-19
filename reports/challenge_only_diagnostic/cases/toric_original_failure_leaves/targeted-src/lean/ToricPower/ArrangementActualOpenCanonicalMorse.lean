module

public import ToricPower.ArrangementActualOpenNamedMorse
public import ToricPower.ArrangementMorseSinglePresentation
public import ToricPower.ToricDerivedAffineCover
public import ToricPower.ArrangementActualOpenModel
public import ToricPower.ArrangementMorsePrecomposition

/-! # Named coefficient models on the genuine image-open charts

Transport through the actual affine-chart/image-open isomorphism is
performed at the full functor level. No coefficient or incidence map
is replaced, and arbitrary quasicoherent coefficients are admitted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

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

local instance actualOpenCanonicalMorseChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

local instance actualOpenCanonicalMorseRange (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone).opensRange.ι :=
  toricDerivedChartOpen_isAffineHom fan cone

theorem universalChartOpenCoefficientDiagram_canonicalMorse
    (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
    (neighborhood : Set (Fin n → ℝ)) (ξ : Module.Dual ℝ (Fin n → ℝ))
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆ localStar (augmentedForms (fanArrangementMatrix fan basis rays))
      (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2))
    (cone : fan.cones)
    (outside : (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
      fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone)
    (M : QCoh (toricDerivedChartOpen fan cone).toScheme) :
    canonicalSingleMorseAcyclic (fanArrangementMatrix fan basis rays) c
      (universalNegativeHalf (fanArrangementMatrix fan basis rays) c neighborhood ξ)
      ((universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone).obj M) :=
  canonicalSingleMorseAcyclic_all_of_raw (fanArrangementMatrix fan basis rays) c
    (universalNegativeHalf (fanArrangementMatrix fan basis rays) c neighborhood ξ)
    (universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone).obj
    (universalChartOpenCoefficientDiagram_localMorse_acyclic fan nonempty regular basis rays
      c neighborhood ξ convex openNeighborhood center inside cone outside) M

end ToricPower

end
