module

public import ToricPower.ArrangementActualMorse
public import ToricPower.ArrangementNormalizedMorseFactors
public import ToricPower.ArrangementMorseMappedComposition
public import ToricPower.CanonicalAffineMorseComparison

/-! # A literal unbounded representative of the normalized right adjoint

The complex is obtained from the actual input shift, the finite affine
coresolution, and the actual normalized Cartier Hom diagram. Its
localization is identified with the paper's normalized right adjoint.
Thus the subsequent Morse calculation applies to that precise image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "Cells" => IncidenceObject A
local notation "UniversalCells" => UniversalIncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "PN" => normalizedCartierQuasicoherentSources fan nonempty regular basis rays
local notation "H" => Cellular.homDiagram ℂ PN

local instance normalizedMorseDerivedQCoh : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance normalizedMorseDerivedCells : HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

local instance normalizedMorseLocalLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).1
local instance normalizedMorseLocalColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).2

/-- The model represents the actual normalized right adjoint. The entire
natural isomorphism is established before evaluating the coefficient complex. -/
def normalizedAffineMorseModelIso (K : CochainComplex (QCoh X) ℤ) :
    letI := nonempty
    (arrangementNormalizedDerivedHom fan regular basis rays).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((normalizedAffineMorseModel fan nonempty regular basis rays).obj K) := by
  letI := nonempty
  exact (normalizedAffineMorseModelNatIso fan nonempty regular basis rays).app K

/-- Genuine local Morse vanishing for the precise normalized image
representative, without any bound on the input complex. -/
theorem normalizedUniversalMorseModel_acyclic
    (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
    (neighborhood : Set (Fin n → ℝ)) (ξ : Module.Dual ℝ (Fin n → ℝ))
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆ localStar (augmentedForms A)
      (cellCenter (augmentedForms A) c.2))
    (outside : ∀ cone : fan.cones,
      (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
        fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone)
    (K : CochainComplex (QCoh fan.algebraicRealization) ℤ) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      ((normalizedUniversalMorseModel fan nonempty regular basis rays).obj K)).Acyclic := by
  rw [normalizedUniversalMorseModel_eq_construction]
  have vanishes := normalizedUniversalAffineModel_localMorse_acyclic
    fan nonempty regular basis rays c neighborhood ξ convex openNeighborhood center inside outside
  have canonical := (universalLocalMorse_canonicalAffineHom_all_acyclic_iff A c
    (universalNegativeHalf A c neighborhood ξ) X (toricDerivedChartOpen fan)
    PN (universalCoverProjection A) (toricDerivedChartList fan)).mpr vanishes
  exact universalLocalMorse_pulledShiftedHomDiagramModel_acyclic PN A c
    (universalNegativeHalf A c neighborhood ξ) (universalCoverProjection A)
    (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ))
    (canonicalAffineCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)) canonical K



end ToricPower

end
