module

public import Continuation.Runtime.SmoothChartPrimeCoordinates
public import Continuation.Runtime.NormalAffineCoordinateOpens

/-!
# Actual affine subcharts are coordinate faces

The torus in a smooth coordinate chart is the principal open obtained by
inverting every constrained coordinate. An affine open containing this
torus is obtained by inverting a subset of these same coordinates. Its
open immersion is therefore exactly the existing character localization
for the corresponding face. Unrestricted Laurent coordinates are never
discarded.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

namespace PaperVerification.ToricCharacters

variable {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    (k : Type*) [Field k] (b : Module.Basis ι ℤ M)

/-- The literal spectrum map of a coordinate-face inclusion is an open
immersion, for faces of every dimension. -/
instance coordinateChartSpecMap_isOpenImmersion {I J : Finset ι} (hIJ : I ⊆ J) :
    IsOpenImmersion (monoidChartSpecMap k (coordinateConeMonoid_antitone b hIJ)) :=
  monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (coordinateConeMonoid_antitone b hIJ) _ (faceDenominatorExponent_mem b I J)
    (coordinateChartInclusion_isLocalizationMap k b hIJ)

/-- The image open of the proved coordinate-face immersion. -/
def coordinateChartFaceOpen {I J : Finset ι} (hIJ : I ⊆ J) :
    (monoidChartScheme k (coordinateConeMonoid b J)).Opens := by
  letI := coordinateChartSpecMap_isOpenImmersion k b hIJ
  exact (monoidChartSpecMap k (coordinateConeMonoid_antitone b hIJ)).opensRange

theorem coordinateChartSpecMap_opensRange {I J : Finset ι} (hIJ : I ⊆ J) :
    coordinateChartFaceOpen k b hIJ =
      PrimeSpectrum.basicOpen (chartCharacter k (coordinateConeMonoid b J)
        (faceDenominatorExponent b I J) (faceDenominatorExponent_mem b I J)) := by
  letI := coordinateChartSpecMap_isOpenImmersion k b hIJ
  exact monoidChartSpecMap_opensRange_of_isLocalizationMap k
    (coordinateConeMonoid_antitone b hIJ) _ (faceDenominatorExponent_mem b I J)
    (coordinateChartInclusion_isLocalizationMap k b hIJ)

/-- A product indexed by a subset of the constrained coordinates is the
actual character denominator of the complementary coordinate face. -/
theorem coordinateChart_faceDenominator_subproduct (I : Finset ι) (J : Finset I) :
    chartCharacter k (coordinateConeMonoid b I)
        (faceDenominatorExponent b (I \ J.image Subtype.val) I)
        (faceDenominatorExponent_mem b (I \ J.image Subtype.val) I) =
      ∏ i ∈ J, coordinateChartGenerator b I k i := by
  have hJI : J.image Subtype.val ⊆ I := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  have hdifference : I \ (I \ J.image Subtype.val) = J.image Subtype.val := by
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hi, h⟩
      by_contra hn
      exact h ⟨hi, hn⟩
    · intro hi
      exact ⟨hJI hi, fun h => h.2 hi⟩
  have hexponent : faceDenominatorExponent b (I \ J.image Subtype.val) I =
      ∑ i ∈ J, b i.val := by
    rw [faceDenominatorExponent, hdifference, Finset.sum_image]
    intro i hi j hj hij
    exact Subtype.ext hij
  apply Subtype.ext
  simp [coordinateChartGenerator, chartCharacter, AddMonoidAlgebra.prod_single,
    hexponent]

/-- Inverting all constrained coordinates gives precisely the actual
open zero-cone chart. -/
theorem coordinateChart_torus_opensRange (I : Finset ι) :
    coordinateChartFaceOpen k b (Finset.empty_subset I) =
        PrimeSpectrum.basicOpen (∏ i : I, coordinateChartGenerator b I k i) := by
  rw [coordinateChartSpecMap_opensRange k b (Finset.empty_subset I)]
  congr 1
  have himage : (Finset.univ : Finset I).image Subtype.val = I := by
    ext i
    simp
  have h := coordinateChart_faceDenominator_subproduct k b I (Finset.univ : Finset I)
  simpa only [himage, Finset.sdiff_self] using h

/-- Every nonempty affine subopen of a normal coordinate chart which
contains its actual torus is exactly the image of a coordinate face.
The normality and noetherian instances are discharged by the original
smooth affine ring when this lemma is used in reconstruction. -/
theorem affineOpen_eq_coordinateChartFace (I : Finset ι)
    [IsDomain (monoidChartAlgebra k (coordinateConeMonoid b I))]
    [IsNoetherianRing (monoidChartAlgebra k (coordinateConeMonoid b I))]
    [IsIntegrallyClosed (monoidChartAlgebra k (coordinateConeMonoid b I))]
    (U : (monoidChartScheme k (coordinateConeMonoid b I)).Opens)
    (hU : IsAffineOpen U) [Nonempty U]
    (hT : coordinateChartFaceOpen k b (Finset.empty_subset I) ≤ U) :
    ∃ (K : Finset ι) (hKI : K ⊆ I),
      U = coordinateChartFaceOpen k b hKI := by
  rw [coordinateChart_torus_opensRange] at hT
  obtain ⟨J, hJ⟩ := PaperVerification.ToricSchemes.affineOpen_eq_basicOpen_subproduct
    (monoidChartAlgebra k (coordinateConeMonoid b I))
    (coordinateChartGenerator b I k) (coordinateChartGenerator_prime b I k) U hU hT
  refine ⟨I \ J.image Subtype.val, Finset.sdiff_subset, ?_⟩
  rw [coordinateChartSpecMap_opensRange,
    coordinateChart_faceDenominator_subproduct]
  exact hJ

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.affineOpen_eq_coordinateChartFace
