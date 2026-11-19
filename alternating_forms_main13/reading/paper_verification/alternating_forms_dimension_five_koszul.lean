module

public import PaperVerification.DimensionFiveGradedBasis
public import PaperVerification.HomogeneousBasisProfile
public import PaperVerification.AlternatingFormsExteriorAugmentation
public import PaperVerification.AlternatingFormsExteriorKoszul
public import PaperVerification.AlternatingFormsGenericHilbertCoordinates

/-!
# The actual dimension-five negative case of Proposition 5.3

One principal open in the full space of pairs has the proved homogeneous
ranks (1,5,8,1). Its actual exterior quotient therefore has nonzero ordinary
Tor in internal degree six and homological degree strictly below six.
The augmented basis and every compatibility with the original exterior
grading are constructed here; none is added as a genericity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.DimensionFiveKoszul

open DimensionFiveGradedBasis ExteriorAugmented

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Independently specified graded data and an actual nonzero ordinary Tor
piece. The basis's degrees are the original exterior degrees. -/
structure OriginalDegreeSixTorObstruction (f g : ⋀[K]^2 M) where
  basis : Module.Basis (Option PositiveIndex.{u}) K (ExteriorAugmented.Quotient f g)
  unit : basis none=1
  homogeneous : ∀ i,basis (some i)∈(grading f g).piece (positiveDegree i)
  augmentation_zero : ∀ i,augmentation f g (basis (some i))=0
  product_degree : ∀ a b c,AugmentedAlgebraBasis.productCoefficients basis a b c≠0 →
    positiveDegree c=positiveDegree a+positiveDegree b
  ordinaryTor_nonzero : ∃ r,r<6 ∧
    WeightedBar.torPiece (augmentation f g) basis unit augmentation_zero
      positiveDegree product_degree r 6≠⊥

/-- Failure of ordinary Tor concentration for every finite homogeneous
augmented basis compatible with the actual exterior grading. This is
universally quantified data, not a choice assumed at the principal open. -/
def EveryHomogeneousBasisHasOffDiagonalTor (f g : ⋀[K]^2 M) : Prop :=
  ∀ (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(grading f g).piece (δ i))
    (hε : ∀ i,augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b),
    ¬WeightedBar.HasDiagonalTor (augmentation f g) B hunit hε δ hδ

variable [FiniteDimensional K M] (f g : ⋀[K]^2 M)

def obstructionOfHilbertProfile
    (h : ∀ d,Module.finrank K (ExteriorQuotientDegree f g d)=rankProfile d) :
    OriginalDegreeSixTorObstruction f g := by
  let hp : ∀ d,Module.finrank K ((grading f g).piece d)=rankProfile d :=
    fun d => (grading_piece_finrank f g d).trans (h d)
  exact {
    basis := DimensionFiveGradedBasis.basis (grading f g) (augmentation f g)
      (grading_zero f g) hp
    unit := basis_none (grading f g) (augmentation f g) (grading_zero f g) hp
    homogeneous := basis_positive_mem (grading f g) (augmentation f g) (grading_zero f g) hp
    augmentation_zero := basis_positive_augmentation (grading f g) (augmentation f g)
      (grading_zero f g) hp (augmentation_piece_zero f g)
    product_degree := product_homogeneous (grading f g) (augmentation f g)
      (grading_zero f g) hp (grading_mul f g)
    ordinaryTor_nonzero := ordinaryTor_off_diagonal (grading f g) (augmentation f g)
      (grading_zero f g) hp (augmentation_piece_zero f g) (grading_mul f g) }

theorem every_basis_obstructionOfHilbertProfile
    (h : ∀ d,Module.finrank K (ExteriorQuotientDegree f g d)=rankProfile d) :
    EveryHomogeneousBasisHasOffDiagonalTor f g := by
  intro I inst B hunit δ hpos hhom hε hδ
  exact HomogeneousBasisProfile.not_hasDiagonalTor
    (grading f g) B δ (grading_zero f g) hunit hhom hpos
    (fun d => (grading_piece_finrank f g d).trans (h d))
    (augmentation f g) hε hδ

/-- All natural degrees are included. Only the four low determinant
coefficients are evaluated; the remaining degrees use the proved cutoff. -/
theorem dimensionFive_walk_profile (d : ℕ) : StripWalks.paperWalkCount 5 d=rankProfile d := by
  rcases d with _ | _ | _ | _ | d
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 0 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_zero]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 1 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_one,PathDeterminant.paperMatrix]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 2 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_two,PathDeterminant.paperMatrix]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 3 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_three,PathDeterminant.paperMatrix]
  · exact paperWalkCount_odd_above_cutoff 2 (d+4) (by omega)

/-- A certificate of diagonal ordinary Tor contradicts the obstruction
for every compatible homogeneous augmented basis. -/
theorem not_certificate_of_every_basis (h : EveryHomogeneousBasisHasOffDiagonalTor f g) :
    ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate f g) := by
  rintro ⟨C⟩
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  exact h C.Index C.basis C.unit C.degree C.positive C.homogeneous
    C.augmentation_zero C.product_degree C.diagonal

variable [CharZero K]

/-- The full dimension-five generic negative case: the coefficient basis
covers all two-forms on every five-dimensional space, and the principal
open is proved nonempty. Every point has a nonzero off-diagonal subspace
of genuine ordinary augmentation Tor in the original exterior grading. -/
theorem paper_proposition_5_3_dimension_five (hdim : Module.finrank K M=5) :
    ∃ b₂ : Module.Basis (OddOrbitSlot 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) K,Q≠0 ∧
        (∃ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0) ∧
        ∀ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0 →
          Nonempty (OriginalDegreeSixTorObstruction
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) ∧
          EveryHomogeneousBasisHasOffDiagonalTor
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨b₂,Q,hQ,h⟩ := odd_generic_paperHilbert_in_vector_space (K := K) (M := M) 1
    (by simpa using hdim)
  refine ⟨b₂,Q,hQ,?_,?_⟩
  · by_contra hn
    apply hQ
    apply MvPolynomial.funext
    intro y
    rw [map_zero]
    by_contra hy
    exact hn ⟨y,hy⟩
  · intro y hy
    have hp : ∀ d,Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 d)=rankProfile d :=
      fun d => ((h y hy).1 d).trans (dimensionFive_walk_profile d)
    exact ⟨⟨obstructionOfHilbertProfile _ _ hp⟩,every_basis_obstructionOfHilbertProfile _ _ hp⟩

/-- The generic dimension-five quotient admits no actual homogeneous
Koszul certificate for its original exterior grading. -/
theorem paper_proposition_5_3_dimension_five_not_koszul (hdim : Module.finrank K M=5) :
    ∃ b₂ : Module.Basis (OddOrbitSlot 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) K,Q≠0 ∧
        (∃ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0) ∧
        ∀ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0 →
          ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ :=
    paper_proposition_5_3_dimension_five (K := K) (M := M) hdim
  exact ⟨b₂,Q,hQ,hpoint,fun y hy => not_certificate_of_every_basis _ _ (h y hy).2⟩

end PaperVerification.AlternatingForms.DimensionFiveKoszul
