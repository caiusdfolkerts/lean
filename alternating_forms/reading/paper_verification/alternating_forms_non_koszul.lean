module

public import PaperVerification.HomogeneousBasisHilbert
public import PaperVerification.HomogeneousDiagonalDuality
public import PaperVerification.KoszulDiagonalSeries
public import PaperVerification.AlternatingFormsIntrinsicQuadraticDual
public import PaperVerification.ExteriorKoszulSeriesObstruction
public import PaperVerification.AlternatingFormsExteriorKoszul
public import PaperVerification.AlternatingFormsCubicInjectivity

/-!
# The complete higher-dimensional non-Koszul direction

For every finite homogeneous augmented basis, the actual diagonal bar
homology is compared with the independently defined ordinary quadratic
dual. Koszul concentration therefore gives its genuine Hilbert identity.
The proved PBW formula contradicts the actual exterior degree cutoff.
The final generic theorem constructs a nonempty principal open in the
full coefficient space in every dimension at least six.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.NonKoszul

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The constant coefficient follows from the actual proved PBW series. -/
theorem dual_constant (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    PowerSeries.coeff 0 (QuadraticDual.tensorHilbertSeries f g)=1 := by
  have h := congrArg PowerSeries.constantCoeff
    (QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g hinj)
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h

/-- Every homogeneous basis of the actual original quotient has
non-diagonal ordinary Tor when the cubic wedge map is injective. -/
theorem not_hasDiagonalTor
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(ExteriorAugmented.grading f g).piece (δ i))
    (hε : ∀ i,ExteriorAugmented.augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b) :
    ¬WeightedBar.HasDiagonalTor (ExteriorAugmented.augmentation f g)
      B hunit hε δ hδ := by
  intro hKoszul
  have hdim : ∀ r,(Module.finrank K
      ((WeightedBar.internalComplex (ExteriorAugmented.augmentation f g)
        B hunit hε δ hδ (r+1)).homology (r+1)) : ℤ)=
      PowerSeries.coeff (r+1) (QuadraticDual.tensorHilbertSeries f g) := by
    intro r
    have he := HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
      (ExteriorAugmented.grading f g) (ExteriorAugmented.augmentation f g)
      B δ (ExteriorAugmented.grading_zero f g) hunit hhom hpos hε hδ
      (ExteriorAugmented.grading_mul f g) r
    exact (congrArg (fun m : ℕ => (m : ℤ)) he).trans
      (IntrinsicQuadraticDual.degree_finrank_eq_coeff f g (r+1))
  have hseries : 1+WeightedBar.positiveSeries δ=
      KoszulBarObstruction.actualExteriorSeries f g := by
    refine (HomogeneousBasisHilbert.one_add_positiveSeries_eq
      (ExteriorAugmented.grading f g) (ExteriorAugmented.augmentation f g)
      B δ (ExteriorAugmented.grading_zero f g) hunit hhom hpos).trans ?_
    apply PowerSeries.ext
    intro d
    simp only [HomogeneousBasisHilbert.series,KoszulBarObstruction.actualExteriorSeries,
      PowerSeries.coeff_mk]
    exact congrArg (fun m : ℕ => (m : ℤ)) (ExteriorAugmented.grading_piece_finrank f g d)
  apply KoszulBarObstruction.actual_exterior_dual_no_koszul_identity f g hinj
  rw [←hseries]
  exact KoszulDiagonalSeries.one_add_mul_signed_series
    (ExteriorAugmented.augmentation f g) B hunit hε δ hpos hδ
    (QuadraticDual.tensorHilbertSeries f g) (dual_constant f g hinj) hdim hKoszul

/-- The conclusion rules out every actual homogeneous Koszul certificate,
not just the particular basis used in the Hilbert computation. -/
theorem not_certificate (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate f g) := by
  rintro ⟨C⟩
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  exact not_hasDiagonalTor f g hinj C.Index C.basis C.unit C.degree C.positive
    C.homogeneous C.augmentation_zero C.product_degree C.diagonal

end PaperVerification.AlternatingForms.NonKoszul

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K]

/-- All dimensions at least six, one nonempty principal open of the full
space of pairs, and the actual original-graded ordinary-Tor conclusion. -/
theorem paper_proposition_5_3_non_koszul_large (n : ℕ) (hn : 6≤n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  letI : NeZero n := ⟨by omega⟩
  have hdim : Module.finrank K (Fin n → K)=n := by simp
  obtain ⟨ι,fin,h⟩ := generic_cubic_wedge_injective (K := K) (M := Fin n → K) n hn hdim
  letI := fin
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
  exact ⟨ι,fin,b₂,Q,hQ,hpoint,fun y hy => NonKoszul.not_certificate _ _ (h y hy)⟩

end PaperVerification.AlternatingForms
