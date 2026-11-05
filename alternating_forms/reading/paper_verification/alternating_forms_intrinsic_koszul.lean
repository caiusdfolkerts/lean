module

public import PaperVerification.HomogeneousKoszulInvariance
public import PaperVerification.AlternatingFormsExteriorKoszul
public import PaperVerification.AlternatingFormsExteriorHomogeneousBasis

/-!
# Basis-independent Koszulness of the actual exterior quotient

The predicate quantifies over every finite homogeneous augmented basis
compatible with the original grading, and asserts concentration of actual
ordinary augmentation Tor. Basis independence is proved, not assumed.
The independently constructed homogeneous basis shows this quantification
is nonvacuous and proves its equivalence to the constructive certificates
used in the principal generic classification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open ExteriorAugmented AugmentedAlgebraBasis

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Diagonal concentration of ordinary Tor for the original grading,
independently of all choices of compatible finite homogeneous coordinates. -/
def IsKoszul (f g : ⋀[K]^2 M) : Prop :=
  ∀ (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(grading f g).piece (δ i))
    (hε : ∀ i,augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b),
    WeightedBar.HasDiagonalTor (augmentation f g) B hunit hε δ hδ

/-- A single constructive certificate forces concentration for every
compatible homogeneous basis, by a proved ordinary-Tor dimension argument. -/
theorem isKoszul_of_certificate (f g : ⋀[K]^2 M)
    (hC : Nonempty (HomogeneousKoszulCertificate f g)) : IsKoszul f g := by
  obtain ⟨C⟩ := hC
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  intro I inst B hunit δ hpos hhom hε hδ
  exact HomogeneousKoszulInvariance.hasDiagonalTor_transfer
    (augmentation f g) C.basis C.unit C.augmentation_zero C.degree C.product_degree
    (grading f g) (grading_zero f g) C.homogeneous C.positive (grading_mul f g)
    B hunit hε δ hδ hhom hpos C.diagonal

section CoordinateSpace

variable {ν : Type u} [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The actual quotient has an independently constructed finite homogeneous
basis for every pair, including zero-dimensional ambient spaces. -/
def certificateOfIsKoszul (h : IsKoszul f g) : HomogeneousKoszulCertificate f g := by
  letI := ExteriorHomogeneousBasis.positiveFintype f g
  exact {
    Index := ExteriorHomogeneousBasis.PositiveIndex f g
    finite := inferInstance
    basis := ExteriorHomogeneousBasis.basis f g
    degree := ExteriorHomogeneousBasis.positiveDegree f g
    unit := ExteriorHomogeneousBasis.basis_none f g
    positive := ExteriorHomogeneousBasis.positiveDegree_pos f g
    homogeneous := ExteriorHomogeneousBasis.basis_positive_mem f g
    augmentation_zero := ExteriorHomogeneousBasis.basis_positive_augmentation f g
    product_degree := ExteriorHomogeneousBasis.product_homogeneous f g
    diagonal := h (ExteriorHomogeneousBasis.PositiveIndex f g)
      (ExteriorHomogeneousBasis.basis f g) (ExteriorHomogeneousBasis.basis_none f g)
      (ExteriorHomogeneousBasis.positiveDegree f g)
      (ExteriorHomogeneousBasis.positiveDegree_pos f g)
      (ExteriorHomogeneousBasis.basis_positive_mem f g)
      (ExteriorHomogeneousBasis.basis_positive_augmentation f g)
      (ExteriorHomogeneousBasis.product_homogeneous f g) }

/-- Exact equivalence between basis-independent ordinary graded Koszulness
and the constructive certificates, with no normal-form or rank premise. -/
theorem isKoszul_iff_nonempty_certificate :
    IsKoszul f g ↔ Nonempty (HomogeneousKoszulCertificate f g) := by
  constructor
  · intro h
    exact ⟨certificateOfIsKoszul f g h⟩
  · exact isKoszul_of_certificate f g

end CoordinateSpace

end PaperVerification.AlternatingForms.ExteriorKoszul
