module

public import PaperVerification.FoldedComplexHomologyGrading
public import PaperVerification.GradedDifferentialCochainComplex
public import PaperVerification.AlternatingFormsIntegerGrading

/-!
# Hilbert series of genuine folded cohomology

These identities take dimensions only after constructing the degreewise
linear equivalences of actual homology. In particular, the graded quotient
and the ordinary cochain complex are both defined independently of the
Hilbert formulas they satisfy.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.FoldedComplexHomologyHilbert

open AlternatingForms

variable {K : Type u} [Field K]

section Conjugacy

variable {A B : Type v} [AddCommGroup A] [AddCommGroup B]
  [Module K A] [Module K B] [FiniteDimensional K A] [FiniteDimensional K B]
  (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
  (D : A →ₗ[K] A) (E : B →ₗ[K] B)
  (hD : D.comp D = 0) (hE : E.comp E = 0) {δ : ℤ}
  (hd : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece δ)
  (he : TauCeti.LinearMap.IsHomogeneous E H.piece H.piece δ)
  (e : A ≃ₗ[K] B) (hcomm : ∀ x, e (D x) = E (e x))
  (hgrade : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)

include hcomm hgrade in
/-- Homogeneous conjugacy preserves the genuine Hilbert series of the
inherited kernel/image quotient. -/
theorem hilbert_conjugacy :
    finiteHilbertLaurent (SquareZeroHomologyGrading.homologyGrading G D hD hd) =
      finiteHilbertLaurent (SquareZeroHomologyGrading.homologyGrading H E hE he) := by
  ext q
  simp only [finiteHilbertLaurent_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    (SquareZeroHomologyGrading.homogeneousPieceEquiv G D hD hd H E hE he e hcomm hgrade q).finrank_eq

end Conjugacy

section Folded

open FoldedComplexHomologyGrading

variable {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module K A₀] [Module K A₁] [Module K A₂]
  [FiniteDimensional K A₀] [FiniteDimensional K A₁] [FiniteDimensional K A₂]
  (G₀ : TauCeti.InternalGrading K A₀)
  (G₁ : TauCeti.InternalGrading K A₁)
  (G₂ : TauCeti.InternalGrading K A₂)
  (d₁ : A₁ →ₗ[K] A₀) (d₂ : A₂ →ₗ[K] A₁) (h : d₁.comp d₂ = 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)

/-- The full Laurent-polynomial identity for actual folded homology. -/
theorem hilbert_folded :
    finiteHilbertLaurent (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂) =
      finiteHilbertLaurent (zerothGrading G₀ G₁ d₁ hd₁) +
        (LaurentPolynomial.T (-1) *
            finiteHilbertLaurent (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂) +
          LaurentPolynomial.T (-2) *
            finiteHilbertLaurent (secondGrading G₁ G₂ d₂ hd₂)) := by
  ext q
  change (Module.finrank K ((homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece q) : ℤ) =
    (finiteHilbertLaurent (zerothGrading G₀ G₁ d₁ hd₁)).coeff q +
      ((LaurentPolynomial.T (-1) *
          finiteHilbertLaurent (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)).coeff q +
        (LaurentPolynomial.T (-2) *
          finiteHilbertLaurent (secondGrading G₁ G₂ d₂ hd₂)).coeff q)
  simp only [finiteHilbertLaurent_coeff, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_neg]
  rw [finrank_homology_piece]
  simp only [Nat.cast_add]
  rw [add_comm (1 : ℤ) q, add_comm (2 : ℤ) q]

/-- In each integer degree, the actual categorical cochain cohomology has
the sum of the three original homology dimensions, with their exact shifts. -/
theorem finrank_cochain_homology (q : ℤ) :
    Module.finrank K
      ((GradedDifferentialCochainComplex.cochainComplex (totalGrading G₀ G₁ G₂)
        (FoldedComplexHomology.differential d₁ d₂)
        (FoldedComplexHomology.differential_sq d₁ d₂ h)
        (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)).homology q) =
      Module.finrank K ((zerothGrading G₀ G₁ d₁ hd₁).piece q) +
        (Module.finrank K ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (q + 1)) +
          Module.finrank K ((secondGrading G₁ G₂ d₂ hd₂).piece (q + 2))) := by
  rw [(GradedDifferentialCochainComplex.cochainHomologyEquiv
    (totalGrading G₀ G₁ G₂) (FoldedComplexHomology.differential d₁ d₂)
    (FoldedComplexHomology.differential_sq d₁ d₂ h)
    (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂) q).finrank_eq]
  exact finrank_homology_piece G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ q

end Folded

end PaperVerification.FoldedComplexHomologyHilbert
