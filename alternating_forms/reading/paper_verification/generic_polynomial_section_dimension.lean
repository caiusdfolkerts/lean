module

public import PaperVerification.JacobianRelativeDimension
public import PaperVerification.GenericSectionResidueJacobian

/-!
# Expected relative dimension on the actual generic parameter open

The avoidance polynomial is the same one used for generic smoothness. The
result applies to the literal ideal quotient by the original specialized
equations, with no regularity or dimension assumption on that quotient.
-/

@[expose] public section
noncomputable section

universe u

namespace PaperVerification.GenericSectionDifferentials

variable {K ι κ τ : Type u} [Field K] [CharZero K]
  [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The same nonempty principal parameter open gives smooth quotients of the
full expected relative dimension, not merely smooth quotients. -/
theorem linearSection_quotient_locally_standardSmoothOfRelativeDimension
    (v : Matrix κ ι (MvPolynomial τ K))
    (u : Matrix ι κ (MvPolynomial τ K)) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu) ≠ 0) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card τ - Fintype.card κ))
      (algebraMap K (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a)))) := by
  apply JacobianRelativeDimension.locally_standardSmoothOfRelativeDimension
  intro J hJ
  exact linearSection_residue_pderiv_rows v u hvu a ha J

end PaperVerification.GenericSectionDifferentials
