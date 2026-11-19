module

public import PaperVerification.HomogeneousNullstellensatz
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A common-zero test over an algebraically closed extension

Mathlib's Nullstellensatz is stated for a polynomial ring over any field and
zeros valued in an algebraically closed extension. It therefore puts the origin
ideal inside the radical in the original coefficient ring directly. No change
of polynomial-ring universes, scalar-extension regularity assumption, or
faithful-flatness premise is needed.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial RingTheory.Sequence

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

/-- A common-zero test over an algebraically closed extension yields a global
regular sequence in the original positively graded polynomial ring. -/
theorem homogeneous_parameters_regular_of_common_zero_extension
    [Fintype σ] [IsAlgClosed L]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List (MvPolynomial σ K))
    (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (horigin : ∀ f ∈ rs, constantCoeff f = 0)
    (hzero : ∀ x : σ → L,
      (∀ f ∈ rs, MvPolynomial.eval₂ (algebraMap K L) x f = 0) → x = 0)
    (hlen : rs.length = Fintype.card σ) :
    IsWeaklyRegular (MvPolynomial σ K) rs := by
  apply HomogeneousLocalization.homogeneous_parameters_regular w hw rs
    hhom horigin _ hlen
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := L)]
  intro f hf x hx
  have hx0 : x = 0 := hzero x (fun g hg => by
    simpa only [MvPolynomial.aeval_def] using hx g (Ideal.subset_span hg))
  rw [hx0, MvPolynomial.aeval_zero,
    (HomogeneousLocalization.mem_originIdeal f).mp hf, map_zero]

end PaperVerification.AlternatingForms
