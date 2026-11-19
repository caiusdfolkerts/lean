module

public import PaperVerification.AlternatingFormsOddAffineDimension

/-!
# The coordinate convention in Section 4

In path coordinates `(b₀,a₁,b₁,…,aₖ,bₖ)`, the Section 4 pair `(f,g)` is
`(G,-F)`. The displayed exterior sums and equality of the actual homogeneous
isotropy ideals make this coordinate identification explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The Section 4 forms, written in the interleaved path coordinate order. -/
def sectionFourPluckerForms (k : ℕ) (l : Fin 2) : StrictPairs (2*k+1) → K :=
  if l = 0 then oddPluckerForms k 1 else -oddPluckerForms k 0

theorem twoFormOfCoefficients_neg_form {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (f : StrictPairs n → K) (z : Fin n → M) :
    twoFormOfCoefficients (-f) z = -twoFormOfCoefficients f z := by
  unfold twoFormOfCoefficients
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change (-f a) • exteriorPair (z a.val.1) (z a.val.2) =
    -(f a • exteriorPair (z a.val.1) (z a.val.2))
  exact _root_.neg_smul (f a) (exteriorPair (z a.val.1) (z a.val.2))

private theorem sectionFour_exteriorPair_swap {M : Type*}
    [AddCommGroup M] [Module K M] (u v : M) :
    exteriorPair (K := K) u v = -exteriorPair v u := by
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

/-- The first form is literally `Σ aᵢ ∧ bᵢ`. -/
theorem sectionFour_first_coefficients {M : Type*} [AddCommGroup M] [Module K M]
    (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (sectionFourPluckerForms (K := K) k 0) z =
      ∑ i : Fin k, exteriorPair (z (oddAffineOddVertex k i))
        (z (oddAffineEvenVertex k i.succ)) := by
  rw [sectionFourPluckerForms, if_pos rfl, oddPluckerForms_twoForm]
  rfl

/-- The second form is literally `Σ aᵢ ∧ bᵢ₋₁`. -/
theorem sectionFour_second_coefficients {M : Type*} [AddCommGroup M] [Module K M]
    (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (sectionFourPluckerForms (K := K) k 1) z =
      ∑ i : Fin k, exteriorPair (z (oddAffineOddVertex k i))
        (z (oddAffineEvenVertex k i.castSucc)) := by
  rw [sectionFourPluckerForms, if_neg (by decide : (1 : Fin 2) ≠ 0),
    twoFormOfCoefficients_neg_form, oddPluckerForms_twoForm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sectionFour_exteriorPair_swap _ _).symm

theorem pluckerIsotropyEquation_neg_form {t n : ℕ}
    (f : StrictPairs n → K) (J : Fin t → Fin n) :
    pluckerIsotropyEquation (-f) J = -pluckerIsotropyEquation f J := by
  simp only [pluckerIsotropyEquation, Pi.neg_apply, _root_.neg_smul, Finset.sum_neg_distrib]

private theorem isotropy_equation_mem {t n m : ℕ}
    (forms : Fin m → StrictPairs n → K) (l : Fin m) (J : Fin t → Fin n) :
    pluckerIsotropyEquation (forms l) J ∈ isotropicPluckerIdeal forms :=
by
  apply (show Ideal.span (Set.range fun a : Fin m × (Fin t → Fin n) =>
    pluckerIsotropyEquation (forms a.1) a.2) ≤ isotropicPluckerIdeal forms from
      le_sup_right)
  exact Ideal.subset_span ⟨(l,J), rfl⟩

/-- Changing `(F,G)` to the literal Section 4 pair `(G,-F)` preserves the
actual homogeneous ideal, hence the projective zero scheme with its scheme structure. -/
theorem sectionFour_isotropicPluckerIdeal (k t : ℕ) :
    isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k) =
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  apply le_antisymm
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro q ⟨⟨l,J⟩,rfl⟩
    fin_cases l
    · simpa [sectionFourPluckerForms] using
        isotropy_equation_mem (oddPluckerForms (K := K) k) 1 J
    · simpa [sectionFourPluckerForms, pluckerIsotropyEquation_neg_form] using
        (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)).neg_mem
          (isotropy_equation_mem (oddPluckerForms (K := K) k) 0 J)
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro q ⟨⟨l,J⟩,rfl⟩
    fin_cases l
    · simpa [sectionFourPluckerForms, pluckerIsotropyEquation_neg_form] using
        (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k)).neg_mem
          (isotropy_equation_mem (sectionFourPluckerForms (K := K) k) 1 J)
    · simpa [sectionFourPluckerForms] using
        isotropy_equation_mem (sectionFourPluckerForms (K := K) k) 0 J

end PaperVerification.AlternatingForms
