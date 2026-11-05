module

public import sunlet.normalized_algebra
public import sunlet.dimension_algebra
public import Lean.Elab.Tactic.Omega

/-!
# The dimension upper bound after exact gauge normalization

The coordinate-ring comparison is proved in `NormalizedAlgebra`.  Here its
normalized image embeds into a localization of a polynomial ring with exactly
`3m + 2c - 2` variables.  The Krull bound follows from the finite-type-domain
dimension theorem, not from a redefinition of dimension.
-/

@[expose] public section
noncomputable section

namespace Sunlet.Normalization

variable {K ι Ω : Type*} [Field K] [DecidableEq ι] [DecidableEq Ω]
  [Fintype Ω] {e : ι} {o : Ω}

theorem denominator_ne_zero : denominator K e o ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)

instance localizedRing_isDomain : IsDomain (LocalizedRing K e o) :=
  IsLocalization.Away.isDomain (LocalizedRing K e o)
    (denominator_ne_zero (K := K) (e := e) (o := o))

instance localizedRing_faithfulSMul :
    FaithfulSMul (PolynomialRing K e o) (LocalizedRing K e o) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsLocalization.injective (LocalizedRing K e o)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (denominator_ne_zero (K := K) (e := e) (o := o))))

theorem localized_trdeg_eq_polynomial :
    Algebra.trdeg K (LocalizedRing K e o) = Algebra.trdeg K (PolynomialRing K e o) := by
  haveI : Algebra.IsAlgebraic (PolynomialRing K e o) (LocalizedRing K e o) :=
    IsLocalization.isAlgebraic (LocalizedRing K e o) (Submonoid.powers (denominator K e o))
  simpa only [trdeg_eq_zero, add_zero] using
    (trdeg_add_eq K (PolynomialRing K e o) (A := LocalizedRing K e o)).symm


variable [Fintype ι]

theorem variable_card :
    Fintype.card (Variable ι Ω e o) =
      3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 := by
  rw [Fintype.card_congr (variableEquivSum (e := e) (o := o))]
  simp only [Fintype.card_sum]
  have hnonbase : Fintype.card {b : Ω // b ≠ o} = Fintype.card Ω - 1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun b : Ω => b = o)
  have hpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨o⟩
  omega

theorem normalizedImage_dimension_le_variable_card (π : ι → Equiv.Perm Ω) :
    ringKrullDim (normalizedComorphism (K := K) (e := e) (o := o) π).range ≤
      (Fintype.card (Variable ι Ω e o) : ℕ) := by
  let A := (normalizedComorphism (K := K) (e := e) (o := o) π).range
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (normalizedComorphism (K := K) (e := e) (o := o) π).rangeRestrict
    (normalizedComorphism (K := K) (e := e) (o := o) π).rangeRestrict_surjective
  rw [Sunlet.DimensionAlgebra.ringKrullDim_eq_trdeg_toNat K A]
  have hfinite : Algebra.trdeg K (LocalizedRing K e o) < Cardinal.aleph0 := by
    rw [localized_trdeg_eq_polynomial, MvPolynomial.trdeg_of_isDomain]
    simp
  have h := Cardinal.toNat_le_toNat
    (lift_trdeg_le_of_injective A.val Subtype.val_injective)
    (by simpa only [Cardinal.lift_lt_aleph0] using hfinite)
  have hn : (Algebra.trdeg K A).toNat ≤ Fintype.card (Variable ι Ω e o) := by
    simpa [localized_trdeg_eq_polynomial, MvPolynomial.trdeg_of_isDomain] using h
  exact_mod_cast hn

include o in
/-- The full coordinate algebra of any permutation family with an identity
color satisfies the exact upper bound from the paper. -/
theorem coordinateRing_dimension_le (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π)) ≤
        (3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv
    (coordinateRingEquivNormalizedImage (K := K) (o := o) π he).toRingEquiv]
  simpa only [variable_card] using
    normalizedImage_dimension_le_variable_card (K := K) (e := e) (o := o) π

include o in
theorem imageClosure_dimension_le [Infinite K] (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (Sunlet.imageClosure (K := K) π)) ≤
        (3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 : ℕ) := by
  rw [Sunlet.imageClosure, PolynomialImage.vanishingIdeal_imageClosure]
  exact coordinateRing_dimension_le (o := o) π he

end Sunlet.Normalization
