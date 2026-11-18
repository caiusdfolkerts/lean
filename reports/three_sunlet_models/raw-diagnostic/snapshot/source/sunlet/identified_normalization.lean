module

public import sunlet.group_coordinates
public import sunlet.dimension_upper_bound

/-!
# Gauge normalization with identified parameter classes

A class map need not induce a permutation of the set of classes under
translation. Accordingly the coordinates remain indexed by actual pairs of
group elements throughout this module. The class map is used only on the
five independent parameter families.
-/

@[expose] public section
noncomputable section

namespace Sunlet.Identified

open Normalization

variable {K G C : Type*} [Field K] [AddCommGroup G]
  [Fintype G] [Fintype C] [DecidableEq C]

/-- The actual polynomial map with all five parameter families constant on
the fibers of the specified class map. -/
def coordinatePolynomial (q : G → C) (ab : G × G) :
    MvPolynomial (ParamVar C C) K :=
  MvPolynomial.X (.s (q ab.2)) * MvPolynomial.X (.t (q (ab.1 + ab.2))) *
    (MvPolynomial.X (.u (q ab.1)) * MvPolynomial.X (.h (q (ab.1 + ab.2))) +
      MvPolynomial.X (.v (q ab.1)) * MvPolynomial.X (.h (q ab.2)))

/-- A coordinate-wise auxiliary permutation, used only to reuse the proved
normalization identities. It is not asserted to be an action on the classes. -/
def localPermutation (q : G → C) (ab : G × G) : C → Equiv.Perm C :=
  fun a => if a = q 0 then Equiv.refl C else Equiv.swap (q ab.2) (q (ab.1 + ab.2))

theorem localPermutation_identity (q : G → C) (ab : G × G) :
    localPermutation q ab (q 0) = Equiv.refl C := by simp [localPermutation]

theorem localPermutation_value (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) (ab : G × G) :
    localPermutation q ab (q ab.1) (q ab.2) = q (ab.1 + ab.2) := by
  by_cases ha : ab.1 = 0
  · simp [localPermutation, ha]
  · have hqa : q ab.1 ≠ q 0 := fun h => ha ((hq0 ab.1).mp h)
    simp [localPermutation, hqa]

theorem coordinate_as_local (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) (ab : G × G) :
    coordinatePolynomial (K := K) q ab =
      Sunlet.coordinatePolynomial (localPermutation q ab) (q ab.1, q ab.2) := by
  simp only [coordinatePolynomial, Sunlet.coordinatePolynomial,
    localPermutation_value q hq0]

/-- The normalized map lands in a localization with exactly `5r-4` variables. -/
def normalizedComorphism (q : G → C) :
    MvPolynomial (G × G) K →ₐ[K] LocalizedRing K (q 0) (q 0) :=
  (specialization (K := K) (ι := C) (Ω := C) (e := q 0) (o := q 0)).comp
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) q))

theorem normalizedComorphism_coordinate (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) (ab : G × G) :
    normalizedComorphism (K := K) q (MvPolynomial.X ab) =
      Normalization.coordinate (localPermutation q ab)
        (universalParameters (K := K) (e := q 0) (o := q 0)) (q ab.1) (q ab.2) := by
  simp only [normalizedComorphism, AlgHom.comp_apply, PolynomialImage.comorphism,
    MvPolynomial.aeval_X, coordinate_as_local q hq0]
  exact specialization_coordinate _ (localPermutation_identity q ab) _

theorem normalizing_coordinate (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) (ab : G × G) :
    normalizingHom (specialization (K := K) (e := q 0) (o := q 0)
      (coordinatePolynomial (K := K) q ab)) =
        algebraMap (OriginalRing K C C) (OriginalField K C C)
          (coordinatePolynomial (K := K) q ab) := by
  rw [coordinate_as_local q hq0,
    specialization_coordinate _ (localPermutation_identity q ab)]
  rw [Normalization.parameterMap,
    normalizingHom_coordinate _ (localPermutation_identity q ab)]
  exact generic_coordinate _ _

theorem normalizing_comp (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) :
    (normalizingHom (K := K) (ι := C) (Ω := C) (e := q 0) (o := q 0)).comp
        (normalizedComorphism (K := K) q) =
      (IsScalarTower.toAlgHom K (OriginalRing K C C) (OriginalField K C C)).comp
        (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)) := by
  ext ab
  simp only [normalizedComorphism, AlgHom.comp_apply, PolynomialImage.comorphism,
    MvPolynomial.aeval_X, IsScalarTower.toAlgHom_apply]
  exact normalizing_coordinate q hq0 ab

/-- Identifying parameters preserves the full gauge-normalization argument;
the two maps have exactly the same polynomial identities. -/
theorem definingIdeal_eq_normalizedKernel (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) :
    PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q) =
      RingHom.ker (normalizedComorphism (K := K) q) := by
  apply le_antisymm
  · intro f hf
    change PolynomialImage.comorphism (coordinatePolynomial (K := K) q) f = 0 at hf
    change normalizedComorphism q f = 0
    simp only [normalizedComorphism, AlgHom.comp_apply, hf, map_zero]
  · intro f hf
    change normalizedComorphism (K := K) q f = 0 at hf
    change PolynomialImage.comorphism (coordinatePolynomial (K := K) q) f = 0
    apply IsFractionRing.injective (OriginalRing K C C) (OriginalField K C C)
    rw [map_zero]
    calc
      _ = normalizingHom (normalizedComorphism (K := K) q f) :=
        (AlgHom.congr_fun (normalizing_comp q hq0) f).symm
      _ = 0 := by rw [hf, map_zero]

def coordinateRingEquivNormalizedImage (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) :
    (MvPolynomial (G × G) K ⧸ PolynomialImage.definingIdeal
      (coordinatePolynomial (K := K) q)) ≃ₐ[K]
      (normalizedComorphism (K := K) q).range :=
  (Ideal.quotientEquivAlgOfEq K (definingIdeal_eq_normalizedKernel q hq0)).trans
    (Ideal.quotientKerEquivRange (normalizedComorphism q))

/-- The upper bound in Theorem 7.1, for the actual identified coordinate ring.
It does not assume that translations act on the quotient set of classes. -/
theorem coordinateRing_dimension_le (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ PolynomialImage.definingIdeal
      (coordinatePolynomial (K := K) q)) ≤
      (5 * Fintype.card C - 4 : ℕ) := by
  let A := (normalizedComorphism (K := K) q).range
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (normalizedComorphism (K := K) q).rangeRestrict
    (normalizedComorphism (K := K) q).rangeRestrict_surjective
  rw [ringKrullDim_eq_of_ringEquiv (coordinateRingEquivNormalizedImage q hq0).toRingEquiv]
  change ringKrullDim A ≤ _
  rw [Sunlet.DimensionAlgebra.ringKrullDim_eq_trdeg_toNat K A]
  have hfinite : Algebra.trdeg K (LocalizedRing K (q 0) (q 0)) < Cardinal.aleph0 := by
    rw [localized_trdeg_eq_polynomial, MvPolynomial.trdeg_of_isDomain]
    simp
  have h := Cardinal.toNat_le_toNat
    (lift_trdeg_le_of_injective A.val Subtype.val_injective)
    (by simpa only [Cardinal.lift_lt_aleph0] using hfinite)
  have hn : (Algebra.trdeg K A).toNat ≤
      Fintype.card (Variable C C (q 0) (q 0)) := by
    simpa [localized_trdeg_eq_polynomial, MvPolynomial.trdeg_of_isDomain] using h
  have hnonzero : Fintype.card {a : C // a ≠ q 0} = Fintype.card C - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun a : C => a = q 0)
  have hcard : Fintype.card (Variable C C (q 0) (q 0)) = 5 * Fintype.card C - 4 := by
    rw [variable_card, hnonzero]
    have hc : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨q 0⟩
    omega
  rw [hcard] at hn
  exact_mod_cast hn

theorem imageClosure_dimension_le [Infinite K] (q : G → C)
    (hq0 : ∀ a, q a = q 0 ↔ a = 0) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinatePolynomial (K := K) q))) ≤
      (5 * Fintype.card C - 4 : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  exact coordinateRing_dimension_le q hq0

end Sunlet.Identified
