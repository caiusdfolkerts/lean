module

public import PaperVerification.AlternatingFormsBooleanWeighted
public import PaperVerification.AlternatingFormsBooleanCoefficients
public import PaperVerification.AlternatingFormsBooleanQuotient
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial relations with monomial constant term

The local inverse may use negative parameter powers.  After multiplication
by the full linear form, every correction exponent is positive.  This file
constructs the resulting polynomial relation explicitly and proves its
specialization identity in every commutative square-zero algebra.  The
constant term is the original monomial, not a separately defined normal form.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanPolynomialRelations

open scoped BigOperators
open MvPolynomial

variable {K L A ι : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
  [CommRing A] [Algebra L A] [Fintype ι] [DecidableEq ι]

theorem map_inverseCoefficient (φ : K →+* L) (h j : ℕ) :
    φ (inverseCoefficient (K := K) h j) = inverseCoefficient (K := L) h j := by
  simp [inverseCoefficient]

def cost (w : ι → ℕ) (J : Finset ι) (T : Finset J) : ℕ :=
  ∑ i ∈ T, w i.val

def correctionExponent (w : ι → ℕ) (J : Finset ι)
    (P T : Finset J) (j : ι) : ℕ := w j + cost w J T - cost w J P

def normalizedRelation (w : ι → ℕ) (J : Finset ι) (h : ℕ)
    (P : FixedSubsets J (h+1)) (tail : Finset ι) :
    MvPolynomial ι (Polynomial K) :=
  ((∏ i ∈ P.val, X i.val) * ∏ i ∈ tail, X i) +
    ∑ j : {i : ι // i ∉ J}, ∑ T : FixedSubsets J h,
      C (Polynomial.C (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
        Polynomial.X ^ correctionExponent w J P.val T.val j.val) *
          (X j.val * ∏ i ∈ T.val, X i.val) * ∏ i ∈ tail, X i

/-- Strict positivity is sufficient for the literal constant-coefficient
specialization to retain only the desired original monomial. -/
theorem normalizedRelation_at_zero (w : ι → ℕ) (J : Finset ι) (h : ℕ)
    (P : FixedSubsets J (h+1)) (tail : Finset ι)
    (hpos : ∀ j : {i : ι // i ∉ J}, ∀ T : FixedSubsets J h,
      0 < correctionExponent w J P.val T.val j.val) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K))
        (normalizedRelation w J h P tail) =
      ((∏ i ∈ P.val, (X i.val : MvPolynomial ι K)) * ∏ i ∈ tail, X i) := by
  unfold normalizedRelation
  simp only [map_add, map_mul, map_sum, map_prod, MvPolynomial.map_X,
    MvPolynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hz (j : {i : ι // i ∉ J}) (T : FixedSubsets J h) :
      (0 : K)^correctionExponent w J P.val T.val j.val = 0 :=
    zero_pow (ne_of_gt (hpos j T))
  simp only [hz, mul_zero, map_zero, zero_mul, Finset.sum_const_zero, add_zero]

theorem power_div_normalize (t : L) (ht : t ≠ 0) (a b : ℕ) (hab : b ≤ a) :
    t^a / t^b = t^(a-b) := by
  apply (div_eq_iff (pow_ne_zero _ ht)).mpr
  rw [← pow_add, Nat.sub_add_cancel hab]

theorem scalar_normalize (φ : K →+* L) (t : L) (ht : t ≠ 0)
    (w : ι → ℕ) (J : Finset ι) (h : ℕ)
    (P : FixedSubsets J (h+1)) (T : FixedSubsets J h) (j : ι)
    (hle : cost w J P.val ≤ w j + cost w J T.val) :
    φ (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
        t^correctionExponent w J P.val T.val j =
      t^(w j) * (inverseCoefficient (K := L) h (T.val ∩ P.val).card *
        (subsetWeight (fun i : J ↦ t^(w i.val)) T.val /
          subsetWeight (fun i : J ↦ t^(w i.val)) P.val)) := by
  rw [map_inverseCoefficient]
  simp only [subsetWeight, Finset.prod_pow_eq_pow_sum]
  change inverseCoefficient (K := L) h (T.val ∩ P.val).card *
      t^(w j + cost w J T.val - cost w J P.val) =
    t^(w j) * (inverseCoefficient (K := L) h (T.val ∩ P.val).card *
      (t^(cost w J T.val) / t^(cost w J P.val)))
  rw [← power_div_normalize t ht _ _ hle, pow_add]
  ring

/-- Evaluation of the displayed polynomial expression after removing its
parameter denominator.  The right-hand side is a multiple of the original
full linear form; local relations have not been substituted for that form. -/
theorem normalized_relation_identity (φ : K →+* L) (t : L) (ht : t ≠ 0)
    (w : ι → ℕ) (J : Finset ι) (h : ℕ) (hJ : J.card = 2*h+1)
    (P : FixedSubsets J (h+1)) (y : ι → A) (hy : ∀ i, y i*y i=0) (tail : A)
    (hle : ∀ j : {i : ι // i ∉ J}, ∀ T : FixedSubsets J h,
      cost w J P.val ≤ w j.val + cost w J T.val) :
    (∏ i ∈ P.val, y i.val) * tail +
        (∑ j : {i : ι // i ∉ J}, ∑ T : FixedSubsets J h,
          (φ (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
            t^correctionExponent w J P.val T.val j.val) •
              (y j.val * ∏ i ∈ T.val, y i.val)) * tail =
      (∑ i, t^(w i) • y i) *
        ((∑ T : FixedSubsets J h,
          (inverseCoefficient (K := L) h (T.val ∩ P.val).card *
            (subsetWeight (fun i : J ↦ t^(w i.val)) T.val /
              subsetWeight (fun i : J ↦ t^(w i.val)) P.val)) •
                ∏ i ∈ T.val, y i.val) * tail) := by
  let η : A := ∑ T : FixedSubsets J h,
    (inverseCoefficient (K := L) h (T.val ∩ P.val).card *
      (subsetWeight (fun i : J ↦ t^(w i.val)) T.val /
        subsetWeight (fun i : J ↦ t^(w i.val)) P.val)) •
          ∏ i ∈ T.val, y i.val
  have hlocal : (∑ i : J, t^(w i.val) • y i.val) * η =
      ∏ i ∈ P.val, y i.val := by
    apply weighted_local_pair_division
    · exact fun i ↦ pow_ne_zero _ ht
    · exact fun i ↦ hy i.val
    · simpa only [Fintype.card_coe] using hJ
  have hsplit : (∑ i, t^(w i) • y i) =
      (∑ i : J, t^(w i.val) • y i.val) +
        ∑ j : {i : ι // i ∉ J}, t^(w j.val) • y j.val := by
    have hJsum : (∑ i ∈ J, t^(w i) • y i) =
        ∑ i : J, t^(w i.val) • y i.val :=
      Finset.sum_subtype J (fun i ↦ Iff.rfl) (fun i ↦ t^(w i) • y i)
    have hCsum : (∑ i ∈ Jᶜ, t^(w i) • y i) =
        ∑ i : {i : ι // i ∉ J}, t^(w i.val) • y i.val :=
      Finset.sum_subtype Jᶜ (fun i ↦ by simp) (fun i ↦ t^(w i) • y i)
    rw [← hJsum, ← hCsum]
    exact (Finset.sum_add_sum_compl J (fun i ↦ t^(w i) • y i)).symm
  have hcorrection :
      (∑ j : {i : ι // i ∉ J}, ∑ T : FixedSubsets J h,
        (φ (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
          t^correctionExponent w J P.val T.val j.val) •
            (y j.val * ∏ i ∈ T.val, y i.val)) =
        (∑ j : {i : ι // i ∉ J}, t^(w j.val) • y j.val) * η := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [η]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [scalar_normalize φ t ht w J h P T j.val (hle j T)]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1 <;> ring
  change _ = (∑ i, t^(w i) • y i) * (η * tail)
  rw [hsplit, ← mul_assoc, add_mul, hlocal, hcorrection, add_mul]

/-- Ordinary coefficient specialization, before passing to an ideal quotient. -/
theorem normalizedRelation_specialize (φ : K →+* L) (t : L)
    (w : ι → ℕ) (J : Finset ι) (h : ℕ)
    (P : FixedSubsets J (h+1)) (tail : Finset ι) :
    MvPolynomial.map (Polynomial.eval₂RingHom φ t)
        (normalizedRelation w J h P tail) =
      ((∏ i ∈ P.val, (X i.val : MvPolynomial ι L)) * ∏ i ∈ tail, X i) +
        (∑ j : {i : ι // i ∉ J}, ∑ T : FixedSubsets J h,
          (φ (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
            t^correctionExponent w J P.val T.val j.val) •
              (X j.val * ∏ i ∈ T.val, X i.val)) * ∏ i ∈ tail, X i := by
  simp only [normalizedRelation, map_add, map_mul, map_sum, map_prod,
    MvPolynomial.map_X, MvPolynomial.map_C, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Finset.sum_mul, MvPolynomial.smul_eq_C_mul]

/-- The specialized polynomial lies in the actual ideal generated by the
coordinate squares and the two original linear forms.  The second form is
arbitrary: a lower-wall relation uses the first form alone. -/
theorem normalizedRelation_mem_quotientIdeal (φ : K →+* L) (t : L) (ht : t ≠ 0)
    (w : ι → ℕ) (J : Finset ι) (h : ℕ) (hJ : J.card = 2*h+1)
    (P : FixedSubsets J (h+1)) (tail : Finset ι) (c : ι → L)
    (hle : ∀ j : {i : ι // i ∉ J}, ∀ T : FixedSubsets J h,
      cost w J P.val ≤ w j.val + cost w J T.val) :
    MvPolynomial.map (Polynomial.eval₂RingHom φ t)
        (normalizedRelation w J h P tail) ∈
      BooleanQuotient.quotientIdeal (fun i ↦ t^(w i)) c := by
  let I := BooleanQuotient.quotientIdeal (fun i ↦ t^(w i)) c
  let π := Ideal.Quotient.mkₐ L I
  let y (i : ι) : MvPolynomial ι L ⧸ I := π (X i)
  have hy (i : ι) : y i * y i = 0 := by
    change π (X i) * π (X i) = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show BooleanQuotient.squareIdeal (K := L) (ι := ι) ≤ I from le_sup_left)
    rw [← pow_two]
    exact coordinatePowerIdeal_generator (R := L) (fun _ : ι ↦ 2) i
  have hlinear : (∑ i, t^(w i) • y i) = 0 := by
    have hspan : Ideal.span
        ({BooleanQuotient.linearForm (fun i ↦ t^(w i)),
          BooleanQuotient.linearForm c} : Set (MvPolynomial ι L)) ≤ I := le_sup_right
    have hmem : BooleanQuotient.linearForm (fun i ↦ t^(w i)) ∈ I :=
      hspan (Ideal.subset_span (by simp))
    have hz : π (BooleanQuotient.linearForm (fun i ↦ t^(w i))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [BooleanQuotient.linearForm, map_sum, map_smul, y] using hz
  have hid := normalized_relation_identity φ t ht w J h hJ P y hy
    (∏ i ∈ tail, y i) hle
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (MvPolynomial.map (Polynomial.eval₂RingHom φ t)
    (normalizedRelation w J h P tail)) = 0
  rw [normalizedRelation_specialize]
  simp only [map_add, map_mul, map_sum, map_prod, map_smul]
  change (∏ i ∈ P.val, y i.val) * (∏ i ∈ tail, y i) +
    (∑ j : {i : ι // i ∉ J}, ∑ T : FixedSubsets J h,
      (φ (inverseCoefficient (K := K) h (T.val ∩ P.val).card) *
        t^correctionExponent w J P.val T.val j.val) •
          (y j.val * ∏ i ∈ T.val, y i.val)) * (∏ i ∈ tail, y i) = 0
  rw [hid, hlinear, zero_mul]

theorem normalizedRelation_coefficients_mem_relations
    (φ : K →+* L) (t : L) (ht : t ≠ 0)
    (w : ι → ℕ) (J : Finset ι) (h : ℕ) (hJ : J.card = 2*h+1)
    (P : FixedSubsets J (h+1)) (tail : Finset ι) (c : ι → L) (q : ℕ)
    (hle : ∀ j : {i : ι // i ∉ J}, ∀ T : FixedSubsets J h,
      cost w J P.val ≤ w j.val + cost w J T.val) :
    BooleanQuotient.coefficients q
        (MvPolynomial.map (Polynomial.eval₂RingHom φ t)
          (normalizedRelation w J h P tail)) ∈
      BooleanQuotient.relations (fun i ↦ t^(w i)) c q :=
  BooleanQuotient.coefficients_mem_relations_of_mem_quotientIdeal _ _ _
    (normalizedRelation_mem_quotientIdeal φ t ht w J h hJ P tail c hle)

end PaperVerification.AlternatingForms.BooleanPolynomialRelations
