module

public import PaperVerification.FermionNewtonCoveredBoxes
public import PaperVerification.FermionCreatorAllDegrees
public import PaperVerification.FermionPairedUpperBound

/-!
# The creator diagonal is exactly the Newton colon multiplier

The word's actual prefix cardinalities determine its signs and heights.
Every diagonal product is identified with a coefficient unit times the
shifted Newton difference product.  This discharges the polynomial input
of the creator separation theorem for all admissible words.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionCreatorPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

def wordMultiplicity (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  (if Sum.inl i ∈ T then 1 else 0) + (if Sum.inr i ∈ T then 1 else 0)

def wordSign (T : Finset (OddIndex n)) (i : Fin n) : ℤ :=
  1 - wordMultiplicity T i

theorem wordSign_cases (T : Finset (OddIndex n)) (i : Fin n) :
    wordSign T i = -1 ∨ wordSign T i = 0 ∨ wordSign T i = 1 := by
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp [wordSign,wordMultiplicity,hθ,hξ]

theorem differenceMultiplicity_wordSign (T : Finset (OddIndex n)) (i : Fin n) :
    differenceMultiplicity (wordSign T) i = wordMultiplicity T i := by
  simp only [differenceMultiplicity,wordSign]
  omega

def wordShift (u v : Fin n → ℕ) (T : Finset (OddIndex n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦
    (if Sum.inl i ∈ T then u i else 0) + (if Sum.inr i ∈ T then v i else 0))

@[simp] theorem wordShift_apply (u v : Fin n → ℕ) (T : Finset (OddIndex n)) (i : Fin n) :
    wordShift u v T i =
      (if Sum.inl i ∈ T then u i else 0) + (if Sum.inr i ∈ T then v i else 0) := rfl

def wordBeta (β : Fin n → F) (T : Finset (OddIndex n)) : F :=
  ∏ i, if Sum.inl i ∈ T then β i else 1

theorem wordBeta_ne_zero (β : Fin n → F) (hβ : ∀ i, β i ≠ 0) (T : Finset (OddIndex n)) :
    wordBeta β T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs
  · exact hβ i
  · exact one_ne_zero

def wordBoxBounds (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  pairedBoxBound (r i) (u i) (v i) s (wordHeight T i) (wordMark T i)

theorem prefix_card_eq_multiplicity_sum (T : Finset (OddIndex n)) (i : ℕ) :
    (T ∩ pairedPrefix n i).card =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i), wordMultiplicity T j := by
  classical
  have h : (T ∩ pairedPrefix n i).card =
      ∑ a : OddIndex n, if a ∈ T ∩ pairedPrefix n i then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext a
    simp
  rw [h,Fintype.sum_sum_type,← Finset.sum_add_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hθ : Sum.inl j ∈ T <;> by_cases hξ : Sum.inr j ∈ T <;>
    by_cases hji : j.val < i <;>
    simp only [Finset.mem_inter,mem_pairedPrefix_inl,mem_pairedPrefix_inr,
      wordMultiplicity,hθ,hξ,hji,and_true,and_false,true_and,false_and,if_true,if_false,
      zero_add]

theorem profileHeight_wordSign (T : Finset (OddIndex n)) (hT : ValidWord T) (s : ℕ) (i : Fin n) :
    profileHeight (fun _ ↦ s) (wordSign T) i = (s + wordHeight T i : ℕ) := by
  have hc := prefix_card_eq_multiplicity_sum T i.val
  have hb := hT i.val i.isLt.le
  have hprefix : (Finset.univ.filter (fun j : Fin n ↦ j < i)).card = i.val := by
    rw [Finset.filter_gt_eq_Iio,Fin.card_Iio]
  have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
      (wordMultiplicity T j : ℤ)) = (T ∩ pairedPrefix n i).card := by
    exact_mod_cast hc.symm
  have hheight : (wordHeight T i.val : ℤ) =
      (i.val : ℤ) - ((T ∩ pairedPrefix n i.val).card : ℤ) := by
    unfold wordHeight
    exact Nat.cast_sub hb
  change (s : ℤ) + (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
    (1 - (wordMultiplicity T j : ℤ))) = ((s + wordHeight T i.val : ℕ) : ℤ)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hprefix, hsum, Nat.cast_add, hheight] <;> ring

theorem heightDegree_wordSign (T : Finset (OddIndex n)) (hT : ValidWord T) (s : ℕ) (i : Fin n) :
    heightDegree (fun _ ↦ s) (wordSign T) i = s + wordHeight T i := by
  have he := profileHeight_wordSign T hT s i
  have hh : 0 ≤ profileHeight (fun _ ↦ s) (wordSign T) i := by rw [he]; positivity
  have hd := heightDegree_cast (fun _ ↦ s) (wordSign T) (wordSign_cases T) i hh
  omega

theorem wordBoxBounds_add_shift (r u v : Fin n → ℕ) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s) (T : Finset (OddIndex n))
    (hT : ValidWord T) (i : Fin n) :
    wordBoxBounds r u v s T i + wordShift u v T i =
      r i * heightDegree (fun _ ↦ s) (wordSign T) i := by
  rw [heightDegree_wordSign T hT s i,wordShift_apply]
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp only [wordBoxBounds,wordMark,hθ,hξ,if_true,if_false,pairedBoxBound]
  all_goals have hh := huv i; nlinarith

theorem covered_differenceProduct_wordSign (r : Fin n → ℕ) (T : Finset (OddIndex n)) :
    powerSubstitution (R := F) r (differenceProduct (wordSign T)) =
      ∏ i : Fin n, (∏ j ∈ Finset.Ioi i, (X i ^ r i - X j ^ r j : PolynomialRing F n)) ^
        wordMultiplicity T i := by
  rw [differenceProduct,map_prod]
  simp only [map_pow,edgeLinear,map_sub,powerSubstitution_X,differenceMultiplicity_wordSign]
  rw [edge_product_eq_double_product
    (fun i j : Fin n ↦ ((X i ^ r i - X j ^ r j : PolynomialRing F n) ^ wordMultiplicity T i))]
  simp only [Finset.prod_pow]

theorem wordShift_monomial (u v : Fin n → ℕ) (T : Finset (OddIndex n)) :
    monomial (wordShift u v T) (1 : F) = ∏ i, X i ^ wordShift u v T i := by
  rw [monomial_eq,(wordShift u v T).prod_fintype _ (fun _ ↦ pow_zero _),map_one,one_mul]

/-- The literal polynomial product of all creator diagonal coefficients. -/
theorem creatorDiagonal_product_polynomial
    (r u v : Fin n → ℕ) (β : Fin n → F) (T : Finset (OddIndex n)) :
    (∏ a ∈ T, prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing F n) ^ r i)
      (fun i ↦ C (β i)) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) a) =
      C (wordBeta β T) * monomial (wordShift u v T) 1 *
        powerSubstitution r (differenceProduct (wordSign T)) := by
  classical
  let D (i : Fin n) : PolynomialRing F n := ∏ j ∈ Finset.Ioi i, (X i ^ r i - X j ^ r j)
  have hstart : (∏ a ∈ T, prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing F n) ^ r i)
      (fun i ↦ C (β i)) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) a) =
      ∏ a : OddIndex n, if a ∈ T then prefixCreatorDiagonal
        (fun i ↦ (X i : PolynomialRing F n) ^ r i) (fun i ↦ C (β i))
        (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) a else 1 := by simp
  rw [hstart,Fintype.prod_sum_type,← Finset.prod_mul_distrib]
  have hrow (i : Fin n) :
      (if Sum.inl i ∈ T then C (β i) * X i ^ u i * D i else 1) *
        (if Sum.inr i ∈ T then X i ^ v i * D i else 1) =
      C (if Sum.inl i ∈ T then β i else 1) * X i ^ wordShift u v T i *
        D i ^ wordMultiplicity T i := by
    by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
      simp only [hθ,hξ,if_true,if_false,wordShift_apply,wordMultiplicity,
        add_zero,zero_add,pow_zero,pow_one,map_one,pow_add,pow_two] <;> ring
  have hreplace := congrArg (fun f : Fin n → PolynomialRing F n ↦ ∏ i, f i) (funext hrow)
  simp only [prefixCreatorDiagonal,Finset.filter_lt_eq_Ioi] at ⊢
  rw [hreplace,Finset.prod_mul_distrib,Finset.prod_mul_distrib,← map_prod,
    ← wordShift_monomial,← covered_differenceProduct_wordSign]
  rfl

theorem creatorDiagonal_map {A : Type*} [CommRing A] [Algebra F A]
    (f : PolynomialRing F n →ₐ[F] A) (φ a c : Fin n → PolynomialRing F n)
    (β : Fin n → F) (j : OddIndex n) :
    f (prefixCreatorDiagonal φ (fun i ↦ C (β i)) a c j) =
      prefixCreatorDiagonal (fun i ↦ f (φ i)) (fun i ↦ algebraMap F A (β i))
        (fun i ↦ f (a i)) (fun i ↦ f (c i)) j := by
  cases j <;> simp only [prefixCreatorDiagonal,map_mul,map_prod,map_sub,specialization_C]

/-- All polynomial diagonal blocks used in triangular creation are
independent in the actual ordinary quotient. -/
theorem paired_creator_diagonal_independent
    (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (T : Finset (OddIndex n)) (hT : ValidWord T) :
    LinearIndependent F (fun a : RectangleIndex (wordBoxBounds r u v s T) ↦
      (Ideal.Quotient.mkₐ F (powerMomentIdeal r β s)) (monomial a.val 1) *
        ∏ j ∈ T, prefixCreatorDiagonal
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ r i))
          (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β s) (β i))
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ u i))
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ v i)) j) := by
  let q := Ideal.Quotient.mkₐ F (powerMomentIdeal r β s)
  have hh (i : Fin n) : 0 < profileHeight (fun _ ↦ s) (wordSign T) i := by
    rw [profileHeight_wordSign T hT s i]
    exact_mod_cast Nat.add_pos_left hs (wordHeight T i)
  have h := shifted_difference_rectangle_independent r hr β s hs (wordSign T)
    (wordSign_cases T) hβ hh (wordShift u v T) (wordBoxBounds r u v s T)
    (fun i ↦ (wordBoxBounds_add_shift r u v s huv T hT i).le)
  have hb := wordBeta_ne_zero β (singleton_weight_ne_zero β hβ) T
  have hscaled := h.units_smul (fun _ ↦ Units.mk0 (wordBeta β T) hb)
  have hprod :
      (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ q (X i ^ r i))
        (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β s) (β i))
        (fun i ↦ q (X i ^ u i)) (fun i ↦ q (X i ^ v i)) j) =
      q (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing F n) ^ r i)
        (fun i ↦ C (β i)) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) j) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact (creatorDiagonal_map q _ _ _ β j).symm
  convert hscaled using 1
  funext a
  simp only [Pi.smul_apply, Pi.smul_apply', Units.smul_def, Units.val_mk0]
  change q (monomial a.val 1) *
      (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ q (X i ^ r i))
        (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β s) (β i))
        (fun i ↦ q (X i ^ u i)) (fun i ↦ q (X i ^ v i)) j) =
      wordBeta β T • q (monomial a.val 1 *
        (monomial (wordShift u v T) 1 * powerSubstitution r (differenceProduct (wordSign T))))
  rw [hprod, creatorDiagonal_product_polynomial]
  have hscalar : q (C (wordBeta β T) * (monomial a.val 1 *
        (monomial (wordShift u v T) 1 * powerSubstitution r (differenceProduct (wordSign T))))) =
      wordBeta β T • q (monomial a.val 1 *
        (monomial (wordShift u v T) 1 * powerSubstitution r (differenceProduct (wordSign T)))) := by
    simpa only [AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul] using
      q.toLinearMap.map_smul (wordBeta β T) (monomial a.val 1 *
        (monomial (wordShift u v T) 1 * powerSubstitution r (differenceProduct (wordSign T))))
  rw [← hscalar, ← map_mul]
  congr 1
  ring

end PaperVerification.Fermion
