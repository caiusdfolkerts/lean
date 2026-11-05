module

public import PaperVerification.FermionStrictCreatorIndependence
public import PaperVerification.FermionCreatorPolynomialBoxes
public import PaperVerification.FermionStrictExtension

/-!
# The strict creator diagonal and its exact Newton rectangle

The strict side length at an arrival is r_i*c_i. Both creator colors
contribute r_i, so its exponent shift plus the side length is exactly the
enlarged constant-one Newton side length. Thus the existing complete colon
rectangle applies directly, with no new endpoint or colength assumption.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators

variable {n : ℕ}

local instance FermionStrictPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

def strictWordBoxBounds (r : Fin n → ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  r i*wordHeight T (i.val+1)

def StrictWordPolynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n)) :=
  {a : RectangleIndex (strictWordBoxBounds r T) // ValidWord T}

instance strictWordPolynomialIndex_fintype (r : Fin n → ℕ) (T : Finset (OddIndex n)) :
    Fintype (StrictWordPolynomialIndex r T) := by
  classical
  unfold StrictWordPolynomialIndex
  infer_instance

abbrev StrictPowerIndex (r : Fin n → ℕ) := Sigma (StrictWordPolynomialIndex r)

def StrictWord (T : Finset (OddIndex n)) : Prop :=
  ∀ j,0<j → j≤n → (T ∩ pairedPrefix n j).card<j

theorem StrictWord.valid {T : Finset (OddIndex n)} (hT : StrictWord T) : ValidWord T := by
  intro j hj
  cases j with
  | zero => simp [pairedPrefix]
  | succ j => exact (hT (j+1) (Nat.succ_pos _) hj).le

theorem strictWord_of_polynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n))
    (a : StrictWordPolynomialIndex r T) : StrictWord T := by
  intro j hj hjn
  let i : Fin n := ⟨j-1,by omega⟩
  have hi := a.val.property i
  have hh : 0<wordHeight T j := by
    have he : i.val+1=j := by dsimp only [i]; omega
    rw [strictWordBoxBounds,he] at hi
    by_contra hz
    have hz' : wordHeight T j=0 := by omega
    rw [hz',mul_zero] at hi
    exact Nat.not_lt_zero _ hi
  change 0<j-(T ∩ pairedPrefix n j).card at hh
  omega

theorem strictWordBounds_add_shift (r : Fin n → ℕ)
    (T : Finset (OddIndex n)) (hT : ValidWord T) (i : Fin n) :
    strictWordBoxBounds r T i+wordShift r r T i =
      r i*heightDegree (fun _ ↦ 1) (wordSign T) i := by
  have hs := wordHeight_steps T hT i.val i.isLt
  rw [heightDegree_wordSign T hT 1 i,strictWordBoxBounds,wordShift_apply]
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp only [wordMark,hθ,hξ,if_true,if_false,HeightStep] at hs ⊢ <;> nlinarith

variable {F : Type*} [Field F]

/-- The strict diagonal multiplies precisely into the proved enlarged
Newton rectangle. Every positive covering degree and every admissible word
is retained. Zero-bound words have an empty rectangle automatically. -/
theorem strict_creator_diagonal_independent
    (r : Fin n → ℕ) (β : Fin n → F) (hr : ∀ i,0<r i)
    (hβ : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i ∈ U,β i))
    (T : Finset (OddIndex n)) (hT : ValidWord T) :
    LinearIndependent F (fun a : RectangleIndex (strictWordBoxBounds r T) ↦
      (Ideal.Quotient.mkₐ F (powerMomentIdeal r β 1)) (monomial a.val 1)*
        ∏ j ∈ T,prefixCreatorDiagonal
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β 1) (X i^r i))
          (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β 1) (β i))
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β 1) (X i^r i))
          (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β 1) (X i^r i)) j) := by
  let q := Ideal.Quotient.mkₐ F (powerMomentIdeal r β 1)
  have hh (i : Fin n) : 0<profileHeight (fun _ ↦ 1) (wordSign T) i := by
    rw [profileHeight_wordSign T hT 1 i]
    exact_mod_cast (by omega : 0<1+wordHeight T i)
  have h := shifted_difference_rectangle_independent r hr β 1 Nat.zero_lt_one
    (wordSign T) (wordSign_cases T) hβ hh (wordShift r r T) (strictWordBoxBounds r T)
    (fun i ↦ (strictWordBounds_add_shift r T hT i).le)
  have hb := wordBeta_ne_zero β (singleton_weight_ne_zero β hβ) T
  have hscaled := h.units_smul (fun _ ↦ Units.mk0 (wordBeta β T) hb)
  have hprod :
      (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ q (X i ^ r i))
        (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β 1) (β i))
        (fun i ↦ q (X i ^ r i)) (fun i ↦ q (X i ^ r i)) j) =
      q (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing F n) ^ r i)
        (fun i ↦ C (β i)) (fun i ↦ X i ^ r i) (fun i ↦ X i ^ r i) j) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact (creatorDiagonal_map q _ _ _ β j).symm
  convert hscaled using 1
  funext a
  simp only [Pi.smul_apply,Pi.smul_apply',Units.smul_def,Units.val_mk0]
  change q (monomial a.val 1) *
      (∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ q (X i ^ r i))
        (fun i ↦ algebraMap F (PolynomialRing F n ⧸ powerMomentIdeal r β 1) (β i))
        (fun i ↦ q (X i ^ r i)) (fun i ↦ q (X i ^ r i)) j) =
      wordBeta β T • q (monomial a.val 1 *
        (monomial (wordShift r r T) 1 * powerSubstitution r (differenceProduct (wordSign T))))
  rw [hprod,creatorDiagonal_product_polynomial]
  have hscalar : q (C (wordBeta β T) * (monomial a.val 1 *
        (monomial (wordShift r r T) 1 * powerSubstitution r (differenceProduct (wordSign T))))) =
      wordBeta β T • q (monomial a.val 1 *
        (monomial (wordShift r r T) 1 * powerSubstitution r (differenceProduct (wordSign T)))) := by
    simpa only [AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul] using
      q.toLinearMap.map_smul (wordBeta β T) (monomial a.val 1 *
        (monomial (wordShift r r T) 1 * powerSubstitution r (differenceProduct (wordSign T))))
  rw [← hscalar, ← map_mul]
  congr 1
  ring

end PaperVerification.Fermion
