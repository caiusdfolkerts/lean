module

public import PaperVerification.FermionCreatorPolynomialBoxes
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The full homogeneous paired basis over the original field

The lower bound comes from the actual Newton colon rectangles and the actual
creator test maps.  The upper bound comes from all-prefix harmonic equations.
Their common index set consists of every admissible exterior word and every
monomial in its literal box; no finite-range reduction is made.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators TensorProduct

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionPairedPowerBasis_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def PairedWordPolynomialIndex (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) :=
  {a : RectangleIndex (wordBoxBounds r u v s T) // ValidWord T}

instance pairedWordPolynomialIndex_fintype
    (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) :
    Fintype (PairedWordPolynomialIndex r u v s T) := by
  classical
  unfold PairedWordPolynomialIndex
  infer_instance

abbrev PairedPowerIndex (r u v : Fin n → ℕ) (s : ℕ) :=
  Sigma (PairedWordPolynomialIndex r u v s)

theorem card_pairedWordPolynomialIndex (r u v : Fin n → ℕ) (s : ℕ)
    (T : Finset (OddIndex n)) :
    Fintype.card (PairedWordPolynomialIndex r u v s T) = pairedWordBoxCard r u v s T := by
  classical
  by_cases hT : ValidWord T
  · let e : PairedWordPolynomialIndex r u v s T ≃ RectangleIndex (wordBoxBounds r u v s T) :=
      { toFun := Subtype.val
        invFun := fun a ↦ ⟨a,hT⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e,card_rectangleIndex]
    simp only [pairedWordBoxCard,if_pos hT,wordBoxBounds]
  · haveI : IsEmpty (PairedWordPolynomialIndex r u v s T) := ⟨fun a ↦ hT a.property⟩
    rw [pairedWordBoxCard,if_neg hT]
    exact Fintype.card_eq_zero (α := PairedWordPolynomialIndex r u v s T)

theorem card_pairedPowerIndex (r u v : Fin n → ℕ) (s : ℕ) :
    Fintype.card (PairedPowerIndex r u v s) =
      ∑ T : Finset (OddIndex n), pairedWordBoxCard r u v s T := by
  rw [Fintype.card_sigma]
  simp only [card_pairedWordPolynomialIndex]

/-- The literal residue classes, with the theta-then-xi exterior order. -/
def pairedPowerClasses (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ)
    (z : PairedPowerIndex r u v s) :
    PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) :=
  (pairedIdeal β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)).ringCon.mkₐ F
    (monomial z.2.val.val 1 ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra z.1)

theorem pairedPowerClasses_linearIndependent
    (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    LinearIndependent F (pairedPowerClasses r u v β s) := by
  classical
  let q := Ideal.Quotient.mkₐ F (powerMomentIdeal r β s)
  apply paired_independent_of_ordinary_diagonal q β
    (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)
    (by
      simpa only [q,Ideal.Quotient.mkₐ_eq_mk,← MvPolynomial.algebraMap_eq,Ideal.Quotient.mk_algebraMap] using
        powerMoment_quotient_all_moments r u v β s huv)
    (PairedWordPolynomialIndex r u v s) (fun T a ↦ monomial a.val.val 1)
  intro T
  by_cases hT : ValidWord T
  · exact (paired_creator_diagonal_independent r u v β s hs hr huv hβ T hT).comp
      (fun a : PairedWordPolynomialIndex r u v s T ↦ a.val) Subtype.val_injective
  · haveI : IsEmpty (PairedWordPolynomialIndex r u v s T) := ⟨fun a ↦ hT a.property⟩
    exact linearIndependent_empty_type

/-- The matching lower and upper bounds for the original homogeneous quotient. -/
theorem pairedPower_finrank_eq_card
    (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : F)) :
    Module.finrank F
      (PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)) =
      Fintype.card (PairedPowerIndex r u v s) := by
  letI := pairedPower_quotient_finite r u v β s huv hβ
  apply le_antisymm
  · rw [card_pairedPowerIndex]
    exact pairedPower_quotient_finrank_le_box_count r u v β s hs hr huv hβ hfac
  · exact (pairedPowerClasses_linearIndependent r u v β s hs hr huv hβ).fintype_card_le_finrank

/-- Every homogeneous monomial claimed by Theorem 1.1 is a member of this
basis of the actual paired quotient. No independence or dimension hypothesis
is passed to the endpoint. -/
def pairedPowerBasis
    (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : F)) :
    Module.Basis (PairedPowerIndex r u v s) F
      (PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)) := by
  letI := pairedPower_quotient_finite r u v β s huv hβ
  exact basisOfLinearIndependentOfCardEqFinrank' (pairedPowerClasses r u v β s)
    (pairedPowerClasses_linearIndependent r u v β s hs hr huv hβ)
    (pairedPower_finrank_eq_card r u v β s hs hr huv hβ hfac).symm

@[simp] theorem pairedPowerBasis_apply
    (r u v : Fin n → ℕ) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : F)) (z : PairedPowerIndex r u v s) :
    pairedPowerBasis r u v β s hs hr huv hβ hfac z = pairedPowerClasses r u v β s z := by
  letI := pairedPower_quotient_finite r u v β s huv hβ
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) z

end PaperVerification.Fermion
