module

public import PaperVerification.FermionPathBoxes
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The exact paired box count and free rank

The finite path enumeration is identified with the full exterior-support
sum.  The basis-index cardinality is valid over every base ring; the usual
intrinsic module rank is stated over nonzero commutative rings, where rank
is uniquely defined.

Identifying the displayed box
polynomial with the actual exterior grading is a separate step.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Paths Exterior Endpoint
open scoped BigOperators

variable {A R : Type*} [CommSemiring A] [CommRing R] {n : ℕ}

theorem paired_box_sum (r u v : Fin n → ℕ) (s : ℕ)
    (huv : ∀ i,u i+v i=r i*s) (t : A) :
    (∑ W : Finset (OddIndex n), (pairedWordBoxCard r u v s W : A)*t^W.card) =
      ((∏ i,r i : ℕ) : A)*(s.ascFactorial n : A)*(1+t)^n := by
  classical
  have hsplit (i : ℕ) : extendNat u i+extendNat v i=extendNat r i*s := by
    by_cases hi : i<n
    · simpa only [extendNat,dif_pos hi] using huv ⟨i,hi⟩
    · simp only [extendNat,dif_neg hi,zero_add,zero_mul]
  have h := sum_boxes_eq_closed (extendNat r) (extendNat u) (extendNat v) s t hsplit n
  rw [Finset.prod_range] at h
  simp only [extendNat_fin] at h
  rw [← Equiv.sum_comp (marksWordEquiv n)]
  convert h using 1
  apply Finset.sum_congr rfl
  intro m hm
  change (pairedWordBoxCard r u v s (wordOfMarks m) : A) * t ^ (wordOfMarks m).card = _
  simp only [pairedWordBoxCard,boxProduct,wordMark_wordOfMarks,
    extendNat_fin,Nat.cast_ite,Nat.cast_zero,Nat.cast_prod,ite_mul,zero_mul]

theorem card_pairedPowerIndex_closed (r u v : Fin n → ℕ) (s : ℕ)
    (huv : ∀ i,u i+v i=r i*s) :
    Fintype.card (PairedPowerIndex r u v s)=2^n*(∏ i,r i)*s.ascFactorial n := by
  rw [card_pairedPowerIndex]
  have h := paired_box_sum r u v s huv (1 : ℕ)
  simpa only [Nat.cast_id,one_pow,mul_one,one_mul,show (1+1 : ℕ)=2 from rfl,
    mul_assoc,mul_comm,mul_left_comm] using h

instance pairedIndex_fintype (d : PairedData (K := R) (n := n)) : Fintype (PairedIndex d) :=
  Fintype.ofEquiv (PairedPowerIndex d.r d.u d.v d.s) (pairedIndexEquiv d).symm

/-- The cardinality of the literal paper basis, including over the zero
ring where intrinsic free rank is not uniquely determined. -/
theorem card_pairedIndex (d : PairedData (K := R) (n := n)) :
    Fintype.card (PairedIndex d)=2^n*(∏ i,d.r i)*d.s.ascFactorial n := by
  rw [Fintype.card_congr (pairedIndexEquiv d)]
  exact card_pairedPowerIndex_closed d.r d.u d.v d.s d.degree_split

theorem paired_finrank [Nontrivial R] (d : PairedData (K := R) (n := n)) :
    Module.finrank R (PairedQuotient d.beta d.phi d.a d.b)=
      2^n*(∏ i,d.r i)*d.s.ascFactorial n := by
  rw [Module.finrank_eq_card_basis (pairedPaperBasis d),card_pairedIndex]

/-- The total-exterior polynomial enumerating every actual basis index. -/
def pairedBasisExteriorPolynomial (d : PairedData (K := R) (n := n)) : Polynomial ℕ :=
  ∑ W : Finset (OddIndex n), Polynomial.C (pairedWordBoxCard d.r d.u d.v d.s W)*
    Polynomial.X^W.card

theorem pairedBasisExteriorPolynomial_closed (d : PairedData (K := R) (n := n)) :
    pairedBasisExteriorPolynomial d =
      Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n := by
  have h := paired_box_sum d.r d.u d.v d.s d.degree_split (Polynomial.X : Polynomial ℕ)
  have hC (k : ℕ) : Polynomial.C k = (k : Polynomial ℕ) := by
    simpa only [Nat.cast_id] using (Polynomial.C_eq_natCast (R := ℕ) k)
  simpa only [pairedBasisExteriorPolynomial,hC,Nat.cast_mul,mul_assoc] using h

end PaperVerification.Fermion
