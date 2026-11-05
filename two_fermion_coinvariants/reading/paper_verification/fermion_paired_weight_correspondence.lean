module

public import PaperVerification.FermionPairedAssociatedGraded
public import Mathlib.Tactic.FieldSimp

/-!
# Exact correspondence with the paper's rational weights

Multiplying all weights by the positive covering product gives the integer
filtration used in the associated-graded construction. The actual monomial
inequalities and homogeneous degree conditions are proved equivalent.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Exterior

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedWeightCorrespondence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def pairedRationalOddWeight (d : PairedData (K := R) (n := n)) : OddIndex n → ℚ
  | .inl i => (d.u i : ℚ)/d.r i
  | .inr i => (d.v i : ℚ)/d.r i

def pairedRationalSuperWeight (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n) : ℚ :=
  monomialWeight d.r z.1+∑ j ∈ z.2,pairedRationalOddWeight d j

theorem pairedRationalOddWeight_mul_product (d : PairedData (K := R) (n := n))
    (j : OddIndex n) :
    pairedRationalOddWeight d j*(∏ i,d.r i : ℕ)=(pairedOddWeight d j : ℚ) := by
  cases j with
  | inl i =>
      have hr : (d.r i : ℚ) ≠ 0 := by exact_mod_cast (d.positive_r i).ne'
      rw [show (∏ j,d.r j : ℕ)=d.r i*coveringWeight d.r i from (coveringWeight_mul d.r i).symm]
      simp only [pairedRationalOddWeight,pairedOddWeight,Nat.cast_mul]
      field_simp
  | inr i =>
      have hr : (d.r i : ℚ) ≠ 0 := by exact_mod_cast (d.positive_r i).ne'
      rw [show (∏ j,d.r j : ℕ)=d.r i*coveringWeight d.r i from (coveringWeight_mul d.r i).symm]
      simp only [pairedRationalOddWeight,pairedOddWeight,Nat.cast_mul]
      field_simp

theorem pairedRationalSuperWeight_mul_product (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n) :
    pairedRationalSuperWeight d z*(∏ i,d.r i : ℕ)=(pairedSuperWeight d z : ℚ) := by
  rw [pairedRationalSuperWeight,add_mul,monomialWeight_mul_coveringProduct d.r d.positive_r,
    Finset.sum_mul]
  simp only [pairedRationalOddWeight_mul_product,pairedSuperWeight,superMonomialWeight,
    wordPolynomialWeight,Nat.cast_add,Nat.cast_sum]

theorem pairedSuperWeight_le_iff (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n) (k : ℕ) :
    pairedSuperWeight d z ≤ k ↔
      pairedRationalSuperWeight d z ≤ (k : ℚ)/(∏ i,d.r i : ℕ) := by
  have hp : (0 : ℚ)<(∏ i,d.r i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ ↦ d.positive_r i)
  rw [le_div_iff₀ hp,pairedRationalSuperWeight_mul_product]
  norm_cast

theorem pairedSuperWeight_eq_iff (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n) (k : ℕ) :
    pairedSuperWeight d z=k ↔
      pairedRationalSuperWeight d z=(k : ℚ)/(∏ i,d.r i : ℕ) := by
  have hp : (∏ i,d.r i : ℕ) ≠ (0 : ℚ) := by
    exact_mod_cast (Finset.prod_pos (fun i _ ↦ d.positive_r i)).ne'
  rw [eq_div_iff hp,pairedRationalSuperWeight_mul_product]
  norm_cast

/-- Equality of the actual coefficient-wise filtration conditions, not only
of an assigned degree on the proposed quotient basis. -/
theorem paired_bound_iff_rational (d : PairedData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n) :
    BasisFiltered.Bound (superMonomialBasis (K := R)) (pairedSuperWeight d) k x ↔
      ∀ z,(superMonomialBasis (K := R)).repr x z ≠ 0 →
        pairedRationalSuperWeight d z ≤ (k : ℚ)/(∏ i,d.r i : ℕ) := by
  simp only [BasisFiltered.Bound,pairedSuperWeight_le_iff]

theorem paired_homogeneous_iff_rational (d : PairedData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (pairedSuperWeight d) k x ↔
      ∀ z,(superMonomialBasis (K := R)).repr x z ≠ 0 →
        pairedRationalSuperWeight d z=(k : ℚ)/(∏ i,d.r i : ℕ) := by
  simp only [BasisFiltered.Homogeneous,pairedSuperWeight_eq_iff]

end PaperVerification.Fermion
