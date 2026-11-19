module

public import PaperVerification.AlternatingFormsOddStandardPieces
public import PaperVerification.AlternatingFormsRichardsonNormalForm
public import PaperVerification.WeightedInitialNormalForm
public import PaperVerification.HomogeneousBasisCoefficients

/-!
# The three genuine bounds on the odd-pencil normal form

The coefficients below are the coordinates in the actual quotient basis.
Their ordinary degree is forced by the inherited quotient grading. Their
first weight is bounded by actual initial-relation lifts; at equality they
are the Richardson coefficients, whose diagonal leading terms supply the
second bound and identify the unique possible meet/join term.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators
open WeightedInitialFiber Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "w" => pluckerVertexWeight (oddNatVertexWeight k)
local notation "B" => oddPluckerStandardBasis (K := K) k t hs
local notation "B₀" => oddInitialStandardBasis (K := K) k t hs

def oddCoefficients (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) :
    OddStandardIndex k t hs →₀ K := (B).repr (Ideal.Quotient.mk Q p)

theorem oddInitialCoefficient_eq_interval
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K)
    (C : OddStandardIndex k t hs) :
    (B₀).repr (Ideal.Quotient.mk _ p) C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) p C := by
  change (intervalStandardBasis α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)).repr
    ((Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval k t hs).symm).symm
      (Ideal.Quotient.mk _ p)) C=_
  rw [Ideal.quotientEquivAlgOfEq_symm,Ideal.quotientEquivAlgOfEq_mk]
  rfl

theorem oddCoefficients_weight_le
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : WeightBound w d p) (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs p C≠0) : oddStandardWeight k t hs C≤d := by
  by_contra h
  exact hc (lifted_coefficient_eq_zero_of_weight_lt Q w
    (oddStandardRepresentative (K := K) k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted (K := K) k t hs) B₀ (oddInitialStandardBasis_apply (K := K) k t hs)
    p d hp C (lt_of_not_ge h))

theorem oddCoefficients_top_eq
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : WeightBound w d p) (C : OddStandardIndex k t hs)
    (hc : oddStandardWeight k t hs C=d) :
    oddCoefficients (K := K) k t hs p C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (weightedHomogeneousComponent w d p) C := by
  exact (lifted_top_coefficient Q w (oddStandardRepresentative (K := K) k t hs)
    (oddStandardWeight k t hs) (oddStandardRepresentative_weighted (K := K) k t hs)
    B₀ (oddInitialStandardBasis_apply (K := K) k t hs) p d hp C hc).trans
      (oddInitialCoefficient_eq_interval (K := K) k t hs _ C)

theorem oddCoefficients_degree_eq
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : p.IsHomogeneous d) (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs p C≠0) : C.1=d := by
  by_contra hne
  apply hc
  apply GradedComponentBasis.repr_eq_zero_of_degree_ne
    (HomogeneousIdealPieces.grading Q (isotropicPluckerIdeal_isHomogeneous _)) B
    (fun C => C.1)
    (fun C => by
      rw [HomogeneousIdealPieces.grading_piece]
      exact oddPluckerStandardBasis_mem_degree (K := K) k t hs C)
    d (Ideal.Quotient.mk Q p) ?_ C hne
  rw [HomogeneousIdealPieces.grading_piece]
  exact ⟨p,hp,rfl⟩

def oddGoodWeight (I : IntervalIndex α β) : ℕ := w I.val

theorem odd_pair_homogeneous (I J : IntervalIndex α β) :
    (X I.val*X J.val : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K).IsWeightedHomogeneous w (oddGoodWeight k t hs I+oddGoodWeight k t hs J) :=
  (isWeightedHomogeneous_X K w I.val).mul (isWeightedHomogeneous_X K w J.val)

theorem odd_pair_coefficients_degree (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) : C.1=2 :=
  oddCoefficients_degree_eq (K := K) k t hs _ 2
    ((isHomogeneous_X K I.val).mul (isHomogeneous_X K J.val)) C hc

theorem odd_pair_coefficients_interval (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hw : oddStandardWeight k t hs C=oddGoodWeight k t hs I+oddGoodWeight k t hs J) :
    oddCoefficients (K := K) k t hs (X I.val*X J.val) C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (X I.val*X J.val) C := by
  have hp := odd_pair_homogeneous (K := K) k t hs I J
  rw [oddCoefficients_top_eq (K := K) k t hs _ _ (fun a ha => (hp ha).le) C hw,
    weightedHomogeneousComponent_eq_self hp]

/-- Every actual straightening coefficient obeys the two filtration
bounds. In the common top of both, its chain is exactly meet/join. -/
theorem odd_pair_coefficients_triangular (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) :
    oddStandardWeight k t hs C<oddGoodWeight k t hs I+oddGoodWeight k t hs J ∨
      (oddStandardWeight k t hs C=oddGoodWeight k t hs I+oddGoodWeight k t hs J ∧
        (standardDiagonalWeight α β C<diagonalWeight α β I+diagonalWeight α β J ∨
          (standardDiagonalWeight α β C=diagonalWeight α β I+diagonalWeight α β J ∧
            C=pairChain α β I J))) := by
  have hp := odd_pair_homogeneous (K := K) k t hs I J
  have hw := oddCoefficients_weight_le (K := K) k t hs _ _ (fun a ha => (hp ha).le) C hc
  rcases hw.lt_or_eq with hw | hw
  · exact Or.inl hw
  · refine Or.inr ⟨hw,?_⟩
    have hc' : intervalCoefficients (K := K) α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (X I.val*X J.val) C≠0 := by
      rwa [←odd_pair_coefficients_interval (K := K) k t hs I J C hw]
    have hd := interval_pair_diagonal_le (K := K) α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) I J C hc'
    rcases hd.lt_or_eq with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨hd,interval_pair_top_chain (K := K) α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) I J C hc' hd⟩

end PaperVerification.AlternatingForms
