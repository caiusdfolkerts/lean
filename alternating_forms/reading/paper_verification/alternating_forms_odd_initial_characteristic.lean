module

public import PaperVerification.AlternatingFormsInitialCharacteristic
public import PaperVerification.AlternatingFormsOddInitialIdeal

/-!
# The exact odd initial ideal with the degree-dependent factorial condition

The full Richardson ideal is proved equal to the actual weight initial
ideal.  No dimension, primality, or extra relation is assumed: the interval
domain and its dimension are supplied by integral standard monomials, and
the opposite dimension inequality comes from the actual isotropic chart.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K]

theorem odd_interval_le_initial_of_degree_factorials
    (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    intervalPluckerIdeal (K := K) (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs) ≤
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  apply sup_le
  · exact matrixPluckerIdeal_le_initial_isotropic _ _
  · apply Ideal.span_le.mpr
    rintro _ ⟨I,hbad,rfl⟩
    obtain ⟨i,hi⟩ := not_forall.mp hbad
    by_cases hl : oddIntervalLower k (t+2) hs i≤I.val i
    · have hr : ¬ I.val i≤oddIntervalUpper k (t+2) hs i :=
        fun h => hi ⟨hl,h⟩
      apply odd_right_variable_mem_initial_of_degree_factorials hfac I
      refine ⟨i,?_⟩
      have hv : 2*(k+1-(t+2)+i.val)<(I.val i).val := lt_of_not_ge hr
      omega
    · apply odd_left_variable_mem_initial_of_degree_factorials hfac I
      exact ⟨i,lt_of_not_ge hl⟩

theorem odd_isotropic_initial_eq_interval_of_degree_factorials
    (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) := by
  letI := intervalPluckerIdeal_isPrime (K := K)
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)
  exact initial_eq_of_prime_candidate _ _ _ ((t+2)*(2*k+2-2*(t+2))+1)
    (odd_interval_le_initial_of_degree_factorials k t hs hfac)
    (oddInterval_krullDim k (t+2) hs (by omega))
    (odd_isotropic_Plucker_cone_dimension_ge k t hs)

/-- The initial-ideal assertion of Theorem 7.1, for every prime, including
two, and every plane dimension at least two in the stated range. -/
theorem paper_theorem_7_1_initial_ideal
    (p k t : ℕ) [Fact p.Prime] [CharP K p]
    (hs : t+2≤k+1) (hp : t+2<2*p) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) :=
  odd_isotropic_initial_eq_interval_of_degree_factorials k t hs
    (degreeFactorials_of_lt_twice_characteristic p (t+2) hp)

end PaperVerification.AlternatingForms
