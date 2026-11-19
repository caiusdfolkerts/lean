module

public import PaperVerification.AlternatingFormsReflectedInitial
public import PaperVerification.AlternatingFormsIntervalDimension
public import PaperVerification.WeightedInitialComparison

/-!
# The exact weight initial ideal of the canonical odd isotropy locus

Both forbidden-coordinate families and the entire generic-minor kernel are
contained in the actual weight initial ideal.  The interval quotient is an
affine domain of the exact expected dimension.  The literal isotropic chart
gives the opposite dimension bound, so strict dimension drop rules out any
additional initial relation.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k s t : ℕ}

def oddIntervalLower (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*i.val,by have := i.isLt; omega⟩

def oddIntervalUpper (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*(k+1-s+i.val),by have := i.isLt; omega⟩

theorem oddIntervalLower_strictMono (k s : ℕ) (hs : s≤k+1) :
    StrictMono (oddIntervalLower k s hs) := by
  intro i j hij
  change 2*i.val<2*j.val
  omega

theorem oddIntervalUpper_strictMono (k s : ℕ) (hs : s≤k+1) :
    StrictMono (oddIntervalUpper k s hs) := by
  intro i j hij
  change 2*(k+1-s+i.val)<2*(k+1-s+j.val)
  omega

theorem oddIntervalLower_le_upper (k s : ℕ) (hs : s≤k+1) (i : Fin s) :
    oddIntervalLower k s hs i≤oddIntervalUpper k s hs i := by
  change 2*i.val≤2*(k+1-s+i.val)
  omega

theorem oddInterval_krullDim (k s : ℕ) (hs : s≤k+1) (hpos : 0<s) :
    ringKrullDim (MvPolynomial (PluckerIndex s (2*k+1)) K ⧸
      intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))=
      ((s*(2*k+2-2*s)+1 : ℕ) : WithBot ℕ∞) := by
  rw [intervalPlucker_krullDim _ _ (oddIntervalLower_strictMono k s hs)
    (oddIntervalUpper_strictMono k s hs) (oddIntervalLower_le_upper k s hs) hpos]
  have he (i : Fin s) :
      (oddIntervalUpper k s hs i).val-(oddIntervalLower k s hs i).val=2*(k+1-s) := by
    dsimp only [oddIntervalUpper,oddIntervalLower]
    omega
  apply congrArg (fun d : ℕ => (d : WithBot ℕ∞))
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have hgap : 2*k+2-2*s=2*(k+1-s) := by omega
  rw [hgap]
  omega

/-- The containment concerns the full actual interval ideal, including all
polynomial identities among generic maximal minors, not a chosen finite
list of Plücker equations. -/
theorem odd_interval_le_initial [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
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
      apply odd_right_variable_mem_initial I
      refine ⟨i,?_⟩
      have hv : 2*(k+1-(t+2)+i.val)<(I.val i).val := lt_of_not_ge hr
      omega
    · apply odd_left_variable_mem_initial I
      exact ⟨i,lt_of_not_ge hl⟩

/-- The complete canonical odd-pencil initial-ideal equality in the whole
nonempty isotropic-plane range `2 ≤ s ≤ k+1`, with `s=t+2`.
No dimension, primality, support, or containment premise is supplied. -/
theorem odd_isotropic_initial_eq_interval [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) := by
  letI := intervalPluckerIdeal_isPrime (K := K)
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)
  exact initial_eq_of_prime_candidate (K := K) _ _ _ ((t+2)*(2*k+2-2*(t+2))+1)
    (odd_interval_le_initial (K := K) k t hs)
    (oddInterval_krullDim (K := K) k (t+2) hs (by omega))
    (odd_isotropic_Plucker_cone_dimension_ge (K := K) k t hs)

end PaperVerification.AlternatingForms
