module

public import PaperVerification.AlternatingFormsOddInitialCharacteristic
public import PaperVerification.AlternatingFormsOnePlane

/-!
# The one-plane boundary of Theorem 7.1

Every line is isotropic for both alternating forms.  In degree one the
printed Richardson interval contains every Plucker coordinate, so its
ideal is the actual Grassmannian ideal.  Its weight initial ideal is the
same ideal in every characteristic, completing the boundary omitted by
the convenient parameterization `s=t+2` of the nontrivial equations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K]

theorem odd_onePlane_interval_eq_matrix (k : ℕ) :
    intervalPluckerIdeal (K := K)
      (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega)) =
      matrixPluckerIdeal := by
  unfold intervalPluckerIdeal
  apply sup_eq_left.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨I,hbad,rfl⟩
  exfalso
  apply hbad
  intro i
  have hi := i.isLt
  have hI := (I.val i).isLt
  constructor
  · change 2*i.val≤(I.val i).val
    omega
  · change (I.val i).val≤2*(k+1-1+i.val)
    omega

/-- The exact one-plane initial-ideal clause of Theorem 7.1; no
characteristic hypothesis is needed for this boundary case. -/
theorem paper_theorem_7_1_initial_ideal_one_plane (k : ℕ) :
    initialIdeal (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
        (pluckerVertexWeight (oddNatVertexWeight k)) =
      intervalPluckerIdeal
        (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega)) := by
  rw [odd_onePlane_interval_eq_matrix]
  exact onePlane_initialIdeal _

end PaperVerification.AlternatingForms
