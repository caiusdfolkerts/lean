module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The dimension-five reciprocal obstruction

This is the exact numerical step used in Proposition 5.3.  It concerns
ordinary formal power series over the integers.  Any inverse of
`1 - 5t + 8t² - t³` has coefficient `-26` in degree six, and consequently
cannot be a series of dimensions.  The recurrence is obtained from the
actual coefficient formula for multiplication, rather than a numerical
experiment or a truncated inverse accepted as a hypothesis.

This supporting result does not assert the Koszul identity or identify a
series with Tor.  Those are separate homological proof obligations.  This
source remains a candidate until its complete proof is checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.KoszulHilbertObstruction

def dimensionFiveSignedHilbert : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => if d=0 then 1 else if d=1 then -5 else
    if d=2 then 8 else if d=3 then -1 else 0)

theorem inverse_coefficient_six (F : ℤ⟦X⟧)
    (hF : dimensionFiveSignedHilbert*F=1) : PowerSeries.coeff 6 F = -26 := by
  have hc (d : ℕ) :
      (∑ i ∈ Finset.range (d+1),
        PowerSeries.coeff i dimensionFiveSignedHilbert*PowerSeries.coeff (d-i) F)=
          if d=0 then 1 else 0 := by
    have h := congrArg (PowerSeries.coeff d) hF
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i dimensionFiveSignedHilbert*PowerSeries.coeff j F) d,
      PowerSeries.coeff_one] at h
    exact h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  norm_num [dimensionFiveSignedHilbert,PowerSeries.coeff_mk,
    Finset.sum_range_succ] at h0 h1 h2 h3 h4 h5 h6
  omega

theorem no_nonnegative_inverse (F : ℤ⟦X⟧)
    (hF : dimensionFiveSignedHilbert*F=1)
    (hnonnegative : ∀ d,0≤PowerSeries.coeff d F) : False := by
  have h6 := inverse_coefficient_six F hF
  have hpos := hnonnegative 6
  omega

end PaperVerification.KoszulHilbertObstruction
