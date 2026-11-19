module

public import PaperVerification.WeightedBarTor

/-!
# Converting actual diagonal homology dimensions into the Koszul identity

This general comparison lemma uses ordinary Tor concentration, the proved
finite bar Euler identity, and an explicitly supplied comparison with the
actual positive diagonal homology dimensions. The constant term follows
from Euler itself. Applications must prove every dimension comparison;
none is inserted as a new axiom or a definition of Koszulness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped PowerSeries

namespace PaperVerification.KoszulDiagonalSeries

open WeightedBar AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ) (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hpos in
/-- All comparison assumptions are explicit and concern actual categorical
homology, independently constructed before the Hilbert identity. -/
theorem one_add_mul_signed_series
    (H : PowerSeries ℤ) (hzero : PowerSeries.coeff 0 H=1)
    (hdim : ∀ r,(Module.finrank K
      ((internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1)) : ℤ)=
        PowerSeries.coeff (r+1) H)
    (hKoszul : HasDiagonalTor ε B hunit hε δ hδ) :
    (1+positiveSeries δ)*PowerSeries.rescale (-1 : ℤ) H=1 := by
  let D := WeightedBarEuler.diagonalHomologySeries
    (internalComplex ε B hunit hε δ hδ)
  have hEuler : (1+positiveSeries δ)*D=1 :=
    one_add_mul_signed_diagonalTor ε B hunit hε δ hδ hpos hKoszul
  have hDzero : PowerSeries.coeff 0 D=1 := by
    have he := congrArg PowerSeries.constantCoeff hEuler
    simp only [map_mul,map_add,map_one,positiveSeries_constantCoeff δ hpos,
      add_zero,one_mul] at he
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using he
  have he : D=PowerSeries.rescale (-1 : ℤ) H := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        rw [hDzero,PowerSeries.coeff_rescale,pow_zero,one_mul,hzero]
    | succ r =>
        simp only [D,WeightedBarEuler.diagonalHomologySeries,PowerSeries.coeff_mk,
          PowerSeries.coeff_rescale]
        rw [hdim r]
  rw [←he]
  exact hEuler

end PaperVerification.KoszulDiagonalSeries
