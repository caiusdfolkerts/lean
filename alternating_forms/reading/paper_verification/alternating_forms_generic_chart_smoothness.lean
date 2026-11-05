module

public import PaperVerification.AlternatingFormsChartEvaluation
public import PaperVerification.GenericVectorSectionSmoothness
import Mathlib.Tactic

/-!
# A genuine generic-smoothness polynomial for all isotropic charts

The parameter space is the full space of `m` alternating forms. For fixed
ambient and plane dimensions, one nonzero polynomial works simultaneously on
every Plücker chart. The quotient rings are the original row-isotropy rings;
their ideals are neither radicalized nor replaced by simplified equations.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

/-- The bad-parameter polynomial on one standard Grassmannian chart. -/
def isotropicChartSmoothnessPolynomial (p : PluckerIndex (t+2) n) :
    MvPolynomial (Fin m × StrictPairs n) K :=
  criticalAvoidancePolynomial
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p)

theorem isotropicChartSmoothnessPolynomial_ne_zero (p : PluckerIndex (t+2) n) :
    isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p ≠ 0 :=
  criticalAvoidancePolynomial_ne_zero _ _ _ _

/-- Nonvanishing of the chart polynomial implies actual algebraic smoothness. -/
theorem isotropicChartRing_smooth_of_polynomial
    (p : PluckerIndex (t+2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p) ≠ 0) :
    Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  have h := linearSection_quotient_smooth
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t+2) =>
        alternatingRowPair (fun i => a (j.1,i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  exact h

/-- One polynomial for the entire finite Grassmannian atlas. -/
def isotropicSmoothnessPolynomial (t n m : ℕ) :
    MvPolynomial (Fin m × StrictPairs n) K :=
  ∏ p : PluckerIndex (t+2) n, isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p

theorem isotropicSmoothnessPolynomial_ne_zero (t n m : ℕ) :
    isotropicSmoothnessPolynomial (K:=K) t n m ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact isotropicChartSmoothnessPolynomial_ne_zero p

/-- Every original affine chart of the common-isotropic scheme is smooth on
the same principal open of the full coefficient space. -/
theorem isotropic_all_charts_smooth (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0) :
    ∀ p : PluckerIndex (t+2) n,
      Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  intro p
  apply isotropicChartRing_smooth_of_polynomial p a
  rw [isotropicSmoothnessPolynomial,map_prod] at ha
  exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

/-- The simultaneous good locus has a point over the original field. -/
theorem exists_isotropic_all_charts_smooth (t n m : ℕ) :
    ∃ a : (Fin m × StrictPairs n) → K,
      MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0 ∧
      ∀ p : PluckerIndex (t+2) n,
        Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  have hex : ∃ a : (Fin m × StrictPairs n) → K,
      MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0 := by
    by_contra h
    push Not at h
    apply isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero,MvPolynomial.aeval_eq_eval] using h a
  obtain ⟨a,ha⟩ := hex
  exact ⟨a,ha,isotropic_all_charts_smooth t n m a ha⟩

end PaperVerification.AlternatingForms
