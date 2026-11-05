module

public import PaperVerification.JacobianHilbertBasis
public import PaperVerification.JacobianHilbertDefect
public import PaperVerification.HomogeneousQuotientBasis
public import PaperVerification.HilbertTowerCount

/-!
# The full scalar exceptional Hilbert-series formula

The coefficients are dimensions of actual weighted quotient components. The
denominator is represented by its proved inverse in the integral formal power
series ring. A homogeneous Milnor basis is constructed, so no basis or regularity
assumption remains in the final isolated-hypersurface statement.

The finite-group equivariance clause of paper Theorem 6.3 is separate from the
scalar Hilbert-series assertion proved here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K

def integerHilbertSeries (w : ι → ℕ) (U : Submodule K P) : PowerSeries ℤ :=
  PowerSeries.mk fun e => (Module.finrank K (EulerResonance.quotientComponent w e U) : ℤ)

theorem integer_exceptional_hilbert_series (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    integerHilbertSeries w (EulerJacobian.hit (gradient F) F t) =
      integerHilbertSeries w (jacobianSubmodule F) +
        PowerSeries.monomial (h+d) (Module.finrank K (DefectQuotient F t) : ℤ) := by
  ext e
  have he := congrArg (fun n : ℕ => (n : ℤ))
    (exceptional_hilbert_function F w h d e t hw hh hF hres)
  by_cases hd' : e = h+d
  · subst e
    simpa [integerHilbertSeries, PowerSeries.coeff_monomial] using he
  · simpa [integerHilbertSeries, PowerSeries.coeff_monomial, hd', Ne.symm hd'] using he

theorem milnor_basis_component {I : Type*} (F : P) (w : ι → ℕ)
    (b : I → P) (degree : I → ℕ)
    (hbhom : ∀ i, (b i).IsWeightedHomogeneous w (degree i))
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) (i : I) :
    B i ∈ EulerResonance.quotientComponent w (degree i) (jacobianSubmodule F) := by
  rw [EulerResonance.quotientComponent_eq_map]
  exact ⟨b i, hbhom i, hB i⟩

theorem milnor_basisSeries_eq {I : Type*} (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (b : I → P) (degree : I → ℕ)
    (hbhom : ∀ i, (b i).IsWeightedHomogeneous w (degree i))
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    HilbertTowerCount.basisSeries degree = integerHilbertSeries w (jacobianSubmodule F) := by
  ext e
  simp only [HilbertTowerCount.basisSeries, integerHilbertSeries, PowerSeries.coeff_mk]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (EulerResonance.homogeneous_basis_component_finrank w (jacobianSubmodule F)
      (homogeneousComponent_mem_jacobian F w h hF) B degree
      (milnor_basis_component F w b degree hbhom B hB) e).symm

theorem milnor_tower_coefficient {I : Type*} (F : P) (w : ι → ℕ) (h d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (b : I → P) (degree : I → ℕ)
    (hbhom : ∀ i, (b i).IsWeightedHomogeneous w (degree i))
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    (Nat.card {a : ℕ × I // a.1*h + degree a.2 = d} : ℤ) =
      PowerSeries.coeff d (integerHilbertSeries w (jacobianSubmodule F) *
        HilbertTowerCount.geometricInverse h) := by
  have hf : ∀ e, Finite (HilbertTowerCount.Fibre degree e) :=
    EulerResonance.homogeneous_basis_fibre_finite w (jacobianSubmodule F)
      (homogeneousComponent_mem_jacobian F w h hF) hw B degree
      (milnor_basis_component F w b degree hbhom B hB)
  have hs := HilbertTowerCount.towerSeries_eq degree h hh hf
  rw [milnor_basisSeries_eq F w h hF b degree hbhom B hB] at hs
  have hc := congrArg (PowerSeries.coeff d) hs
  simpa only [HilbertTowerCount.towerSeries, PowerSeries.coeff_mk,
    HilbertTowerCount.Towers] using hc

/-- Formula (6.1), under exactly the paper's isolated-hypersurface hypotheses.
The coefficient-extraction expression is taken in `ℤ⟦q⟧`; the formal inverse of
`1-q^h` has been independently verified in `HilbertTowerCount`.

This declaration is the scalar formula. It does not claim the additional
finite-group representation statement of Theorem 6.3. -/
theorem hypersurface_exceptional_hilbert_formula
    {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h d : ℕ) (t : ℂ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (hres : (h : ℂ) + t * ((∑ i, w i : ℕ) + d : ℂ) = 0) :
    integerHilbertSeries w (EulerJacobian.hit (gradient F) F t) =
      integerHilbertSeries w (jacobianSubmodule F) +
        PowerSeries.monomial (h+d)
          (PowerSeries.coeff d (integerHilbertSeries w (jacobianSubmodule F) *
            HilbertTowerCount.geometricInverse h)) := by
  obtain ⟨s, b, B, hhom, hrep⟩ := exists_homogeneous_milnor_basis F w
  choose degree hdegree using hhom
  have hreg := gradient_regular_of_isolated F w h hw hF hiso
  have hdim := (exceptional_defect_dimension hn F w h d t hw hh hF hres
    hreg b degree hdegree B hrep).2
  have hcoeff : (Module.finrank ℂ (DefectQuotient F t) : ℤ) =
      PowerSeries.coeff d (integerHilbertSeries w (jacobianSubmodule F) *
        HilbertTowerCount.geometricInverse h) := by
    rw [hdim]
    exact milnor_tower_coefficient F w h d hw hh hF b degree hdegree B hrep
  rw [integer_exceptional_hilbert_series F w h d t hw hh hF hres, hcoeff]

/-- The paper's formula (6.1) with the parameter literally equal to its printed
fraction and with the paper's occurring-degree hypothesis retained. The Euler
eigenvalue formulation is converted by a proved equivalence. -/
theorem paper_formula_6_1
    {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h d : ℕ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (hd : d ∈ EulerJacobian.occurringDegrees (K := ℂ) w) :
    integerHilbertSeries w (EulerJacobian.hit (gradient F) F
        (-(h : ℂ) / ((∑ i, w i : ℕ) + d : ℂ))) =
      integerHilbertSeries w (jacobianSubmodule F) +
        PowerSeries.monomial (h+d)
          (PowerSeries.coeff d (integerHilbertSeries w (jacobianSubmodule F) *
            HilbertTowerCount.geometricInverse h)) := by
  letI : Nonempty (Fin n) :=
    EulerJacobian.nonempty_of_positive_degree F w h hne hh hF
  apply hypersurface_exceptional_hilbert_formula hn F w h d _ hne hw hh hF hiso
  exact (EulerJacobian.eigenvalue_zero_iff w hw h d _).mpr rfl

end PaperVerification.JacobianDivergence
