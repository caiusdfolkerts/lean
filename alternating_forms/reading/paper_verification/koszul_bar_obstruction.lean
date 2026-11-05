module

public import PaperVerification.WeightedBarDegrees
public import PaperVerification.WeightedBarEuler
public import PaperVerification.KoszulHilbertObstruction
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring

/-!
# Exact homological and series obstructions in Proposition 5.3

The dimension-five result forces nonzero off-diagonal homology in the
actual internal-degree-six bar complex. Its input is the independently
specified positive basis-degree series; its terms and differential are the
actual noncommutative bar construction, not a proposed inverse series.

The independent formal-series lemma excludes the Koszul identity when a
bounded series and the stated PBW denominator are given. It is not a
claim of the full Koszul classification: identification of diagonal bar
homology with the quadratic dual and the small-dimensional positive cases
remain separate proof obligations. This file is a candidate until checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.KoszulBarObstruction

universe u

open PaperVerification.WeightedBarEuler PaperVerification.KoszulHilbertObstruction

def dimensionFivePositiveSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => if d=1 then 5 else if d=2 then 8 else if d=3 then 1 else 0)

theorem dimensionFive_signed_rescale :
    PowerSeries.rescale (-1 : ℤ) (1+dimensionFivePositiveSeries)=
      dimensionFiveSignedHilbert := by
  apply PowerSeries.ext
  intro d
  by_cases h0 : d=0
  · subst d
    rw [PowerSeries.coeff_rescale]
    norm_num [dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h1 : d=1
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h2 : d=2
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h3 : d=3
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  simp [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert,
    h0,h1,h2,h3]

theorem dimensionFive_euler_coefficient_six :
    PowerSeries.coeff 6 (eulerSeries dimensionFivePositiveSeries) = -26 := by
  have h0 : PowerSeries.coeff 0 dimensionFivePositiveSeries=0 := by
    simp [dimensionFivePositiveSeries]
  have h := congrArg (PowerSeries.rescale (-1 : ℤ))
    (one_add_mul_eulerSeries dimensionFivePositiveSeries h0)
  rw [map_mul,dimensionFive_signed_rescale,map_one] at h
  have h6 := inverse_coefficient_six _ h
  simpa only [PowerSeries.coeff_rescale,show (-1 : ℤ)^6=1 by norm_num,one_mul] using h6

/-- The negative Euler coefficient forces actual lower-length homology;
no vanishing or Koszul identity is assumed in this conclusion. -/
theorem dimensionFive_complex_off_diagonal
    {K : Type*} [Field K] (C : ChainComplex (ModuleCat K) ℕ)
    (hfinite : ∀ r, r≤6 → Module.Finite K (C.X r))
    (hboundary : C.d 7 6=0)
    (hterm : ∀ r, r≤6 → (Module.finrank K (C.X r) : ℤ)=
      PowerSeries.coeff 6 (dimensionFivePositiveSeries^r)) :
    ∃ r, r<6 ∧ ¬IsZero (C.homology r) := by
  by_contra h
  have hz (r : ℕ) (hr : r<6) : IsZero (C.homology r) := by
    by_contra hn
    exact h ⟨r,hr,hn⟩
  have ht : (∑ r∈Finset.range 7,(-1 : ℤ)^r*(Module.finrank K (C.X r) : ℤ)) = -26 := by
    calc
      _ = PowerSeries.coeff 6 (eulerSeries dimensionFivePositiveSeries) := by
        simp only [eulerSeries,PowerSeries.coeff_mk]
        apply Finset.sum_congr rfl
        intro r hr
        rw [hterm r (by have := Finset.mem_range.mp hr; omega)]
      _ = -26 := dimensionFive_euler_coefficient_six
  have hh : (∑ r∈Finset.range 7,(-1 : ℤ)^r*(Module.finrank K (C.homology r) : ℤ)) =
      (Module.finrank K (C.homology 6) : ℤ) := by
    rw [Finset.sum_eq_single 6]
    · norm_num
    · intro r hr hne
      rw [ModuleCat.finrank_eq_zero_of_isZero (hz r (by
        have := Finset.mem_range.mp hr
        omega)),Nat.cast_zero,mul_zero]
    · intro h6
      exact (h6 (by simp)).elim
  have he := C.sum_range_finrank_X_eq_sum_range_finrank_homology hfinite hboundary
  rw [ht,hh] at he
  have hnonnegative : (0 : ℤ)≤(Module.finrank K (C.homology 6) : ℤ) :=
    Int.natCast_nonneg _
  omega

set_option maxHeartbeats 800000 in
/-- The preceding obstruction for the actual noncommutative reduced bar
complex, using the real original homogeneous basis degrees. -/
theorem dimensionFive_actual_bar_off_diagonal
    {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
    (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
    (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
    (δ : I → ℕ)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 →
      δ c=δ a+δ b)
    (hpos : ∀ i,0<δ i)
    (hseries : WeightedBar.positiveSeries δ=dimensionFivePositiveSeries) :
    let C : ChainComplex (ModuleCat K) ℕ :=
      WeightedBar.internalComplex (K := K) (A := A) (I := I) ε B hunit hε δ hδ 6
    ∃ r,r<6 ∧ ¬IsZero (C.homology r) := by
  let C : ChainComplex (ModuleCat K) ℕ :=
    WeightedBar.internalComplex (K := K) (A := A) (I := I) ε B hunit hε δ hδ 6
  have hf : ∀ r,r≤6 → Module.Finite K (C.X r) := fun r _ =>
    WeightedBar.pieceFinite (K := K) (I := I) δ r 6
  have hb : C.d 7 6=0 :=
    WeightedBar.internalComplex_top_differential (K := K) ε B hunit hε δ hδ hpos 6
  have ht : ∀ r,r≤6 → (Module.finrank K (C.X r) : ℤ)=
      PowerSeries.coeff 6 (dimensionFivePositiveSeries^r) := by
    intro r hr
    exact (WeightedBar.internalComplex_term_rank (K := K)
      ε B hunit hε δ hδ r 6).trans (congrArg (fun P : ℤ⟦X⟧ =>
        PowerSeries.coeff 6 (P^r)) hseries)
  exact dimensionFive_complex_off_diagonal C hf hb ht

theorem coeff_one_add_X_pow (n d : ℕ) :
    PowerSeries.coeff d ((1+PowerSeries.X)^n : ℤ⟦X⟧)=(n.choose d : ℤ) := by
  have hp : ((1+PowerSeries.X)^n : ℤ⟦X⟧)=
      (((1+Polynomial.X)^n : Polynomial ℤ) : ℤ⟦X⟧) := by simp
  rw [hp,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

/-- The exact impossible coefficient above the exterior degree ceiling. -/
theorem proposedKoszulPolynomial_top (n : ℕ) :
    PowerSeries.coeff (n+4)
      (((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2) : ℤ⟦X⟧)=1 := by
  let A : ℤ⟦X⟧ := (1+PowerSeries.X)^n
  have hhigh : PowerSeries.coeff (n+4) A=0 := by
    dsimp only [A]
    rw [coeff_one_add_X_pow,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
  have hmid : PowerSeries.coeff (n+2) A=0 := by
    dsimp only [A]
    rw [coeff_one_add_X_pow,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
  have hself : PowerSeries.coeff n A=1 := by simp [A,coeff_one_add_X_pow]
  have htwo : PowerSeries.coeff (n+4) (A*PowerSeries.X^2)=0 := by
    rw [show n+4=(n+2)+2 by omega,PowerSeries.coeff_mul_X_pow,hmid]
  have hfour : PowerSeries.coeff (n+4) (A*PowerSeries.X^4)=1 := by
    rw [PowerSeries.coeff_mul_X_pow,hself]
  have hexp : A*(1-PowerSeries.X^2)^2=
      A-(A*PowerSeries.X^2+A*PowerSeries.X^2)+A*PowerSeries.X^4 := by ring
  change PowerSeries.coeff (n+4) (A*(1-PowerSeries.X^2)^2)=1
  rw [hexp,map_add,map_sub,map_add,hhigh,htwo,hfour]
  norm_num

/-- The PBW denominator and a bounded exterior Hilbert function cannot
satisfy the Koszul identity, in any dimension in which that denominator holds. -/
theorem no_bounded_koszul_identity (n : ℕ) (H D : ℤ⟦X⟧)
    (hH : PowerSeries.coeff (n+4) H=0)
    (hD : D*((1-PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1) :
    H*PowerSeries.rescale (-1 : ℤ) D≠1 := by
  intro hKoszul
  have hdual : PowerSeries.rescale (-1 : ℤ) D*
      ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1 := by
    have h := congrArg (PowerSeries.rescale (-1 : ℤ)) hD
    simpa only [map_mul,map_pow,map_sub,map_one,PowerSeries.rescale_neg_one_X,
      neg_sq,sub_neg_eq_add] using h
  have he : H=(1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2 := by
    calc
      H=H*1 := (mul_one H).symm
      _=H*(PowerSeries.rescale (-1 : ℤ) D*
          ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2)) := by rw [hdual]
      _=(H*PowerSeries.rescale (-1 : ℤ) D)*
          ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2) := (mul_assoc _ _ _).symm
      _=_ := by rw [hKoszul,one_mul]
  have hc := congrArg (PowerSeries.coeff (n+4)) he
  rw [hH,proposedKoszulPolynomial_top] at hc
  exact zero_ne_one hc

end PaperVerification.KoszulBarObstruction
