module

public import Recovery.Unimodular.KoszulSupport.TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Lean.Elab.Tactic.Omega

/-!
# The actual bounded bar Euler characteristic and the Koszul series identity

For each original internal degree `N`, use a genuine chain complex of
vector spaces. Its terms have the coefficients of the powers of the
positive-degree series, its outgoing boundary above length `N` vanishes,
and its homology is concentrated at length `N`. Euler--Poincare then gives
an exact inverse identity of formal power series.

The hypotheses concern actual terms, differentials and homology objects.
They are intermediate inputs to be verified for a bar construction; this
file does not assume or assert that the paper's algebra is Koszul.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators PowerSeries
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.WeightedBarEuler

section FormalSeries

variable {R : Type*} [CommRing R]

/-- Positive series have no coefficient in a degree below their power. -/
theorem coeff_power_eq_zero_of_lt (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) {N r : ℕ} (hNr : N < r) :
    PowerSeries.coeff N (P^r)=0 := by
  induction r generalizing N with
  | zero => omega
  | succ r ih =>
      rw [pow_succ,PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro a ha
      have he := Finset.mem_antidiagonal.mp ha
      by_cases hz : a.2=0
      · rw [hz,hP,mul_zero]
      · rw [ih (by omega),zero_mul]

/-- The coefficientwise finite alternating sum of positive-series powers. -/
def eulerSeries (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun N =>
    ∑ r∈Finset.range (N+1),(-1 : R)^r*PowerSeries.coeff N (P^r))

/-- The finite geometric expression used to check any prescribed coefficient. -/
def finiteGeometric (P : PowerSeries R) (N : ℕ) : PowerSeries R :=
  ∑ r∈Finset.range (N+1),PowerSeries.C ((-1 : R)^r)*P^r

theorem coeff_finiteGeometric (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) {i N : ℕ} (hi : i ≤ N) :
    PowerSeries.coeff i (finiteGeometric P N)=PowerSeries.coeff i (eulerSeries P) := by
  simp only [finiteGeometric,eulerSeries,PowerSeries.coeff_mk,map_sum,
    PowerSeries.coeff_C_mul]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))
  intro r hr hri
  have hir : i < r := by
    have hri' : ¬r < i+1 := fun hr' => hri (Finset.mem_range.mpr hr')
    omega
  rw [coeff_power_eq_zero_of_lt P hP hir,mul_zero]

theorem one_add_mul_finiteGeometric (P : PowerSeries R) (N : ℕ) :
    (1+P)*finiteGeometric P N=1-(-P)^(N+1) := by
  have he : finiteGeometric P N=∑ r∈Finset.range (N+1),(-P)^r := by
    unfold finiteGeometric
    apply Finset.sum_congr rfl
    intro r hr
    simp only [map_pow,map_neg,map_one]
    exact (neg_pow P r).symm
  rw [he]
  simpa only [sub_neg_eq_add] using mul_neg_geom_sum (-P) (N+1)

/-- The coefficientwise finite Euler sum is the genuine inverse of `1+P`. -/
theorem one_add_mul_eulerSeries (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) : (1+P)*eulerSeries P=1 := by
  apply PowerSeries.ext
  intro N
  calc
    PowerSeries.coeff N ((1+P)*eulerSeries P)=
        PowerSeries.coeff N ((1+P)*finiteGeometric P N) := by
      rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have he := Finset.mem_antidiagonal.mp ha
      rw [coeff_finiteGeometric P hP (by omega : a.2 ≤ N)]
    _=PowerSeries.coeff N (1 : PowerSeries R) := by
      rw [one_add_mul_finiteGeometric,map_sub,
        coeff_power_eq_zero_of_lt (-P)
          (by rw [map_neg,hP,neg_zero]) (Nat.lt_succ_self N),sub_zero]

end FormalSeries

section ActualChainComplexes

universe u v
variable {K : Type u} [Field K]

/-- The signed series of the actual diagonal internal-degree homology. -/
def diagonalHomologySeries (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N => (-1 : ℤ)^N*(Module.finrank K ((C N).homology N) : ℤ))

/-- Finite Euler--Poincare identifies the two series, with every term and
homology object retaining its actual categorical meaning. -/
theorem eulerSeries_eq_diagonalHomologySeries
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hboundary : ∀ N,(C N).d (N+1) N=0)
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    eulerSeries P=diagonalHomologySeries C := by
  apply PowerSeries.ext
  intro N
  simp only [eulerSeries,diagonalHomologySeries,PowerSeries.coeff_mk]
  calc
    (∑ r∈Finset.range (N+1),(-1 : ℤ)^r*PowerSeries.coeff N (P^r))=
        ∑ r∈Finset.range (N+1),(-1 : ℤ)^r*(Module.finrank K ((C N).X r) : ℤ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hterm N r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
    _=∑ r∈Finset.range (N+1),(-1 : ℤ)^r*(Module.finrank K ((C N).homology r) : ℤ) :=
      (C N).sum_range_finrank_X_eq_sum_range_finrank_homology
        (hfinite N) (hboundary N)
    _=(-1 : ℤ)^N*(Module.finrank K ((C N).homology N) : ℤ) := by
      apply Finset.sum_eq_single N
      · intro r hr hne
        rw [ModuleCat.finrank_eq_zero_of_isZero
          (hhomology N r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hne),
          Nat.cast_zero,mul_zero]
      · intro hN
        exact (hN (Finset.mem_range.mpr (Nat.lt_succ_self N))).elim

/-- The same identity needs only the actual boundary above length `N` to
vanish; this is the direct interface for a separately constructed bar complex. -/
theorem one_add_mul_diagonalHomologySeries_of_boundary_zero
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hP : PowerSeries.coeff 0 P=0)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hboundary : ∀ N,(C N).d (N+1) N=0)
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    (1+P)*diagonalHomologySeries C=1 := by
  rw [←eulerSeries_eq_diagonalHomologySeries C P hfinite hboundary hterm hhomology]
  exact one_add_mul_eulerSeries P hP

/-- The Koszul series identity from a bounded actual internal-degree bar
complex. No identification with a quadratic dual is assumed here. -/
theorem one_add_mul_diagonalHomologySeries
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hP : PowerSeries.coeff 0 P=0)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hbounded : ∀ N,IsZero ((C N).X (N+1)))
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    (1+P)*diagonalHomologySeries C=1 := by
  rw [←eulerSeries_eq_diagonalHomologySeries C P hfinite
    (fun N => (hbounded N).eq_of_src _ 0) hterm hhomology]
  exact one_add_mul_eulerSeries P hP

end ActualChainComplexes
end PaperVerification.WeightedBarEuler
