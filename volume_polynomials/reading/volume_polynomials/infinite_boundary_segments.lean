module

public import VolumePolynomials.BivariateCoordinates
public import VolumePolynomials.SemialgebraicBoundary
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Infinitely many nonparallel boundary segments exclude semialgebraicity

This is the geometric-to-algebraic obstruction used for the forced Minkowski
series in Theorem 7.3. The statement concerns actual subsets of the real plane.
No convexity or smoothness is needed for this obstruction.

The proof uses polynomial roots over the integral domain `ℝ[X]`: every
nonhorizontal boundary segment on which a bivariate polynomial vanishes gives
an affine polynomial root. Pairwise nonparallel directions give distinct roots.
-/

open Polynomial Set
open scoped Polynomial.Bivariate

namespace VolumePolynomials

noncomputable def segmentLinePolynomial (a u : ℝ × ℝ) : ℝ[X] :=
  C (a.1 - u.1 / u.2 * a.2) + C (u.1 / u.2) * X

theorem segmentLinePolynomial_eval (a u : ℝ × ℝ) (hu : u.2 ≠ 0) (t : ℝ) :
    (segmentLinePolynomial a u).eval (a.2 + t * u.2) = a.1 + t * u.1 := by
  simp only [segmentLinePolynomial, eval_add, eval_C, eval_mul, eval_X]
  field_simp [hu]
  ring

/-- Vanishing on a genuine segment makes its affine line a polynomial root. -/
theorem line_isRoot_of_segment_vanishing (p : ℝ[X][Y]) (a u : ℝ × ℝ)
    (hu : u.2 ≠ 0)
    (hzero : ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      p.evalEval (a.2 + t * u.2) (a.1 + t * u.1) = 0) :
    p.IsRoot (segmentLinePolynomial a u) := by
  change p.eval (segmentLinePolynomial a u) = 0
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Set.InjOn (fun t : ℝ => a.2 + t * u.2)
      (Icc (-1 / 2 : ℝ) (1 / 2)) := by
    intro t ht v hv h
    have hmul : (t - v) * u.2 = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hu)
  have hinfinite : ((fun t : ℝ => a.2 + t * u.2) ''
      Icc (-1 / 2 : ℝ) (1 / 2)).Infinite :=
    (Set.Icc_infinite (show (-1 / 2 : ℝ) < 1 / 2 by norm_num)).image hinj
  apply hinfinite.mono
  rintro y ⟨t, ht, rfl⟩
  change (p.eval (segmentLinePolynomial a u)).eval (a.2 + t * u.2) = 0
  rw [bivariate_eval_polynomial, segmentLinePolynomial_eval a u hu t]
  exact hzero t ht

theorem segmentLinePolynomial_ne_of_det_ne_zero (a b u v : ℝ × ℝ)
    (hu : u.2 ≠ 0) (hv : v.2 ≠ 0)
    (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    segmentLinePolynomial a u ≠ segmentLinePolynomial b v := by
  intro h
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 1) h
  have hslope : u.1 / u.2 = v.1 / v.2 := by
    simpa [segmentLinePolynomial] using hcoeff
  have hcross := (div_eq_div_iff hu hv).mp hslope
  apply hdet
  nlinarith

/-- A real polynomial in two variables cannot vanish on countably many
segments in pairwise nonparallel directions unless it is zero. -/
theorem bivariate_eq_zero_of_nonparallel_segments (p : ℝ[X][Y])
    (a u : ℕ → ℝ × ℝ)
    (hnonparallel : ∀ i j : ℕ, i ≠ j →
      (u i).1 * (u j).2 - (u i).2 * (u j).1 ≠ 0)
    (hzero : ∀ i : ℕ, ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      p.evalEval ((a i).2 + t * (u i).2) ((a i).1 + t * (u i).1) = 0) :
    p = 0 := by
  by_contra hp
  let J : Set ℕ := {i | (u i).2 ≠ 0}
  have hmap : Set.MapsTo (fun i => segmentLinePolynomial (a i) (u i)) J
      {q : ℝ[X] | p.IsRoot q} := by
    intro i hi
    exact line_isRoot_of_segment_vanishing p (a i) (u i) hi (hzero i)
  have hinj : Set.InjOn (fun i => segmentLinePolynomial (a i) (u i)) J := by
    intro i hi j hj hij
    by_contra hne
    exact (segmentLinePolynomial_ne_of_det_ne_zero (a i) (a j) (u i) (u j)
      hi hj (hnonparallel i j hne)) hij
  have hfinite : J.Finite :=
    Set.Finite.of_injOn hmap hinj (Polynomial.finite_setOfPred_isRoot hp)
  have hexceptional : Jᶜ.Subsingleton := by
    intro i hi j hj
    by_contra hne
    have hui : (u i).2 = 0 := by simpa only [J, mem_compl_iff, mem_ofPred_eq, not_not] using hi
    have huj : (u j).2 = 0 := by simpa only [J, mem_compl_iff, mem_ofPred_eq, not_not] using hj
    apply hnonparallel i j hne
    simp only [hui, huj, mul_zero, zero_mul, sub_self]
  have hall : (Set.univ : Set ℕ).Finite := by
    simpa only [union_compl_self] using hfinite.union hexceptional.finite
  exact Set.infinite_univ hall

/-- A planar set with the indicated boundary segments is not semialgebraic.
The coordinate conversion is an actual homeomorphism of the real plane. -/
theorem not_semialgebraic_of_nonparallel_boundary_segments
    (s : Set (ℝ × ℝ)) (a u : ℕ → ℝ × ℝ)
    (hnonparallel : ∀ i j : ℕ, i ≠ j →
      (u i).1 * (u j).2 - (u i).2 * (u j).1 ≠ 0)
    (hsegment : ∀ i : ℕ, ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      a i + t • u i ∈ frontier s) :
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' s) := by
  intro hs
  obtain ⟨p, hp, hzero⟩ := frontier_polynomial_relation hs
  have hpoly : twoVariableEquiv p = 0 := by
    apply bivariate_eq_zero_of_nonparallel_segments (twoVariableEquiv p) a u hnonparallel
    intro i t ht
    rw [twoVariableEquiv_eval]
    apply hzero
    rw [← Homeomorph.preimage_frontier]
    change a i + t • u i ∈ frontier s
    exact hsegment i t ht
  exact hp (twoVariableEquiv.injective (by simpa using hpoly))

end VolumePolynomials
