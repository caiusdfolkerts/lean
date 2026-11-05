import verification_bundle
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Module

/-!
# An affinely independent four-cycle

Lemma 3(i) of the paper is independent of convexity. Four affinely
independent points have no nonzero affine relation. Summing the four
edge equations therefore forces their four real scale factors to agree.
Integrating the first three equations gives one common translation.

The statements below hold in every real module, hence in every real
Euclidean dimension. The edge multipliers are arbitrary real numbers.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- On an affinely independent four-cycle, all four edge scale factors
of a parallel redrawing coincide. No sign or nonzero condition is imposed. -/
theorem four_cycle_edge_scalars_eq
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p) (a : Fin 4 → ℝ)
    (h01 : h 1 - h 0 = a 0 • (p 1 - p 0))
    (h12 : h 2 - h 1 = a 1 • (p 2 - p 1))
    (h23 : h 3 - h 2 = a 2 • (p 3 - p 2))
    (h30 : h 0 - h 3 = a 3 • (p 0 - p 3)) :
    ∀ i : Fin 4, a i = a 0 := by
  classical
  have hcycle :
      a 0 • (p 1 - p 0) + a 1 • (p 2 - p 1) +
        a 2 • (p 3 - p 2) + a 3 • (p 0 - p 3) = 0 := by
    rw [← h01, ← h12, ← h23, ← h30]
    abel
  let w : Fin 4 → ℝ := ![a 3 - a 0, a 0 - a 1, a 1 - a 2, a 2 - a 3]
  have hw : (∑ i : Fin 4, w i) = 0 := by
    simp [w, Fin.sum_univ_succ] <;> ring
  have hwp : (∑ i : Fin 4, w i • p i) = 0 := by
    calc
      _ = a 0 • (p 1 - p 0) + a 1 • (p 2 - p 1) +
          a 2 • (p 3 - p 2) + a 3 • (p 0 - p 3) := by
        simp [w, Fin.sum_univ_succ] <;> module
      _ = 0 := hcycle
  have hweights : ∀ i : Fin 4, w i = 0 := by
    intro i
    exact hp.eq_zero_of_sum_eq_zero hw hwp i (Finset.mem_univ i)
  have ha01 : a 0 = a 1 := sub_eq_zero.mp (by simpa [w] using hweights 1)
  have ha12 : a 1 = a 2 := sub_eq_zero.mp (by simpa [w] using hweights 2)
  have ha23 : a 2 = a 3 := sub_eq_zero.mp (by simpa [w] using hweights 3)
  intro i
  fin_cases i
  · rfl
  · exact ha01.symm
  · exact (ha01.trans ha12).symm
  · exact ((ha01.trans ha12).trans ha23).symm

/-- The explicit homothety formula after the four edge scales agree. -/
theorem four_cycle_redrawing_formula
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p) (a : Fin 4 → ℝ)
    (h01 : h 1 - h 0 = a 0 • (p 1 - p 0))
    (h12 : h 2 - h 1 = a 1 • (p 2 - p 1))
    (h23 : h 3 - h 2 = a 2 • (p 3 - p 2))
    (h30 : h 0 - h 3 = a 3 • (p 0 - p 3)) :
    ∀ i : Fin 4, h i = a 0 • p i + (h 0 - a 0 • p 0) := by
  have ha := four_cycle_edge_scalars_eq p h hp a h01 h12 h23 h30
  rw [ha 1] at h12
  rw [ha 2] at h23
  intro i
  fin_cases i
  · change h 0 = a 0 • p 0 + (h 0 - a 0 • p 0)
    abel
  · calc
      h 1 = (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 1 - p 0) + h 0 := by rw [h01]
      _ = a 0 • p 1 + (h 0 - a 0 • p 0) := by module
  · calc
      h 2 = (h 2 - h 1) + (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 2 - p 1) + a 0 • (p 1 - p 0) + h 0 := by rw [h12, h01]
      _ = a 0 • p 2 + (h 0 - a 0 • p 0) := by module
  · calc
      h 3 = (h 3 - h 2) + (h 2 - h 1) + (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 3 - p 2) + a 0 • (p 2 - p 1) +
          a 0 • (p 1 - p 0) + h 0 := by rw [h23, h12, h01]
      _ = a 0 • p 3 + (h 0 - a 0 • p 0) := by module

/-- Lemma 3(i): every parallel redrawing of an affinely independent
four-cycle is a homothety and a translation. Addition on `Fin 4` is
cyclic, so the quantified edges are 01, 12, 23, and 30. -/
theorem lemma_three_one
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p)
    (hparallel : ∀ i : Fin 4, ∃ a : ℝ,
      h (i + 1) - h i = a • (p (i + 1) - p i)) :
    ∃ a : ℝ, ∃ b : V, ∀ i : Fin 4, h i = a • p i + b := by
  classical
  choose a ha using hparallel
  refine ⟨a 0, h 0 - a 0 • p 0, ?_⟩
  apply four_cycle_redrawing_formula p h hp a
  · simpa using ha 0
  · simpa using ha 1
  · simpa using ha 2
  · simpa using ha 3

end CubicalIndecomposability
