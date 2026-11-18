module
public import Papers.GraphicalZonotopes.FiniteLinearAvoidance
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Perturbing a functional away from finitely many hyperplanes

The statements apply to any real normed vector space, including a subspace
of a dual space. They are used to select exposing functionals while retaining
the strict inequalities that define an exposed face.
-/

noncomputable section

namespace Papers.Geometry

open Set

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_near_forall_ne_zero (forms : ι → V →L[ℝ] ℝ)
    (hforms : ∀ i, ∃ x, forms i x ≠ 0) (v : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : V, dist w v < ε ∧ ∀ i, forms i w ≠ 0 := by
  classical
  obtain ⟨direction, hdirection⟩ :=
    exists_forall_linear_forms_ne_zero
      (fun i => (forms i).toLinearMap) hforms
  let δ := ε / (‖direction‖ + 1)
  have hden : 0 < ‖direction‖ + 1 := by linarith [norm_nonneg direction]
  have hδ : 0 < δ := div_pos hε hden
  let bad : Finset ℝ := Finset.univ.image (fun i => -forms i v / forms i direction)
  obtain ⟨t, ht, hnotbad⟩ := (Set.Ioo_infinite hδ).exists_notMem_finset bad
  refine ⟨v + t • direction, ?_, ?_⟩
  · have hprod : t * (‖direction‖ + 1) < ε := (lt_div_iff₀ hden).mp ht.2
    have hdist : dist (v + t • direction) v = t * ‖direction‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [hdist]
    nlinarith [ht.1]
  · intro i hzero
    apply hnotbad
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    symm
    apply (eq_div_iff (hdirection i)).mpr
    change t * (forms i) direction = -(forms i) v
    simp only [map_add, map_smul, smul_eq_mul] at hzero
    linarith only [hzero]

/-- A nonempty open set cannot be covered by finitely many proper linear
hyperplanes. The point can be chosen inside the original open set. -/
theorem exists_in_open_forall_ne_zero (forms : ι → V →L[ℝ] ℝ)
    (hforms : ∀ i, ∃ x, forms i x ≠ 0) {U : Set V}
    (hopen : IsOpen U) (hne : U.Nonempty) :
    ∃ w ∈ U, ∀ i, forms i w ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen v hv
  obtain ⟨w, hw, hall⟩ := exists_near_forall_ne_zero forms hforms v hε
  exact ⟨w, hball hw, hall⟩

end Papers.Geometry
