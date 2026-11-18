module

public import ToricPower.RelativeSimplicialRefinement
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Maximal cones of a complete fan have full dimension

The proof uses only continuity of real affine functions of one real
parameter. A sufficiently small motion from a point can enter only
cones already containing that point. A face-determining point of a
maximal cone therefore cannot move out of its linear span in a complete
fan. No topology on the abstract ambient vector space is assumed.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i)

/-- A sufficiently short positive motion avoids all cones that do not
contain its starting point. -/
theorem exists_positive_motion_same_star (x v : V) :
    ∃ t : ℝ, 0 < t ∧
      ∀ C ∈ fan.cones, x + t • v ∈ C → x ∈ C := by
  classical
  let excluded := {C : fan.cones // x ∉ C.val}
  have separators : ∀ C : excluded, ∃ φ : Module.Dual ℝ V,
      (∀ y ∈ C.val.val, 0 ≤ φ y) ∧ φ x < 0 := by
    intro C
    have h : ¬ (∀ φ : Module.Dual ℝ V,
        (∀ y ∈ C.val.val, 0 ≤ φ y) → 0 ≤ φ x) :=
      fun h => C.property ((finiteCone_mem_iff_nonneg C.val.val
        (fan.isToricCone C.val.property).fg x).mpr h)
    push_neg at h
    exact h
  choose φ nonnegative negative using separators
  let U : Set ℝ := ⋂ C : excluded, {t | φ C x + t * φ C v < 0}
  have openU : IsOpen U := isOpen_iInter_of_finite fun C =>
    isOpen_lt (continuous_const.add (continuous_id.mul continuous_const)) continuous_const
  have zeroInU : (0 : ℝ) ∈ U := by
    apply Set.mem_iInter.mpr
    intro C
    simpa only [Set.mem_setOf_eq, zero_mul, add_zero] using negative C
  obtain ⟨epsilon, positive, inside⟩ := Metric.isOpen_iff.mp openU 0 zeroInU
  have halfPositive : 0 < epsilon / 2 := half_pos positive
  have small : epsilon / 2 ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos halfPositive]
    exact half_lt_self positive
  refine ⟨epsilon / 2, halfPositive, ?_⟩
  intro C hC moved
  by_contra outside
  let index : excluded := ⟨⟨C, hC⟩, outside⟩
  have neg := Set.mem_iInter.mp (inside small) index
  have nonneg := nonnegative index (x + (epsilon / 2) • v) moved
  rw [map_add, map_smul, smul_eq_mul] at nonneg
  exact (not_lt_of_ge nonneg) neg

/-- Every maximal cone in a complete finite rational fan spans the
entire ambient vector space. -/
theorem maximalCone_span_eq_top (complete : fan.IsComplete)
    {C : PointedCone ℝ V} (maximal : Maximal (· ∈ fan.cones) C) :
    Submodule.span ℝ (C : Set V) = ⊤ := by
  classical
  by_contra notFull
  obtain ⟨v, outside⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr notFull)
  have vOutside : v ∉ Submodule.span ℝ (C : Set V) := outside.2
  obtain ⟨q, point, determines⟩ :=
    rationalCone_exists_integral_interior (fan.isToricCone maximal.1).rational
  obtain ⟨t, positive, sameStar⟩ := exists_positive_motion_same_star fan (i q) v
  obtain ⟨D, hD, moved⟩ := (Fan.isComplete_iff fan).mp complete (i q + t • v)
  have pointD := sameStar D hD moved
  have C_le_D : C ≤ D :=
    (determines (C ⊓ D) (fan.inf_isFaceOf_left maximal.1 hD) ⟨point, pointD⟩).trans inf_le_right
  have D_le_C : D ≤ C := maximal.2 hD C_le_D
  have scaled : t • v ∈ Submodule.span ℝ (C : Set V) := by
    have h := (Submodule.span ℝ (C : Set V)).sub_mem
      (Submodule.subset_span (D_le_C moved)) (Submodule.subset_span point)
    simpa only [add_sub_cancel_left] using h
  apply vOutside
  have h := (Submodule.span ℝ (C : Set V)).smul_mem t⁻¹ scaled
  rwa [smul_smul, inv_mul_cancel₀ positive.ne', one_smul] at h

/-- Every cone is a face of a full-dimensional cone in a complete fan. -/
theorem exists_fullDimensional_supercone (complete : fan.IsComplete)
    {C : PointedCone ℝ V} (member : C ∈ fan.cones) :
    ∃ D ∈ fan.cones, C.IsFaceOf D ∧ Submodule.span ℝ (D : Set V) = ⊤ := by
  obtain ⟨D, C_le_D, maximal⟩ := fan.finite_cones.exists_le_maximal member
  exact ⟨D, maximal.1, fan.isFaceOf_of_le maximal.1 member C_le_D,
    maximalCone_span_eq_top fan complete maximal⟩

theorem exists_rankDimension_supercone (complete : fan.IsComplete)
    {C : PointedCone ℝ V} (member : C ∈ fan.cones) :
    ∃ D ∈ fan.cones, C.IsFaceOf D ∧ coneDimension D = Module.finrank ℤ N := by
  obtain ⟨D, hD, face, spans⟩ := exists_fullDimensional_supercone fan complete member
  refine ⟨D, hD, face, ?_⟩
  dsimp [coneDimension]
  rw [spans, finrank_top, fan.lattice.finrank_eq]

/-- In a complete fan, regularity of the full-dimensional cones implies
regularity of every cone. -/
theorem regular_of_fullDimensional (complete : fan.IsComplete)
    (regular : ∀ D ∈ fan.cones, Submodule.span ℝ (D : Set V) = ⊤ → IsRegularCone i D) :
    fan.IsRegular := by
  apply Fan.isRegular_iff.mpr
  intro C hC
  obtain ⟨D, hD, face, full⟩ := exists_fullDimensional_supercone fan complete hC
  exact (regular D hD full).of_isFaceOf face

end ToricPower.FanSubdivision
end
