module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.Order.Compact
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-! # Bounded polyhedra with trivial recession cone

A finite family of linear inequalities has a bounded solution set whenever
its homogeneous inequalities have only the zero solution. The proof uses
the positive minimum on the unit sphere of the sum of positive parts of
the linear forms. It applies also in dimension zero and to an empty family
of inequalities, without an assumed nonempty polyhedron.

Intersecting a bounded set with the literal discrete integral lattice then
gives a finite set of integral solutions.
-/

@[expose] public noncomputable section

open scoped Classical BigOperators
open TauCeti.Toric

namespace ToricPower

section Boundedness

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype J]

/-- Triviality of the homogeneous inequality cone forces boundedness of
every affine solution polyhedron with those same normal forms. -/
theorem finiteHalfspaceIntersection_bounded
    (form : J → E →ₗ[ℝ] ℝ) (bound : J → ℝ)
    (recession_zero : ∀ x : E, (∀ j, form j x ≤ 0) → x = 0) :
    Bornology.IsBounded {x : E | ∀ j, form j x ≤ bound j} := by
  let positivePart (x : E) : ℝ := ∑ j : J, max 0 (form j x)
  have continuousPart : Continuous positivePart := by
    apply continuous_finset_sum
    intro j _
    exact continuous_const.max (form j).continuous_of_finiteDimensional
  have positive (x : E) (nonzero : x ≠ 0) : 0 < positivePart x := by
    have existsPositive : ∃ j, 0 < form j x := by
      by_contra h
      push_neg at h
      exact nonzero (recession_zero x h)
    obtain ⟨j, hj⟩ := existsPositive
    exact (hj.trans_le (le_max_right _ _)).trans_le
      (Finset.single_le_sum (fun j _ => le_max_left 0 (form j x)) (Finset.mem_univ j))
  have homogeneous (r : ℝ) (hr : 0 ≤ r) (x : E) :
      positivePart (r • x) = r * positivePart x := by
    unfold positivePart
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul, mul_max_of_nonneg _ _ hr, mul_zero]
  obtain ⟨ε, epsilon_pos, minimum⟩ :=
    (isCompact_sphere (0 : E) 1).exists_forall_le' continuousPart.continuousOn (by
      intro x hx
      apply positive x
      intro hx0
      have hnorm := mem_sphere_zero_iff_norm.mp hx
      rw [hx0, norm_zero] at hnorm
      exact zero_ne_one hnorm)
  let totalBound : ℝ := ∑ j : J, max 0 (bound j)
  have total_nonnegative : 0 ≤ totalBound := Finset.sum_nonneg
    (fun j _ => le_max_left 0 (bound j))
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨totalBound / ε, ?_⟩
  intro x hx
  by_cases zero : x = 0
  · rw [zero, norm_zero]
    exact div_nonneg total_nonnegative epsilon_pos.le
  · have norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr zero
    have lower := minimum (‖x‖⁻¹ • x)
      (mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm zero))
    rw [homogeneous _ (inv_nonneg.mpr norm_pos.le)] at lower
    have scaled := mul_le_mul_of_nonneg_left lower norm_pos.le
    rw [← mul_assoc, mul_inv_cancel₀ norm_pos.ne', one_mul] at scaled
    have upper : positivePart x ≤ totalBound := by
      apply Finset.sum_le_sum
      intro j _
      exact max_le_max le_rfl (hx j)
    apply (le_div_iff₀ epsilon_pos).mpr
    have scaled' : ‖x‖ * ε ≤ positivePart x := by
      simpa only [mul_comm] using scaled
    exact scaled'.trans upper

end Boundedness

section LatticePoints

variable {N E : Type*} [AddCommGroup N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {embedding : N →+ E}

/-- Finiteness uses discreteness of a genuine integral lattice; injectivity
and real spanning by themselves would not suffice. -/
theorem integralLattice_preimage_finite_of_bounded
    (lattice : IsIntegralLattice embedding) {region : Set E}
    (bounded : Bornology.IsBounded region) :
    (embedding ⁻¹' region).Finite := by
  letI := lattice.finiteDimensional
  letI := lattice.discreteTopology
  let image : Submodule ℤ E := LinearMap.range embedding.toIntLinearMap
  have closed : IsClosed (image : Set E) := by
    exact image.toAddSubgroup.isClosed_of_discreteTopology
  have discrete : IsDiscrete (image : Set E) := DiscreteTopology.isDiscrete
  have finite := Metric.finite_isBounded_inter_isClosed discrete bounded closed
  have result := finite.preimage (f := embedding) lattice.injective.injOn
  convert result using 1
  ext x
  exact ⟨fun hx => ⟨hx, ⟨x, rfl⟩⟩, fun hx => hx.1⟩

end LatticePoints
end ToricPower
