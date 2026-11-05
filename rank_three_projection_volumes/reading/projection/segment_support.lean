module

public import Projection.SupportFunctions
public import Projection.Extrusion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace RankThreeProjection
open VolumePolynomials
open scoped BigOperators Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The support function of the actual centered segment, with the paper's
half-length normalization. -/
@[simp] theorem supportContinuous_centeredSegment (v : E) (u : NormalSphere E) :
    supportContinuous (centeredSegment v) u = |u.val v| / 2 := by
  exact OAI.Paper092.SupportGeometry.support_centered_segment v u.val

theorem supportContinuous_smul_real (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r)
    (u : NormalSphere E) :
    supportContinuous (r • A) u = r * supportContinuous A u :=
  Support.smul_body A u.val hr

theorem supportContinuous_sum {ι : Type*} (s : Finset ι) (A : ι → ConvexBody E)
    (u : NormalSphere E) :
    supportContinuous (∑ i ∈ s, A i) u = ∑ i ∈ s, supportContinuous (A i) u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, supportContinuous_zero, ContinuousMap.zero_apply]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, supportContinuous_add,
        ContinuousMap.add_apply, ih]

/-- The support function of a genuine Minkowski sum of marked segments. -/
theorem supportContinuous_weighted_segments {ι : Type*} [Fintype ι]
    (U : ι → E) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (u : NormalSphere E) :
    supportContinuous (∑ i, x i • centeredSegment (U i)) u =
      (1 / 2 : ℝ) * ∑ i, x i * |u.val (U i)| := by
  rw [supportContinuous_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [supportContinuous_smul_real _ (hx i), supportContinuous_centeredSegment]
  ring

end RankThreeProjection
