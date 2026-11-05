module

public import Ellipsoid.SupportGeometry
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Equivalence with arbitrary invertible affine images of the ball

The principal development uses positive semiaxes and an orthogonal frame.
This file proves that every invertible real affine image of the Euclidean
ball has exactly such a representation.  The factorization is derived from
the spectral theorem for the genuine Gram operator `A† A`; no simple-spectrum
or singular-value decomposition hypothesis is introduced.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace EllipsoidVerification

def positiveAxisLinearEquiv {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Space n ≃ₗ[ℝ] Space n where
  __ := axisLinear a
  invFun := axisMap (fun i => (a i)⁻¹)
  left_inv x := by
    ext i
    simp [axisLinear, axisMap, (ha i).ne', ← mul_assoc]
  right_inv x := by
    ext i
    simp [axisLinear, axisMap, (ha i).ne', ← mul_assoc]

theorem exists_orthogonal_axis_factorization {n : ℕ}
    (A : Space n ≃ₗ[ℝ] Space n) :
    ∃ (a : Fin n → ℝ), (∀ i, 0 < a i) ∧
      ∃ U V : Space n ≃ₗᵢ[ℝ] Space n,
        ∀ x, A x = U (axisMap a (V x)) := by
  let T : Space n →ₗ[ℝ] Space n := A.toLinearMap.adjoint.comp A.toLinearMap
  have hT : T.IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self A.toLinearMap
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  let b : OrthonormalBasis (Fin n) ℝ (Space n) := hT.eigenvectorBasis hdim
  let a : Fin n → ℝ := fun i => ‖A (b i)‖
  have ha (i : Fin n) : 0 < a i := by
    apply norm_pos_iff.mpr
    intro hi
    have hz : A (b i) = A 0 := by simpa only [map_zero] using hi
    exact b.orthonormal.ne_zero i (A.injective hz)
  have horthA {i j : Fin n} (hij : i ≠ j) : ⟪A (b i), A (b j)⟫_ℝ = 0 := by
    calc
      _ = ⟪b i, T (b j)⟫_ℝ :=
        (LinearMap.adjoint_inner_right A.toLinearMap (b i) (A (b j))).symm
      _ = ⟪b i, (hT.eigenvalues hdim j) • b j⟫_ℝ := by
        rw [show T (b j) = (hT.eigenvalues hdim j) • b j from
          hT.apply_eigenvectorBasis hdim j]
      _ = 0 := by
        rw [real_inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j,
          if_neg hij, mul_zero]
  let w : Fin n → Space n := fun i => (a i)⁻¹ • A (b i)
  have hw : Orthonormal ℝ w := by
    constructor
    · intro i
      simp only [w, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha i).le)]
      exact inv_mul_cancel₀ (ha i).ne'
    · intro i j hij
      simp only [w, real_inner_smul_left, real_inner_smul_right, horthA hij, mul_zero]
  have hwr : Orthonormal ℝ ((univ : Set (Fin n)).domRestrict w) :=
    hw.comp _ Subtype.val_injective
  obtain ⟨c, hc⟩ := hwr.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (Space n) = Fintype.card (Fin n) by simpa using hdim)
  have hc' (i : Fin n) : c i = w i := hc i (mem_univ i)
  have hcol (i : Fin n) : A (b i) = a i • c i := by
    rw [hc']
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ (ha i).ne', one_smul]
  refine ⟨a, ha, c.repr.symm, b.repr, ?_⟩
  intro x
  calc
    A x = A (∑ i, b.repr x i • b i) := congrArg A (b.sum_repr x).symm
    _ = ∑ i, b.repr x i • A (b i) := by rw [map_sum]; simp only [map_smul]
    _ = ∑ i, (a i * b.repr x i) • c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcol, smul_smul, mul_comm]
    _ = c.repr.symm (axisMap a (b.repr x)) := by
      simpa only [axisMap, PiLp.toLp_apply] using c.sum_repr_symm (axisMap a (b.repr x))

/-- Coverage of the customary affine-image definition by the semiaxis
parameterization used in the principal theorem. -/
theorem exists_fullEllipsoid_of_affineBall {n : ℕ} (center : Space n)
    (A : Space n ≃ₗ[ℝ] Space n) :
    ∃ E : FullEllipsoid n,
      E.body = (fun x => center + A x) '' Metric.closedBall 0 1 := by
  obtain ⟨a, ha, U, V, hA⟩ := exists_orthogonal_axis_factorization A
  let E : FullEllipsoid n := ⟨center, U, a, ha⟩
  refine ⟨E, ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨V.symm x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, V.symm.norm_map] using hx
    · change center + A (V.symm x) = center + U (axisMap a x)
      rw [hA, V.apply_symm_apply]
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨V x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, V.norm_map] using hx
    · change center + U (axisMap a (V x)) = center + A x
      rw [hA]

/-- Every object used by the formalized theorem is also an invertible affine
image of the ball. Together with the previous theorem this gives both
directions of the geometric parameterization equivalence. -/
theorem FullEllipsoid.exists_affineBallParameterization {n : ℕ} (E : FullEllipsoid n) :
    ∃ (center : Space n) (A : Space n ≃ₗ[ℝ] Space n),
      E.body = (fun x => center + A x) '' Metric.closedBall 0 1 := by
  refine ⟨E.center,
    (positiveAxisLinearEquiv E.semiaxis E.semiaxis_pos).trans E.frame.toLinearEquiv, ?_⟩
  rfl

end EllipsoidVerification
