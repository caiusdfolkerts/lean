module
public import VolumePolynomials.HyperbolicForm
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The finite-dimensional Bochner reduction

This is the spectral step in the polytope proof of Alexandrov–Fenchel. All
operator hypotheses are explicit; a geometric application must prove them for
its actual mixed-volume operator. No geometric theorem is asserted here.
-/

namespace VolumePolynomials

open LinearMap Module
open scoped BigOperators RealInnerProductSpace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Bochner inequality and a simple maximal eigenvalue one imply that the
quadratic form is nonpositive on the ordinary orthogonal complement of its
one-eigenvector. This uses Mathlib's full finite-dimensional spectral theorem. -/
theorem finite_bochner_nonpos_orthogonal (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (e : E)
    (hmax : ∀ (r : ℝ) (v : E), v ≠ 0 → T v = r • v → r ≤ 1)
    (hsimple : ∀ v : E, T v = v → ∃ c : ℝ, v = c • e)
    (hbochner : ∀ v : E, ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ)
    (x : E) (hxe : ⟪x, e⟫_ℝ = 0) : ⟪T x, x⟫_ℝ ≤ 0 := by
  first
  | classical
    let b := hT.eigenvectorBasis (n := finrank ℝ E) rfl
    let ev := hT.eigenvalues (n := finrank ℝ E) rfl
    have heig : ∀ i, T (b i) = ev i • b i := hT.apply_eigenvectorBasis rfl
    have hle : ∀ i, ev i ≤ 1 := fun i =>
      hmax (ev i) (b i) (b.toBasis.ne_zero i) (heig i)
    have hsq : ∀ i, ev i ≤ (ev i) ^ 2 := by
      first
      | intro i
        have h := hbochner (b i)
        simp only [heig, real_inner_smul_left, real_inner_smul_right] at h
        simpa only [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one,
          pow_two] using h
    have hterm : ∀ i, ev i * (b.repr x i) ^ 2 ≤ 0 := by
      first
      | intro i
        by_cases hi : ev i ≤ 0
        · exact mul_nonpos_of_nonpos_of_nonneg hi (sq_nonneg _)
        · have hpos : 0 < ev i := lt_of_not_ge hi
          have hge : 1 ≤ ev i := by
            by_contra h
            have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
            nlinarith [hsq i]
          have heq : ev i = 1 := le_antisymm (hle i) hge
          obtain ⟨c, hc⟩ := hsimple (b i) (by rw [heig, heq, one_smul])
          have hcoord : b.repr x i = 0 := by
            rw [b.repr_apply_apply, hc, real_inner_smul_left,
              real_inner_comm x e, hxe, mul_zero]
          simp only [hcoord, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    have hquad : ⟪T x, x⟫_ℝ = ∑ i, ev i * (b.repr x i) ^ 2 := by
      first
      | rw [← b.sum_inner_mul_inner (T x) x]
        apply Finset.sum_congr rfl
        intro i _
        rw [hT x (b i), heig, real_inner_smul_right,
          real_inner_comm (b i) x, b.repr_apply_apply]
        ring
    rw [hquad]
    exact Finset.sum_nonpos (fun i _ => hterm i)

/-- The finite Bochner hypotheses imply the full reverse Cauchy–Schwarz
inequality for the associated bilinear form, including its null boundary. -/
theorem finite_bochner_reverse_cauchy_schwarz (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (e : E) (he : T e = e)
    (hmax : ∀ (r : ℝ) (v : E), v ≠ 0 → T v = r • v → r ≤ 1)
    (hsimple : ∀ v : E, T v = v → ∃ c : ℝ, v = c • e)
    (hbochner : ∀ v : E, ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ)
    (x y : E) (hy : 0 ≤ ⟪T y, y⟫_ℝ) :
    ⟪T x, x⟫_ℝ * ⟪T y, y⟫_ℝ ≤ ⟪T x, y⟫_ℝ ^ 2 := by
  first
  | let B : LinearMap.BilinForm ℝ E := LinearMap.comp (innerₗ E) T
    have hB : ∀ v w, B v w = B w v := by
      first
      | intro v w
        change ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ
        rw [hT v w, real_inner_comm (T w) v]
    have hperp : ∀ v, B v e = 0 → B v v ≤ 0 := by
      first
      | intro v hv
        change ⟪T v, e⟫_ℝ = 0 at hv
        rw [hT v e, he] at hv
        exact finite_bochner_nonpos_orthogonal T hT e hmax hsimple hbochner v hv
    exact bilinear_reverse_cauchy_schwarz B hB e hperp x y hy

end VolumePolynomials
