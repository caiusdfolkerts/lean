module

public import VolumePolynomials.RationalCoefficientNets
public import VolumePolynomials.ExplicitNormalization
public import VolumePolynomials.EnumeratedQuadraticMatrices

@[expose] public section
set_option autoImplicit false

/-!
# The rational quadratic characterization

This file connects the certified executable finite nets to the literal
volume-polynomial realization locus. The normalization is the proved affine
normalization of actual convex bodies, and nonnegativity comes from the full
volume-polynomial existence theorem. No geometric or computational premise
is added to the final characterization.
-/

open Set
open scoped BigOperators Pointwise

namespace VolumePolynomials

theorem normalized_mem_explicit_boundedLocus {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} (hc : c ∈ VolumeLocus n d) (hs : 0 < ∑ α, c α) :
    (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ))) := by
  first
  | have hn := smul_mem_volumeLocus hd hc (inv_nonneg.mpr hs.le)
    obtain ⟨K, hK⟩ := hn
    have hsum : ∑ α, ((∑ β, c β)⁻¹ • c) α = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    have hvol : bodyVolume (∑ i, K i) = 1 := hK.sum_coefficients.symm.trans hsum
    obtain ⟨g, p, hg, hp, h0, hbox⟩ := explicit_normalization hd K hvol
    let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
    have hL : Realizes L ((∑ α, c α)⁻¹ • c) :=
      (hK.translate (fun i => -p i)).map_of_abs_det_one g hg
    refine ⟨L, ?_, hL⟩
    intro i
    exact ⟨h0 i, fun x hx => hbox (body_le_sum_of_zero_mem L h0 i hx)⟩

namespace Main

open QuadraticSeparation

/-- At every natural-number index this returns the actual rational
coefficients of a homogeneous quadratic form. -/
def volumeInequalityMatrix (n d k : ℕ) : MultiIndex n d → MultiIndex n d → ℚ :=
  enumeratedRationalMatrix (RationalCoefficientNets.model n d d) k

/-- The equivalent semantic multivariate polynomial. Its matrix coefficients
are given by the executable definition above. -/
noncomputable def volumeInequalityPolynomial (n d k : ℕ) : MvPolynomial (MultiIndex n d) ℚ :=
  enumeratedForm (RationalCoefficientNets.model n d d) k

theorem volumeInequalityPolynomial_homogeneous (n d k : ℕ) :
    (volumeInequalityPolynomial n d k).IsHomogeneous 2 :=
  enumeratedForm_isHomogeneous _ _

theorem volumeInequalityMatrix_eval (n d k : ℕ) (c : Coefficients n d) :
    (∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  enumeratedRationalMatrix_eval _ _ (WithLp.toLp 2 c)

/-- Theorem 1.3, in executable rational-matrix form, for every number of
bodies and every positive ambient dimension. Every coefficient, every real
nonnegative Minkowski weight, and every realization is retained. -/
theorem volumeLocus_iff_countableQuadratics (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ ∑ α, ∑ β, (volumeInequalityMatrix n d k α β : ℝ) * c α * c β := by
  first
  | let V : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
      {x | WithLp.ofLp x ∈ VolumeLocus n d}
    have hzero : (0 : QuadraticSeparation.Space (MultiIndex n d)) ∈ V :=
      zero_mem_volumeLocus hd
    have hnonneg : ∀ x ∈ V, ∀ α, 0 ≤ x α := by
      intro x hx α
      obtain ⟨K, hK⟩ := hx
      exact hK.coefficients_nonnegative α
    have hnormalize : ∀ x ∈ V, x ≠ 0 →
        normalize x ∈ (RationalCoefficientNets.model n d d).target := by
      intro x hx hx0
      have hs : 0 < total x := total_pos (hnonneg x hx) hx0
      have h := normalized_mem_explicit_boundedLocus hd hx hs
      exact ⟨(total x)⁻¹ • WithLp.ofLp x, h, rfl⟩
    have hrealize : ∀ x, 0 < total x →
        normalize x ∈ (RationalCoefficientNets.model n d d).target → x ∈ V := by
      intro x hs hx
      obtain ⟨y, hy, hyeq⟩ := hx
      have hnorm : WithLp.ofLp (normalize x) ∈ VolumeLocus n d := by
        rw [← hyeq]
        exact boundedVolumeLocus_subset n d _ hy
      have h := smul_mem_volumeLocus hd hnorm hs.le
      change (total x) • ((total x)⁻¹ • WithLp.ofLp x) ∈ VolumeLocus n d at h
      change WithLp.ofLp x ∈ VolumeLocus n d
      simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using h
    exact countable_matrix_characterization (RationalCoefficientNets.model n d d)
      V hzero hnonneg hnormalize hrealize (WithLp.toLp 2 c)

/-- The original polynomial formulation of the same exact characterization. -/
theorem volumeLocus_iff_enumeratedPolynomials (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) :
    c ∈ VolumeLocus n d ↔
      (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
        0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) := by
  first
  | rw [volumeLocus_iff_countableQuadratics n d hd]
    simp only [volumeInequalityMatrix_eval]

/-- The complete countable homogeneous rational quadratic family in Theorem 1.3.
Its actual rational coefficients are computed by `volumeInequalityMatrix`. -/
theorem countable_characterization (n d : ℕ) (hd : 0 < d) :
    (∀ k, (volumeInequalityPolynomial n d k).IsHomogeneous 2) ∧
      ∀ c : Coefficients n d, c ∈ VolumeLocus n d ↔
        (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) :=
  ⟨volumeInequalityPolynomial_homogeneous n d,
    volumeLocus_iff_enumeratedPolynomials n d hd⟩

end Main
end VolumePolynomials
