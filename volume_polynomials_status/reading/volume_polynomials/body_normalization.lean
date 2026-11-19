module
public import VolumePolynomials.RealizationCone
public import TauCeti.Analysis.Convex.AffineNormalization
public import TauCeti.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

set_option autoImplicit false

/-!
# Uniform normalization of actual realizing tuples

This is a geometric compactness normalization. Its radius depends only on the
ambient dimension. It is deliberately distinct from the explicit numerical
radius needed by the paper's computable grid construction.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem affine_image_eq_translate_linear_image {d : ℕ}
    (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    T '' (K : Set (Space d)) =
      (translateBody (T 0) (mapBody T.linear.toContinuousLinearEquiv.toContinuousLinearMap K) :
        Set (Space d)) := by
  first
  | ext y
    simp only [coe_translateBody, coe_mapBody, Set.mem_vadd_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T.linear x, ⟨x, hx, rfl⟩, ?_⟩
      simpa only [vadd_eq_add, add_zero, add_comm] using (T.map_vadd 0 x).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change T x = T 0 + T.linear x
      simpa only [vadd_eq_add, add_zero, add_comm] using T.map_vadd 0 x

theorem bodyVolume_affine_image {d : ℕ} (T : Space d ≃ᵃ[ℝ] Space d) (K : Body d) :
    volume.real (T '' (K : Set (Space d))) =
      |LinearMap.det T.linear.toLinearMap| * bodyVolume K := by
  first
  | rw [affine_image_eq_translate_linear_image]
    change bodyVolume (translateBody _ (mapBody _ K)) = _
    rw [bodyVolume_translate, bodyVolume_map]
    rfl

/-- Every total-volume-one realization admits independently translated bodies
and a common linear volume normalization inside a fixed ball. No coefficient
positivity or polynomial-existence assertion is used as an assumption. -/
theorem exists_uniform_normalization (d : ℕ) (hd : 0 < d) :
    ∃ R > 0, ∀ (n : ℕ) (K : Fin n → Body d) (c : Coefficients n d),
      Realizes K c → (∑ α, c α) = 1 →
      ∃ L : Fin n → Body d, Realizes L c ∧
        ∀ i, (0 : Space d) ∈ L i ∧ (L i : Set (Space d)) ⊆ closedBall 0 R := by
  first
  | classical
    obtain ⟨r, hr, hnormal⟩ :=
      TauCeti.exists_affineEquiv_ball_subset_image_subset_ball (Space d)
    let m : ℝ := volume.real (ball (0 : Space d) r)
    have hm : 0 < m := ENNReal.toReal_pos (measure_ball_pos volume 0 hr).ne' measure_ball_ne_top
    let q : ℝ := m ^ (-((d : ℝ)⁻¹))
    have hq : 0 < q := Real.rpow_pos_of_pos hm _
    refine ⟨2 * q, mul_pos zero_lt_two hq, ?_⟩
    intro n K c hK hc
    let S : Body d := ∑ i, K i
    have hSvol : bodyVolume S = 1 := hK.sum_coefficients.symm.trans hc
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          change 0 < bodyVolume S
          rw [hSvol]
          exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    obtain ⟨T, hsmall, hlarge⟩ := hnormal (S : Set (Space d)) S.convex S.isBounded
      ((S.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).mp hSpos)
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, hSvol, mul_one]
        rfl
    have hmD : m ≤ D := by
      first
      | rw [← hTD]
        exact measureReal_mono hsmall (by
          rw [affine_image_eq_translate_linear_image]
          exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
    have hD : 0 < D := hm.trans_le hmD
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have haq : a ≤ q := Real.rpow_le_rpow_of_nonpos hm hmD
      (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg d)))
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    choose p hp using fun i => (K i).nonempty
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hpsum : (∑ i, p i) ∈ S := by
      first
      | exact (mem_sum_body K _).mpr ⟨p, hp, rfl⟩
    have hPsum : ∑ i, P i = translateBody (-(∑ i, p i)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    have hfnorm : ∀ u ∈ (∑ i, P i : Body d), ‖f u‖ < 2 := by
      first
      | intro u hu
        rw [hPsum, mem_translateBody, sub_neg_eq_add] at hu
        have h₁ := hlarge (Set.mem_image_of_mem T hu)
        have h₂ := hlarge (Set.mem_image_of_mem T hpsum)
        rw [mem_ball_zero_iff] at h₁ h₂
        have hfu : f u = T (u + ∑ i, p i) - T (∑ i, p i) := by
          apply eq_sub_iff_add_eq.mpr
          change T.linear u + T (∑ i, p i) = T (u + ∑ i, p i)
          simpa only [vadd_eq_add] using (T.map_vadd (∑ i, p i) u).symm
        rw [hfu]
        exact (norm_sub_le _ _).trans_lt (by linarith)
    let L : Fin n → Body d := fun i => a • mapBody f (P i)
    have hreal : Realizes L c := by
      first
      | have h := ((hK.translate (fun i => -p i)).map f).dilate ha.le
        have hscale : a ^ d • (D • c) = c := by
          rw [smul_smul, hapow, inv_mul_cancel₀ hD.ne', one_smul]
        change Realizes L (a ^ d • (D • c)) at h
        rwa [hscale] at h
    refine ⟨L, hreal, fun i => ⟨?_, ?_⟩⟩
    · change (0 : Space d) ∈ a • (mapBody f (P i) : Set (Space d))
      exact ⟨0, ⟨0, hP0 i, map_zero f⟩, smul_zero _⟩
    · rintro y ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ha.le]
      have huS := body_le_sum_of_zero_mem P hP0 i hu
      have hbound := hfnorm u huS
      calc
        a * ‖f u‖ ≤ a * 2 := mul_le_mul_of_nonneg_left hbound.le ha.le
        _ ≤ q * 2 := mul_le_mul_of_nonneg_right haq zero_le_two
        _ = 2 * q := mul_comm _ _

end VolumePolynomials
