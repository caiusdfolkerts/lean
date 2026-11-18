module
public import VolumePolynomials.BodyNormalization
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false

/-!
# The explicit normalization box

The maximal-simplex coordinates bound the image by the unit cube. The coordinate
simplex contains the cube of side `1/d`; its elementary product volume suffices
to obtain the paper's final radius `d`, without needing a simplex-volume formula.
-/

noncomputable section
open Set MeasureTheory Finset Metric
open scoped Pointwise BigOperators ENNReal

namespace VolumePolynomials

def droppedCoordinateMap {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d →ᵃ[ℝ] Space d := AffineMap.pi (fun i => b.coord i.succ)

@[simp] theorem droppedCoordinateMap_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateMap b x i = b.coord i.succ x := rfl

theorem droppedCoordinateMap_bijective {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Function.Bijective (droppedCoordinateMap b) := by
  first
  | constructor
    · intro x y hxy
      apply b.ext_elem
      intro i
      cases i using Fin.cases with
      | zero =>
          have hx := b.sum_coord_apply_eq_one x
          have hy := b.sum_coord_apply_eq_one y
          rw [Fin.sum_univ_succ] at hx hy
          have hh : (∑ j : Fin d, b.coord j.succ x) = ∑ j : Fin d, b.coord j.succ y := by
            first
            | apply Finset.sum_congr rfl
              intro j _
              exact congrFun hxy j
          linarith
      | succ j => exact congrFun hxy j
    · intro y
      let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
      have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
      refine ⟨Finset.univ.affineCombination ℝ b w, ?_⟩
      funext i
      exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
        (by simp [w])

def droppedCoordinateEquiv {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) :
    Space d ≃ᵃ[ℝ] Space d := AffineEquiv.ofBijective (droppedCoordinateMap_bijective b)

@[simp] theorem droppedCoordinateEquiv_apply {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (x : Space d) (i : Fin d) :
    droppedCoordinateEquiv b x i = b.coord i.succ x := rfl

@[simp] theorem droppedCoordinateEquiv_zero_vertex {d : ℕ}
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) : droppedCoordinateEquiv b (b 0) = 0 := by
  first
  | funext i
    simp [b.coord_apply_ne i.succ_ne_zero]

theorem smallCube_subset_coordinate_image {d : ℕ} (hd : 0 < d) (K : Body d)
    (b : AffineBasis (Fin (d + 1)) ℝ (Space d)) (hb : ∀ i, b i ∈ K) :
    Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹) ⊆ droppedCoordinateEquiv b '' (K : Set (Space d)) := by
  first
  | classical
    intro y hy
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hsum : ∑ i, y i ≤ 1 := by
      first
      | calc
          ∑ i, y i ≤ ∑ _i : Fin d, (d : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hy.2 i)
          _ = 1 := by simp [hdpos.ne']
    let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
    have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_succ]
    have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ w i := by
      first
      | intro i _
        cases i using Fin.cases with
        | zero => exact sub_nonneg.mpr hsum
        | succ i => exact hy.1 i
    let x := Finset.univ.affineCombination ℝ b w
    have hx : x ∈ K := (convexHull_min (Set.range_subset_iff.mpr hb) K.convex)
      (affineCombination_mem_convexHull hw0 hw)
    refine ⟨x, hx, ?_⟩
    funext i
    exact (b.coord_apply_combination_of_mem (Finset.mem_univ i.succ) hw).trans
      (by simp [w])

/-- Lemma 2.3's actual affine normalization, including its common determinant-one
linear map and the bound on the whole Minkowski sum. -/
theorem explicit_normalization {n d : ℕ} (hd : 0 < d) (K : Fin n → Body d)
    (hvol : bodyVolume (∑ i, K i) = 1) :
    ∃ (g : Space d →L[ℝ] Space d) (p : Fin n → Space d),
      |LinearMap.det g.toLinearMap| = 1 ∧ (∀ i, p i ∈ K i) ∧
      let L : Fin n → Body d := fun i => mapBody g (translateBody (-p i) (K i))
      (∀ i, (0 : Space d) ∈ L i) ∧
        ((∑ i, L i : Body d) : Set (Space d)) ⊆
          Icc (fun _ => -(d : ℝ)) (fun _ => (d : ℝ)) := by
  first
  | classical
    let S : Body d := ∑ i, K i
    have hSpos : 0 < volume (S : Set (Space d)) := by
      first
      | have ht : 0 < (volume (S : Set (Space d))).toReal := by
          first
          | change 0 < bodyVolume S
            rw [show bodyVolume S = 1 from hvol]
            exact zero_lt_one
        exact (ENNReal.toReal_pos_iff.mp ht).1
    have hspan : affineSpan ℝ (S : Set (Space d)) = ⊤ :=
      (S.convex.addHaar_pos_iff_affineSpan_eq_top (μ := volume)).mp hSpos
    obtain ⟨b, hb, hcoord⟩ := S.isCompact.exists_affineBasis_abs_coord_le_one
      (ι := Fin (d + 1)) hspan (by simp [Space])
    let T : Space d ≃ᵃ[ℝ] Space d := droppedCoordinateEquiv b
    let f : Space d →L[ℝ] Space d := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
    let D : ℝ := |LinearMap.det f.toLinearMap|
    have hTD : volume.real (T '' (S : Set (Space d))) = D := by
      first
      | rw [bodyVolume_affine_image, show bodyVolume S = 1 from hvol, mul_one]
        rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hlow : ((d : ℝ)⁻¹) ^ d ≤ D := by
      first
      | rw [← hTD]
        have h := measureReal_mono (smallCube_subset_coordinate_image hd S b hb)
          (show volume (T '' (S : Set (Space d))) ≠ ∞ from by
            rw [affine_image_eq_translate_linear_image]
            exact (translateBody (T 0) (mapBody f S)).isCompact.measure_lt_top.ne)
        have hcube : volume.real (Icc (0 : Space d) (fun _ => (d : ℝ)⁻¹)) =
            ((d : ℝ)⁻¹) ^ d := by
          first
          | rw [measureReal_def, Real.volume_Icc_pi_toReal
              (show (0 : Space d) ≤ (fun _ => (d : ℝ)⁻¹) from
                fun _ => inv_nonneg.mpr hdpos.le)]
            simp
        rwa [hcube] at h
    have hD : 0 < D := (pow_pos (inv_pos.mpr hdpos) d).trans_le hlow
    let a : ℝ := D ^ (-((d : ℝ)⁻¹))
    have ha : 0 < a := Real.rpow_pos_of_pos hD _
    have hapow : a ^ d = D⁻¹ := by
      first
      | dsimp [a]
        rw [Real.rpow_neg hD.le, inv_pow, Real.rpow_inv_natCast_pow hD.le hd.ne']
    have had : a ≤ d := by
      first
      | apply (pow_le_pow_iff_left₀ ha.le hdpos.le hd.ne').mp
        rw [hapow]
        have hinv := (inv_le_inv₀ hD (pow_pos (inv_pos.mpr hdpos) d)).mpr hlow
        simpa only [inv_pow, inv_inv] using hinv
    let g : Space d →L[ℝ] Space d := a • f
    have hg : |LinearMap.det g.toLinearMap| = 1 := by
      first
      | change |LinearMap.det (a • f.toLinearMap)| = 1
        rw [LinearMap.det_smul, abs_mul, abs_pow, abs_of_pos ha]
        have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
        rw [hdim]
        change a ^ d * D = 1
        rw [hapow, inv_mul_cancel₀ hD.ne']
    obtain ⟨p, hp, hpsum⟩ := (mem_sum_body K (b 0)).mp (hb 0)
    let P : Fin n → Body d := fun i => translateBody (-p i) (K i)
    have hP0 : ∀ i, (0 : Space d) ∈ P i := by
      first
      | intro i
        simpa [P, mem_translateBody] using hp i
    have hPsum : ∑ i, P i = translateBody (-(b 0)) S := by
      first
      | simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib, hpsum, P, S] using
          weightedSum_translate K (fun i => -p i) (fun _ => 1)
    refine ⟨g, p, hg, hp, ?_⟩
    constructor
    · intro i
      exact ⟨0, hP0 i, map_zero g⟩
    · intro y hy
      have hmapsum : (∑ i, mapBody g (P i)) = mapBody g (∑ i, P i) :=
        (map_sum (mapBodyHom g) P Finset.univ).symm
      change y ∈ ∑ i, mapBody g (P i) at hy
      rw [hmapsum] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hPsum] at hu
      change u ∈ translateBody (-(b 0)) S at hu
      rw [mem_translateBody, sub_neg_eq_add] at hu
      have hfu : f u = T (u + b 0) := by
        first
        | change T.linear u = T (u + b 0)
          have h := T.map_vadd (b 0) u
          simpa only [vadd_eq_add, T, droppedCoordinateEquiv_zero_vertex, add_zero] using h.symm
      have hbound : ∀ j, |g u j| ≤ d := by
        first
        | intro j
          have hc : |f u j| ≤ 1 := by
            first
            | rw [hfu]
              exact hcoord (u + b 0) hu j.succ
          change |a * f u j| ≤ d
          rw [abs_mul, abs_of_pos ha]
          exact (mul_le_of_le_one_right ha.le hc).trans had
      exact ⟨fun j => (abs_le.mp (hbound j)).1, fun j => (abs_le.mp (hbound j)).2⟩

end VolumePolynomials
