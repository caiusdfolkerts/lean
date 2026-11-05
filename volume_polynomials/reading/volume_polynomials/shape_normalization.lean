module
public import VolumePolynomials.ShapeTuple
public import VolumePolynomials.FrameCalibration
public import VolumePolynomials.ShapeEvaluation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.Holonomy
open ShapeConditions

@[simp] theorem weightedSum_unitWeight_pair (K : Fin 9 → Body 3) (i j : Label) :
    weightedSum K (unitWeight i + unitWeight j) = K i + K j := by
  first
  | rw [weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j)]
    simp only [weightedSum_unitWeight]

@[simp] theorem weightedSum_unitWeight_triple (K : Fin 9 → Body 3) (i j k : Label) :
    weightedSum K (unitWeight i + unitWeight j + unitWeight k) = K i + K j + K k := by
  first
  | rw [weightedSum_add K (unitWeight i + unitWeight j) (unitWeight k)
      (fun h => add_nonneg (unitWeight_nonneg i h)
      (unitWeight_nonneg j h)) (unitWeight_nonneg k)]
    simp only [weightedSum_unitWeight_pair, weightedSum_unitWeight]

@[simp] theorem volumeFunction_unitWeight_pair (K : Fin 9 → Body 3) (i j : Label) :
    volumeFunction K (unitWeight i + unitWeight j) = bodyVolume (K i + K j) := by
  first
  | simp only [volumeFunction, weightedSum_unitWeight_pair]

@[simp] theorem volumeFunction_unitWeight_triple (K : Fin 9 → Body 3) (i j k : Label) :
    volumeFunction K (unitWeight i + unitWeight j + unitWeight k) =
      bodyVolume (K i + K j + K k) := by
  first
  | simp only [volumeFunction, weightedSum_unitWeight_triple]

/-- The frame and plane constraints read from literal volume evaluations.
This is a proved consequence of `OrdinaryConditions`, not an extra hypothesis
in the eventual shape-forcing theorem. -/
structure BasicCalibration (K : Fin 9 → Body 3) : Prop where
  segmentZero : ∀ i : Fin 6, ∀ j : Fin 3,
    bodyVolume (K (segmentIndex i) + K (frameIndex j)) = 0
  frameVolume : bodyVolume (K e₁ + K e₂ + K e₃) = 1
  v₀ : bodyVolume (K sᵥ + K e₂ + K e₃) = 0
  v₁ : bodyVolume (K sᵥ + K e₁ + K e₃) = 1
  v₂ : bodyVolume (K sᵥ + K e₁ + K e₂) = 1
  w₀ : bodyVolume (K s𝓌 + K e₂ + K e₃) = 1
  w₁ : bodyVolume (K s𝓌 + K e₁ + K e₃) = 1
  w₂ : bodyVolume (K s𝓌 + K e₁ + K e₂) = 0
  z₀ : bodyVolume (K s𝓏 + K e₂ + K e₃) = 1
  z₁ : bodyVolume (K s𝓏 + K e₁ + K e₃) = (2 / 3 : ℝ)
  z₂ : bodyVolume (K s𝓏 + K e₁ + K e₂) = 1
  obliqueVolume : bodyVolume (K sᵥ + K s𝓌 + K s𝓏) = (4 / 3 : ℝ)
  planeA : bodyVolume (K bodyA + K e₁ + K e₂) = 0
  planeB : bodyVolume (K bodyB + K e₁ + K e₃) = 0
  planeC : bodyVolume (K bodyC + K e₂ + K e₃) = 0

theorem OrdinaryConditions.basicCalibration {lam a : ℝ} {K : Fin 9 → Body 3}
    (h : OrdinaryConditions lam a (volumeFunction K)) : BasicCalibration K := by
  first
  | obtain ⟨hf, hv₀, hv₁, hv₂, hw₀, hw₁, hw₂, hz₀, hz₁, hz₂,
      hs, hA, hB, hC, _⟩ := h.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simpa only [volumeFunction_unitWeight_pair] using h.1 i j
    all_goals
      first
      | simpa only [volumeFunction_unitWeight_triple] using hf
      | simpa only [volumeFunction_unitWeight_triple] using hv₀
      | simpa only [volumeFunction_unitWeight_triple] using hv₁
      | simpa only [volumeFunction_unitWeight_triple] using hv₂
      | simpa only [volumeFunction_unitWeight_triple] using hw₀
      | simpa only [volumeFunction_unitWeight_triple] using hw₁
      | simpa only [volumeFunction_unitWeight_triple] using hw₂
      | simpa only [volumeFunction_unitWeight_triple] using hz₀
      | simpa only [volumeFunction_unitWeight_triple] using hz₁
      | simpa only [volumeFunction_unitWeight_triple] using hz₂
      | simpa only [volumeFunction_unitWeight_triple] using hs
      | simpa only [volumeFunction_unitWeight_triple] using hA
      | simpa only [volumeFunction_unitWeight_triple] using hB
      | simpa only [volumeFunction_unitWeight_triple] using hC

theorem BasicCalibration.segments {K : Fin 9 → Body 3} (h : BasicCalibration K)
    (hzero : ∀ i, (0 : ThreeSpace) ∈ K i) :
    ∀ i : Fin 6, ∃ x y : ThreeSpace,
      x ∈ K (segmentIndex i) ∧ y ∈ K (segmentIndex i) ∧
      K (segmentIndex i) = segmentBody x y := by
  first
  | intro i
    obtain ⟨x, y, hx, hy, hxy⟩ := body_is_segment_of_three_zero_volumes
      (K (segmentIndex i)) (K e₁) (K e₂) (K e₃)
      (hzero _) (hzero _) (hzero _) (hzero _)
      (h.segmentZero i 0) (h.segmentZero i 1) (h.segmentZero i 2)
      (by rw [h.frameVolume]; exact zero_lt_one)
    exact ⟨x, y, hx, hy, body_eq_segmentBody hxy⟩

/-- Independent translations put every body through the origin and put an
endpoint of each of the six forced segments at the origin. -/
theorem normalize_segment_origins {lam a : ℝ} (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L : Label → Body 3, ∃ u : Fin 6 → ThreeSpace,
      AffinelyNormalized K L ∧
      (∀ i, (0 : ThreeSpace) ∈ L i) ∧
      (∀ i, L (segmentIndex i) = segmentBody 0 (u i)) ∧
      OrdinaryConditions lam a (volumeFunction L) := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let K₀ : Label → Body 3 := fun i => translateBody (-p i) (K i)
    have hK₀ : AffinelyNormalized K K₀ := AffinelyNormalized.of_translate K _
    have hz₀ : ∀ i, (0 : ThreeSpace) ∈ K₀ i :=
      fun i => zero_mem_translateBody_neg (hp i)
    have hc₀ : OrdinaryConditions lam a (volumeFunction K₀) := by
      rw [hK₀.volumeFunction_eq]
      exact hcond
    choose x y hx hy hxy using BasicCalibration.segments
      (OrdinaryConditions.basicCalibration hc₀) hz₀
    let t : Label → ThreeSpace := fun i => if h : i.val < 6 then -x ⟨i.val, h⟩ else 0
    let L : Label → Body 3 := fun i => translateBody (t i) (K₀ i)
    have hL : AffinelyNormalized K₀ L := AffinelyNormalized.of_translate K₀ t
    refine ⟨L, fun i => y i - x i, hK₀.trans hL, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < 6
      · let j : Fin 6 := ⟨i.val, hi⟩
        have hji : segmentIndex j = i := Fin.ext rfl
        have hx' : x j ∈ K₀ i := by rw [← hji]; exact hx j
        simpa only [L, t, dif_pos hi] using zero_mem_translateBody_neg hx'
      · simpa only [L, t, dif_neg hi, translateBody_zero] using hz₀ i
    · intro i
      have ht : t (segmentIndex i) = -x i := by
        simp only [t, segmentIndex, Fin.coe_castLE, dif_pos i.isLt]
      change translateBody (t (segmentIndex i)) (K₀ (segmentIndex i)) = _
      rw [ht, hxy i, translate_segmentBody, neg_add_cancel, neg_add_eq_sub]
    · rw [hL.volumeFunction_eq]
      exact hc₀

/-- A common determinant-one change of coordinates fixes the frame vectors
exactly.  Its hypotheses still concern the actual nine convex bodies. -/
theorem normalize_coordinate_frame {lam a : ℝ} (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L : Label → Body 3, ∃ u : Fin 6 → ThreeSpace,
      AffinelyNormalized K L ∧
      (∀ i, (0 : ThreeSpace) ∈ L i) ∧
      (∀ i, L (segmentIndex i) = segmentBody 0 (u i)) ∧
      (∀ i : Fin 3, u (i.castLE (by decide)) = axis i) ∧
      OrdinaryConditions lam a (volumeFunction L) := by
  first
  | obtain ⟨P, v, hKP, hzero, hseg, hP⟩ := normalize_segment_origins K hcond
    let vf : Fin 3 → ThreeSpace := fun i => v (i.castLE (by decide))
    have hframe : bodyVolume (∑ i, segmentBody 0 (vf i)) = 1 := by
      simp only [Fin.sum_univ_three, vf, ← hseg, segmentIndex]
      change bodyVolume (P e₁ + P e₂ + P e₃) = 1
      exact (OrdinaryConditions.basicCalibration hP).frameVolume
    obtain ⟨g, hg, hgv⟩ := normalize_origin_segment_frame vf hframe
    let L : Label → Body 3 := fun i => mapBody g.toContinuousLinearMap (P i)
    have hPL : AffinelyNormalized P L := AffinelyNormalized.of_map P g hg
    refine ⟨L, fun i => g (v i), hKP.trans hPL, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨0, hzero i, map_zero g⟩
    · intro i
      change mapBody g.toContinuousLinearMap (P (segmentIndex i)) = _
      rw [hseg, map_segmentBody, map_zero]
      change segmentBody (0 : Space 3) (g (v i)) = segmentBody 0 (g (v i))
      rfl
    · exact hgv
    · rw [hPL.volumeFunction_eq]
      exact hP

/-- A linear map preserving all three coordinate axes preserves each of the
three coordinate planes. -/
theorem coordinate_zero_of_axis_preserving (g : ThreeSpace →L[ℝ] ThreeSpace)
    (hg : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i)
    (x : ThreeSpace) (k : Fin 3) (hx : x k = 0) : g x k = 0 := by
  first
  | classical
    have hdecomp : x = ∑ i : Fin 3, x i • axis i := by
      ext j
      simp [axis, Pi.single_apply]
    rw [hdecomp, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨s, hs⟩ := hg i
    by_cases hik : i = k
    · subst i
      simp only [hx, zero_mul]
    · rw [hs]
      simp [axis, Pi.single_apply, hik, Ne.symm hik]

theorem mapBody_zero_mem (g : ThreeSpace →L[ℝ] ThreeSpace) {K : Body 3}
    (hK : (0 : ThreeSpace) ∈ K) : (0 : ThreeSpace) ∈ mapBody g K :=
  ⟨0, hK, map_zero g⟩

theorem mapBody_coordinate_zero (g : ThreeSpace →L[ℝ] ThreeSpace)
    (hg : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i)
    {K : Body 3} {k : Fin 3} (hK : ∀ x ∈ K, x k = 0) :
    ∀ x ∈ mapBody g K, x k = 0 := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    exact coordinate_zero_of_axis_preserving g hg x k (hK x hx)

/-- Complete calibration from the finite volume tests.  No segment, plane,
normalization, or Minkowski equality is assumed in this statement. -/
theorem normalize_shape_conditions (lam a : ℝ) (K : Label → Body 3)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ L, AffinelyNormalized K L ∧ IsCalibratedTuple L := by
  first
  | classical
    obtain ⟨Q, u, hKQ, hz, hseg, haxis, hQ⟩ := normalize_coordinate_frame K hcond
    have hc : BasicCalibration Q := OrdinaryConditions.basicCalibration hQ
    have hu₀ : u 0 = axis 0 := by
      have h := haxis 0
      change u 0 = axis 0 at h
      exact h
    have hu₁ : u 1 = axis 1 := by
      have h := haxis 1
      change u 1 = axis 1 at h
      exact h
    have hu₂ : u 2 = axis 2 := by
      have h := haxis 2
      change u 2 = axis 2 at h
      exact h
    have he₁ : Q e₁ = segmentBody 0 (axis 0) := by
      have h := hseg 0
      change Q e₁ = segmentBody 0 (u 0) at h
      exact h.trans (congrArg (segmentBody 0) hu₀)
    have he₂ : Q e₂ = segmentBody 0 (axis 1) := by
      have h := hseg 1
      change Q e₂ = segmentBody 0 (u 1) at h
      exact h.trans (congrArg (segmentBody 0) hu₁)
    have he₃ : Q e₃ = segmentBody 0 (axis 2) := by
      have h := hseg 2
      change Q e₃ = segmentBody 0 (u 2) at h
      exact h.trans (congrArg (segmentBody 0) hu₂)
    have hv : Q sᵥ = segmentBody 0 (u 3) := hseg 3
    have hw : Q s𝓌 = segmentBody 0 (u 4) := hseg 4
    have hzseg : Q s𝓏 = segmentBody 0 (u 5) := hseg 5
    have hv₀ : u 3 0 = 0 := by
      have h := hc.v₀
      simp only [hv, he₂, he₃, axis, volume_coordinate_test₁] at h
      exact abs_eq_zero.mp h
    have hv₁ : |u 3 1| = 1 := by
      simpa only [hv, he₁, he₃, axis, volume_coordinate_test₂] using hc.v₁
    have hv₂ : |u 3 2| = 1 := by
      simpa only [hv, he₁, he₂, axis, volume_coordinate_test₃] using hc.v₂
    have hw₀ : |u 4 0| = 1 := by
      simpa only [hw, he₂, he₃, axis, volume_coordinate_test₁] using hc.w₀
    have hw₁ : |u 4 1| = 1 := by
      simpa only [hw, he₁, he₃, axis, volume_coordinate_test₂] using hc.w₁
    have hw₂ : u 4 2 = 0 := by
      have h := hc.w₂
      simp only [hw, he₁, he₂, axis, volume_coordinate_test₃] at h
      exact abs_eq_zero.mp h
    have hz₀ : |u 5 0| = 1 := by
      simpa only [hzseg, he₂, he₃, axis, volume_coordinate_test₁] using hc.z₀
    have hz₁ : |u 5 1| = (2 / 3 : ℝ) := by
      simpa only [hzseg, he₁, he₃, axis, volume_coordinate_test₂] using hc.z₁
    have hz₂ : |u 5 2| = 1 := by
      simpa only [hzseg, he₁, he₂, axis, volume_coordinate_test₃] using hc.z₂
    have hd : |determinant3 (u 3) (u 4) (u 5)| = (4 / 3 : ℝ) := by
      simpa only [hv, hw, hzseg, volume_three_origin_segments] using hc.obliqueVolume
    obtain ⟨g, hg, hga, rv, rw, rz, hrv, hrw, hrz, hgv, hgw, hgz⟩ :=
      calibrate_vectors (u 3) (u 4) (u 5)
        hv₀ hv₁ hv₂ hw₀ hw₁ hw₂ hz₀ hz₁ hz₂ hd
    have hga' : ∀ i : Fin 3, ∃ s : ℝ, g (axis i) = s • axis i :=
      fun i => ⟨(hga i).choose, (hga i).choose_spec.2⟩
    have hplaneA : ∀ x ∈ Q bodyA, x 2 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyA) 0 1 2
        (by decide) (by decide) (by decide) (hz bodyA)
      simpa only [he₁, he₂, coordinateSegment, axis] using hc.planeA
    have hplaneB : ∀ x ∈ Q bodyB, x 1 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyB) 0 2 1
        (by decide) (by decide) (by decide) (hz bodyB)
      simpa only [he₁, he₃, coordinateSegment, axis] using hc.planeB
    have hplaneC : ∀ x ∈ Q bodyC, x 0 = 0 := by
      apply coordinate_eq_zero_of_volume_zero (Q bodyC) 1 2 0
        (by decide) (by decide) (by decide) (hz bodyC)
      simpa only [he₂, he₃, coordinateSegment, axis] using hc.planeC
    let R : Label → Body 3 := fun i => mapBody g.toContinuousLinearMap (Q i)
    let t : Label → ThreeSpace := fun i => if h : i.val < 6 then
      -(1 / 2 : ℝ) • g (u ⟨i.val, h⟩) else 0
    let L : Label → Body 3 := fun i => translateBody (t i) (R i)
    have hQR : AffinelyNormalized Q R := AffinelyNormalized.of_map Q g hg
    have hRL : AffinelyNormalized R L := AffinelyNormalized.of_translate R t
    refine ⟨L, (hKQ.trans hQR).trans hRL, ?_⟩
    have hLseg : ∀ i : Fin 6, L (segmentIndex i) = centeredBody (g (u i)) := by
      intro i
      have ht : t (segmentIndex i) = -(1 / 2 : ℝ) • g (u i) := by
        simp only [t, segmentIndex, Fin.coe_castLE, dif_pos i.isLt]
      change translateBody (t (segmentIndex i))
        (mapBody g.toContinuousLinearMap (Q (segmentIndex i))) = _
      rw [ht, hseg, map_segmentBody, map_zero]
      change translateBody (-(1 / 2 : ℝ) • g (u i)) (segmentBody 0 (g (u i))) =
        centeredBody (g (u i))
      exact (centeredBody_eq_translate (g (u i))).symm
    have hLA : L bodyA = R bodyA := by simp [L, t, bodyA]
    have hLB : L bodyB = R bodyB := by simp [L, t, bodyB]
    have hLC : L bodyC = R bodyC := by simp [L, t, bodyC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [hLseg]
      fin_cases i
      · obtain ⟨s, hs, he⟩ := hga 0
        change centeredBody (g (u 0)) = centeredBody (axis 0)
        change g (axis 0) = s • axis 0 at he
        rw [hu₀, he, centeredBody_smul_sign s hs]
      · obtain ⟨s, hs, he⟩ := hga 1
        change centeredBody (g (u 1)) = centeredBody (axis 1)
        change g (axis 1) = s • axis 1 at he
        rw [hu₁, he, centeredBody_smul_sign s hs]
      · obtain ⟨s, hs, he⟩ := hga 2
        change centeredBody (g (u 2)) = centeredBody (axis 2)
        change g (axis 2) = s • axis 2 at he
        rw [hu₂, he, centeredBody_smul_sign s hs]
      · change centeredBody (g (u 3)) = centeredBody directionV
        calc
          centeredBody (g (u 3)) = centeredBody (rv • g (u 3)) :=
            (centeredBody_smul_sign rv hrv _).symm
          _ = centeredBody (g (rv • u 3)) := congrArg centeredBody (map_smul g rv (u 3)).symm
          _ = centeredBody directionV := congrArg centeredBody hgv
      · change centeredBody (g (u 4)) = centeredBody directionW
        calc
          centeredBody (g (u 4)) = centeredBody (rw • g (u 4)) :=
            (centeredBody_smul_sign rw hrw _).symm
          _ = centeredBody (g (rw • u 4)) := congrArg centeredBody (map_smul g rw (u 4)).symm
          _ = centeredBody directionW := congrArg centeredBody hgw
      · change centeredBody (g (u 5)) = centeredBody directionZ
        calc
          centeredBody (g (u 5)) = centeredBody (rz • g (u 5)) :=
            (centeredBody_smul_sign rz hrz _).symm
          _ = centeredBody (g (rz • u 5)) := congrArg centeredBody (map_smul g rz (u 5)).symm
          _ = centeredBody directionZ := congrArg centeredBody hgz
    · rw [hLA]
      exact mapBody_zero_mem _ (hz bodyA)
    · rw [hLB]
      exact mapBody_zero_mem _ (hz bodyB)
    · rw [hLC]
      exact mapBody_zero_mem _ (hz bodyC)
    · rw [hLA]
      exact mapBody_coordinate_zero _ hga' hplaneA
    · rw [hLB]
      exact mapBody_coordinate_zero _ hga' hplaneB
    · rw [hLC]
      exact mapBody_coordinate_zero _ hga' hplaneC

end VolumePolynomials.Holonomy
