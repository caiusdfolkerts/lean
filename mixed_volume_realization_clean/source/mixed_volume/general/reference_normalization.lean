module

public import mixed_volume.general.labels

/-! Arbitrary competing convex bodies are normalized from their actual cubic
volume tests.  No segment, coordinate-plane, or calibration hypothesis is
assumed about the competitors. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralNormalization

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords GeneralLabels GeneralCalibration
open Set
open scoped Pointwise BigOperators

variable {s m : ℕ}

structure Tests (hs : 0 < s) (K : Label s m → Body 3) : Prop where
  segmentZero : ∀ r : Reference s, ∀ j : Fin 3,
    bodyVolume (K (ref r) + K (axisLabel j)) = 0
  frameVolume : bodyVolume (K (axisLabel 0) + K (axisLabel 1) + K (axisLabel 2)) = 1
  letterX : ∀ a, bodyVolume (K (letterLabel a) + K (axisLabel 1) + K (axisLabel 2)) = (a.val : ℝ) + 1
  letterY : ∀ a, bodyVolume (K (letterLabel a) + K (axisLabel 0) + K (axisLabel 2)) = base s
  letterZ : ∀ a, bodyVolume (K (letterLabel a) + K (axisLabel 0) + K (axisLabel 1)) = 1
  identityX : bodyVolume (K identityLabel + K (axisLabel 1) + K (axisLabel 2)) = 0
  identityY : bodyVolume (K identityLabel + K (axisLabel 0) + K (axisLabel 2)) = 1
  identityZ : bodyVolume (K identityLabel + K (axisLabel 0) + K (axisLabel 1)) = 1
  verticalPair : ∀ a, bodyVolume (K (axisLabel 0) + K (letterLabel a) + K identityLabel) = base s - 1
  horizontalPair : ∀ a, bodyVolume (K (letterLabel a) + K (axisLabel 1) + K (letterLabel ⟨0,hs⟩)) = (a.val : ℝ)
  statePlane : ∀ j, bodyVolume (K (stateLabel j) + K (axisLabel 0) + K (axisLabel 2)) = 0
  imagePlane : ∀ a j, bodyVolume (K (imageLabel a j) + K (axisLabel 0) + K (axisLabel 1)) = 0
  deficitPlane : bodyVolume (K deficitLabel + K (axisLabel 0) + K (axisLabel 2)) = 0

theorem Tests.of_sameVolume {hs : 0 < s} {K L : Label s m → Body 3}
    (h : Tests hs K) (heq : SameVolume L K) : Tests hs L := by
  constructor
  · intro r j; rw [heq.pair]; exact h.segmentZero r j
  · rw [heq.triple]; exact h.frameVolume
  · intro a; rw [heq.triple]; exact h.letterX a
  · intro a; rw [heq.triple]; exact h.letterY a
  · intro a; rw [heq.triple]; exact h.letterZ a
  · rw [heq.triple]; exact h.identityX
  · rw [heq.triple]; exact h.identityY
  · rw [heq.triple]; exact h.identityZ
  · intro a; rw [heq.triple]; exact h.verticalPair a
  · intro a; rw [heq.triple]; exact h.horizontalPair a
  · intro j; rw [heq.triple]; exact h.statePlane j
  · intro a j; rw [heq.triple]; exact h.imagePlane a j
  · rw [heq.triple]; exact h.deficitPlane

theorem Tests.segments {hs : 0 < s} {K : Label s m → Body 3}
    (h : Tests hs K) (hz : ∀ i, (0 : Space 3) ∈ K i) :
    ∀ r : Reference s, ∃ x y : Space 3,
      x ∈ K (ref r) ∧ y ∈ K (ref r) ∧ K (ref r) = segmentBody x y := by
  intro r
  obtain ⟨x,y,hx,hy,hxy⟩ := body_is_segment_of_three_zero_volumes
    (K (ref r)) (K (axisLabel 0)) (K (axisLabel 1)) (K (axisLabel 2))
    (hz _) (hz _) (hz _) (hz _)
    (h.segmentZero r 0) (h.segmentZero r 1) (h.segmentZero r 2)
    (by rw [h.frameVolume]; norm_num)
  exact ⟨x,y,hx,hy,body_eq_segmentBody hxy⟩

theorem normalize_origins (hs : 0 < s) (K : Label s m → Body 3) (hK : Tests hs K) :
    ∃ L : Label s m → Body 3, ∃ u : Reference s → Space 3,
      SameVolume L K ∧ (∀ i, (0 : Space 3) ∈ L i) ∧
        ∀ r, L (ref r) = segmentBody 0 (u r) := by
  classical
  choose p hp using fun i => (K i).nonempty
  let K₀ : Label s m → Body 3 := fun i => translateBody (-p i) (K i)
  have hK₀ : SameVolume K₀ K := sameVolume_translate K (fun i => -p i)
  have hz₀ : ∀ i, (0 : Space 3) ∈ K₀ i := fun i => zero_mem_translateBody_neg (hp i)
  choose x y hx hy hxy using (hK.of_sameVolume hK₀).segments hz₀
  let v : Label s m → Space 3
    | .inl r => -x r
    | .inr _ => 0
  let L : Label s m → Body 3 := fun i => translateBody (v i) (K₀ i)
  refine ⟨L, fun r => y r - x r, (sameVolume_translate K₀ v).trans hK₀, ?_, ?_⟩
  · intro i
    cases i with
    | inl r => exact zero_mem_translateBody_neg (hx r)
    | inr j => simpa only [L, v, translateBody_zero] using hz₀ (.inr j)
  · intro r
    change translateBody (-x r) (K₀ (ref r)) = _
    rw [hxy r, translate_segmentBody, neg_add_cancel, neg_add_eq_sub]

theorem normalize_frame (hs : 0 < s) (K : Label s m → Body 3) (hK : Tests hs K) :
    ∃ L : Label s m → Body 3, ∃ u : Reference s → Space 3,
      SameVolume L K ∧ (∀ i, (0 : Space 3) ∈ L i) ∧
      (∀ r, L (ref r) = segmentBody 0 (u r)) ∧
      ∀ i : Fin 3, u (axisRef i) = axis i := by
  obtain ⟨P,v,hP,hz,hseg⟩ := normalize_origins hs K hK
  let vf : Fin 3 → Space 3 := fun i => v (axisRef i)
  have hv : bodyVolume (∑ i, segmentBody 0 (vf i)) = 1 := by
    simp only [Fin.sum_univ_three, vf]
    rw [← hseg (axisRef 0), ← hseg (axisRef 1), ← hseg (axisRef 2)]
    exact (hK.of_sameVolume hP).frameVolume
  obtain ⟨g,hg,hgv⟩ := normalize_origin_segment_frame vf hv
  refine ⟨fun i => mapBody g.toContinuousLinearMap (P i), fun r => g (v r),
    (sameVolume_map P g.toContinuousLinearMap hg).trans hP, ?_, ?_, hgv⟩
  · intro i
    exact ⟨0,hz i,map_zero g⟩
  · intro r
    change mapBody g.toContinuousLinearMap (P (ref r)) = segmentBody 0 (g (v r))
    rw [hseg, map_segmentBody, map_zero, ContinuousLinearEquiv.coe_coe]

structure Calibrated (K : Label s m → Body 3) : Prop where
  axes : ∀ i : Fin 3, K (axisLabel i) = centeredBody (axis i)
  letters : ∀ a, K (letterLabel a) = centeredBody (letterDirection a)
  identity : K identityLabel = centeredBody identityDirection
  stateZero : ∀ j, (0 : Space 3) ∈ K (stateLabel j)
  imageZero : ∀ a j, (0 : Space 3) ∈ K (imageLabel a j)
  deficitZero : (0 : Space 3) ∈ K deficitLabel
  statePlane : ∀ j, ∀ x ∈ K (stateLabel j), x 1 = 0
  imagePlane : ∀ a j, ∀ x ∈ K (imageLabel a j), x 2 = 0
  deficitPlane : ∀ x ∈ K deficitLabel, x 1 = 0

/-- Complete normalization of every competing tuple from its volume tests. -/
theorem normalize_references (hs : 0 < s) (K : Label s m → Body 3) (hK : Tests hs K) :
    ∃ L, SameVolume L K ∧ Calibrated L := by
  classical
  obtain ⟨P,u,hP,hz,hseg,haxis⟩ := normalize_frame hs K hK
  have ht := hK.of_sameVolume hP
  have he (i : Fin 3) : P (axisLabel i) = segmentBody 0 (axis i) :=
    (hseg (axisRef i)).trans (congrArg (segmentBody 0) (haxis i))
  have hl (a : Fin s) : P (letterLabel a) = segmentBody 0 (u (letterRef a)) := hseg _
  have hi : P identityLabel = segmentBody 0 (u identityRef) := hseg _
  have hlx (a : Fin s) : |u (letterRef a) 0| = (a.val : ℝ) + 1 := by
    simpa only [hl, he, axis, volume_coordinate_test₁] using ht.letterX a
  have hly (a : Fin s) : |u (letterRef a) 1| = base s := by
    simpa only [hl, he, axis, volume_coordinate_test₂] using ht.letterY a
  have hlz (a : Fin s) : |u (letterRef a) 2| = 1 := by
    simpa only [hl, he, axis, volume_coordinate_test₃] using ht.letterZ a
  have hix : u identityRef 0 = 0 := by
    have h := ht.identityX
    simp only [hi, he, axis, volume_coordinate_test₁] at h
    exact abs_eq_zero.mp h
  have hiy : |u identityRef 1| = 1 := by
    simpa only [hi, he, axis, volume_coordinate_test₂] using ht.identityY
  have hiz : |u identityRef 2| = 1 := by
    simpa only [hi, he, axis, volume_coordinate_test₃] using ht.identityZ
  have hvertical (a : Fin s) :
      |u (letterRef a) 1 * u identityRef 2 - u (letterRef a) 2 * u identityRef 1| = base s - 1 := by
    simpa [he, hl, hi, volume_three_origin_segments, determinant3, axis] using ht.verticalPair a
  have hhorizontal (a : Fin s) :
      |u (letterRef a) 0 * u (letterRef ⟨0,hs⟩) 2 -
        u (letterRef a) 2 * u (letterRef ⟨0,hs⟩) 0| = (a.val : ℝ) := by
    simpa [he, hl, volume_three_origin_segments, determinant3, axis, sub_eq_add_neg] using ht.horizontalPair a
  obtain ⟨g,hg,hga,hgaBody,hgl,hgi⟩ := GeneralCalibration.calibrate_vectors hs
    (fun a => u (letterRef a)) (u identityRef) hlx hly hlz hix hiy hiz hvertical hhorizontal
  have hstate : ∀ j, ∀ x ∈ P (stateLabel j), x 1 = 0 := by
    intro j
    apply coordinate_eq_zero_of_volume_zero (P (stateLabel j)) 0 2 1
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he, coordinateSegment, axis] using ht.statePlane j
  have himage : ∀ a j, ∀ x ∈ P (imageLabel a j), x 2 = 0 := by
    intro a j
    apply coordinate_eq_zero_of_volume_zero (P (imageLabel a j)) 0 1 2
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he, coordinateSegment, axis] using ht.imagePlane a j
  have hdeficit : ∀ x ∈ P deficitLabel, x 1 = 0 := by
    apply coordinate_eq_zero_of_volume_zero (P deficitLabel) 0 2 1
      (by decide) (by decide) (by decide) (hz _)
    simpa only [he, coordinateSegment, axis] using ht.deficitPlane
  let R : Label s m → Body 3 := fun i => mapBody g.toContinuousLinearMap (P i)
  let t : Label s m → Space 3
    | .inl r => -(1 / 2 : ℝ) • g (u r)
    | .inr _ => 0
  let L : Label s m → Body 3 := fun i => translateBody (t i) (R i)
  have hL : SameVolume L K := (sameVolume_translate R t).trans
    ((sameVolume_map P g.toContinuousLinearMap hg).trans hP)
  have hLseg (r : Reference s) :
      L (ref r) = mapBody g.toContinuousLinearMap (centeredBody (u r)) := by
    change translateBody (-(1 / 2 : ℝ) • g (u r))
      (mapBody g.toContinuousLinearMap (P (ref r))) = _
    rw [hseg, map_segmentBody, map_zero, map_centeredBody]
    exact (centeredBody_eq_translate (g (u r))).symm
  have hLstate (j : Fin m) : L (stateLabel j) = R (stateLabel j) := by
    simp only [L,t,stateLabel,translateBody_zero]
  have hLimage (a : Fin s) (j : Fin m) : L (imageLabel a j) = R (imageLabel a j) := by
    simp only [L,t,imageLabel,translateBody_zero]
  have hLdeficit : L deficitLabel = R deficitLabel := by
    simp only [L,t,deficitLabel,translateBody_zero]
  refine ⟨L,hL,?_⟩
  constructor
  · intro i
    change L (ref (axisRef i)) = _
    rw [hLseg,haxis,hgaBody]
  · intro a
    exact (hLseg (letterRef a)).trans (hgl a)
  · exact (hLseg identityRef).trans hgi
  · intro j
    rw [hLstate]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · intro a j
    rw [hLimage]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · rw [hLdeficit]
    exact mapBody_zero_mem g.toContinuousLinearMap (hz _)
  · intro j
    rw [hLstate]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga (hstate j)
  · intro a j
    rw [hLimage]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga (himage a j)
  · rw [hLdeficit]
    exact mapBody_coordinate_zero g.toContinuousLinearMap hga hdeficit

end MixedVolume.GeneralNormalization

end
