module

public import mixed_volume.general.reference_normalization
public import mixed_volume.general.moment_geometry

/-! The actual reference/state/image tuple of the general reduction, all
calibration tests, and the nondegeneracy needed for Minkowski equality. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.CanonicalGeometry

abbrev Plane := AutomatonWords.Plane

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids
open AutomatonMoments AutomatonRecurrence MomentGeometry GeneralLabels GeneralCalibration
open GeneralNormalization Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

def canonical (A : Data s m) (hs : 0 < s) : Label s m → Body 3
  | .inl r => centeredBody (referenceDirection r)
  | .inr (.inl j) => mapBody embedXZ (stateBody A hs j)
  | .inr (.inr (.inl (a,j))) => mapBody embedXY (mapBody (transition a) (stateBody A hs j))
  | .inr (.inr (.inr _)) => 0

@[simp] theorem canonical_ref (A : Data s m) (hs : 0 < s) (r : Reference s) :
    canonical A hs (ref r) = centeredBody (referenceDirection r) := rfl
@[simp] theorem canonical_state (A : Data s m) (hs : 0 < s) (j : Fin m) :
    canonical A hs (stateLabel j) = mapBody embedXZ (stateBody A hs j) := rfl
@[simp] theorem canonical_image (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    canonical A hs (imageLabel a j) = mapBody embedXY (mapBody (transition a) (stateBody A hs j)) := rfl
@[simp] theorem canonical_deficit (A : Data s m) (hs : 0 < s) : canonical A hs deficitLabel = 0 := rfl
@[simp] theorem canonical_axis (A : Data s m) (hs : 0 < s) (i : Fin 3) :
    canonical A hs (axisLabel i) = centeredBody (axis i) := rfl
@[simp] theorem canonical_letter (A : Data s m) (hs : 0 < s) (a : Fin s) :
    canonical A hs (letterLabel a) = centeredBody (letterDirection a) := rfl
@[simp] theorem canonical_identity (A : Data s m) (hs : 0 < s) :
    canonical A hs identityLabel = centeredBody identityDirection := rfl

theorem volume_three_centered (u v w : Space 3) :
    bodyVolume (centeredBody u + centeredBody v + centeredBody w) = |determinant3 u v w| := by
  rw [centeredBody_eq_translate u, centeredBody_eq_translate v, centeredBody_eq_translate w,
    translateBody_add, translateBody_add, bodyVolume_translate, volume_three_origin_segments]

theorem volume_two_centered (u v : Space 3) : bodyVolume (centeredBody u + centeredBody v) = 0 := by
  have h := volume_three_centered u v 0
  simpa only [centeredBody_zero, add_zero, determinant3, Pi.zero_apply, mul_zero,
    sub_zero, add_zero, abs_zero] using h

theorem map_planar_segment (f : Plane →L[ℝ] Space 3) (v : Plane) :
    mapBody f (PlanarCorner.segmentBody v) = centeredBody (f v) := by
  apply ConvexBody.ext
  rw [coe_mapBody, centeredBody_carrier]
  change f '' ((fun t : ℝ => t • v) '' Icc (-(1/2 : ℝ)) (1/2 : ℝ)) = _
  rw [Set.image_image]
  congr 1
  funext t
  exact f.map_smul t v

theorem embedXY_unitX : mapBody embedXY PlanarCorner.unitX = centeredBody (axis 0) := by
  rw [PlanarCorner.unitX, map_planar_segment]
  congr 1
  ext i
  fin_cases i <;> simp [embedXY, axis]

theorem embedXY_unitY : mapBody embedXY PlanarCorner.unitY = centeredBody (axis 1) := by
  rw [PlanarCorner.unitY, map_planar_segment]
  congr 1
  ext i
  fin_cases i <;> simp [embedXY, axis]

theorem embedXZ_unitX : mapBody embedXZ PlanarCorner.unitX = centeredBody (axis 0) := by
  rw [PlanarCorner.unitX, map_planar_segment]
  congr 1
  ext i
  fin_cases i <;> simp [embedXZ, axis]

theorem embedXZ_unitY : mapBody embedXZ PlanarCorner.unitY = centeredBody (axis 2) := by
  rw [PlanarCorner.unitY, map_planar_segment]
  congr 1
  ext i
  fin_cases i <;> simp [embedXZ, axis]

theorem volume_XZ_axes (K : ConvexBody Plane) :
    bodyVolume (mapBody embedXZ K + centeredBody (axis 0) + centeredBody (axis 2)) = 0 := by
  rw [← embedXZ_unitX, ← embedXZ_unitY, ← mapBody_add, ← mapBody_add]
  have h := ScalarCombination.volume_planePair (K + PlanarCorner.unitX + PlanarCorner.unitY) 0
  have hz : mapBody embedXY (0 : ConvexBody Plane) = 0 := (mapBodyHom embedXY).map_zero
  simpa only [ScalarCombination.planePair,hz,add_zero,
    PlanarInteraction.height_zeroBody,PlanarInteraction.area_zeroBody,mul_zero,add_zero] using h

theorem volume_XY_axes (K : ConvexBody Plane) :
    bodyVolume (mapBody embedXY K + centeredBody (axis 0) + centeredBody (axis 1)) = 0 := by
  rw [← embedXY_unitX, ← embedXY_unitY, ← mapBody_add, ← mapBody_add]
  have h := ScalarCombination.volume_planePair 0 (K + PlanarCorner.unitX + PlanarCorner.unitY)
  have hz : mapBody embedXZ (0 : ConvexBody Plane) = 0 := (mapBodyHom embedXZ).map_zero
  simpa only [ScalarCombination.planePair,hz,zero_add,
    PlanarInteraction.height_zeroBody,PlanarInteraction.area_zeroBody,zero_mul,zero_add] using h

theorem canonical_tests (A : Data s m) (hs : 0 < s) : Tests hs (canonical A hs) := by
  constructor
  · intro r i
    rw [canonical_ref,canonical_axis,volume_two_centered]
  · rw [canonical_axis,canonical_axis,canonical_axis,volume_three_centered]
    norm_num [determinant3,axis]
  · intro a
    rw [canonical_letter,canonical_axis,canonical_axis,volume_three_centered]
    simp [letterDirection,determinant3,axis,abs_of_nonneg (by positivity : 0 ≤ (a.val : ℝ) + 1)]
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) a.val])]
    ring
  · intro a
    rw [canonical_letter,canonical_axis,canonical_axis,volume_three_centered]
    simp [letterDirection,determinant3,axis,abs_of_pos (base_pos s)]
  · intro a
    rw [canonical_letter,canonical_axis,canonical_axis,volume_three_centered]
    norm_num [letterDirection,determinant3,axis]
  · rw [canonical_identity,canonical_axis,canonical_axis,volume_three_centered]
    norm_num [identityDirection,determinant3,axis]
  · rw [canonical_identity,canonical_axis,canonical_axis,volume_three_centered]
    norm_num [identityDirection,determinant3,axis]
  · rw [canonical_identity,canonical_axis,canonical_axis,volume_three_centered]
    norm_num [identityDirection,determinant3,axis]
  · intro a
    rw [canonical_axis,canonical_letter,canonical_identity,volume_three_centered]
    simp only [letterDirection,identityDirection,determinant3,axis]
    norm_num
    rw [abs_of_nonpos (by dsimp [base]; linarith [Nat.cast_nonneg (α := ℝ) s])]
    ring
  · intro a
    rw [canonical_letter,canonical_axis,canonical_letter,volume_three_centered]
    simp only [letterDirection,determinant3,axis]
    norm_num
  · intro j
    rw [canonical_state,canonical_axis,canonical_axis]
    exact volume_XZ_axes _
  · intro a j
    rw [canonical_image,canonical_axis,canonical_axis]
    exact volume_XY_axes _
  · rw [canonical_deficit,canonical_axis,canonical_axis,zero_add,volume_two_centered]

theorem stateBody_zero (A : Data s m) (hs : 0 < s) (j : Fin m) :
    (0 : Plane) ∈ stateBody A hs j := IndexedSeries.zero_mem_segmentSeries _

theorem canonical_calibrated (A : Data s m) (hs : 0 < s) : Calibrated (canonical A hs) := by
  constructor
  · exact canonical_axis A hs
  · exact canonical_letter A hs
  · exact canonical_identity A hs
  · intro j
    exact ⟨0,stateBody_zero A hs j,map_zero embedXZ⟩
  · intro a j
    exact ⟨0,⟨0,stateBody_zero A hs j,map_zero (transition a)⟩,map_zero embedXY⟩
  · exact Set.mem_singleton 0
  · intro j x hx
    rcases hx with ⟨y,hy,rfl⟩
    rfl
  · intro a j x hx
    rcases hx with ⟨y,hy,rfl⟩
    rfl
  · intro x hx
    have hx0 : x = 0 := hx
    rw [hx0]
    rfl

theorem first_pos (A : Data s m) (hs : 0 < s) (j : Fin m) : 0 < first A j := by
  let a : Fin s := ⟨0,hs⟩
  have ht : 0 < firstTerm A j [a] := by
    dsimp [firstTerm,massTerm]
    exact mul_pos (mul_pos (A.weight_pos _ j) (pow_pos (rho_pos hs) _)) (tag_cons_pos a [])
  have hle := (first_summable A hs j).le_tsum [a] (fun w _ => firstTerm_nonneg A hs j w)
  exact lt_of_lt_of_le ht hle

theorem state_area_pos (A : Data s m) (hs : 0 < s) (j : Fin m) :
    0 < volume.real (stateBody A hs j : Set Plane) := by
  let R : ConvexBody Plane := ∑ a, ∑ k, A.P a j k • mapBody (transition a) (stateBody A hs k)
  have he : stateBody A hs j = R + (1 + A.f j) • PlanarCorner.unitY := by
    rw [state_equation]
    exact add_comm _ _
  have hb : 0 < 1 + A.f j := by linarith [A.f_nonneg j]
  have hw : PlanarCorner.width R = first A j := by
    have h := congrArg PlanarCorner.width he
    rw [state_width, PlanarCorner.width_add, PlanarCorner.width_smul _ hb.le,
      PlanarCorner.width_unitY,mul_zero,add_zero] at h
    exact h.symm
  rw [he, PlanarCorner.area_add_scaled_unitY R hb.le, hw]
  exact add_pos_of_nonneg_of_pos measureReal_nonneg (mul_pos hb (first_pos A hs j))

end MixedVolume.CanonicalGeometry

end
