module

public import mixed_volume.general.canonical_geometry

/-! Projected-area equalities extracted from the complete base volume
polynomial force every transition image and every stochastic state equation. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralForcing

abbrev Plane := AutomatonWords.Plane

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids
open AutomatonRecurrence GeneralLabels GeneralCalibration GeneralNormalization CanonicalGeometry
open Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

def state (K : Label s m → Body 3) (j : Fin m) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K (stateLabel j))
def imageState (K : Label s m → Body 3) (a : Fin s) (j : Fin m) : ConvexBody Plane :=
  mapBody (coordinateProjection 2) (K (imageLabel a j))
def deficit (K : Label s m → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K deficitLabel)

def projectionLetter (a : Fin s) : Space 3 →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp
    (projectionFrame 2 (-((a.val : ℝ) + 1), -base s)).toContinuousLinearMap

def projectionIdentity : Space 3 →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp (projectionFrame 2 (0,-1)).toContinuousLinearMap

@[simp] theorem projectionLetter_apply (a : Fin s) (x : Space 3) :
    projectionLetter a x = (x 0 + ((a.val : ℝ) + 1) * x 2, x 1 + base s * x 2) := by
  ext <;> simp [projectionLetter,projectionFrame_apply] <;> ring

@[simp] theorem projectionIdentity_apply (x : Space 3) :
    projectionIdentity x = (x 0,x 1 + x 2) := by
  simp [projectionIdentity,projectionFrame_apply]

theorem extrusion_letter (a : Fin s) (L : Body 3) :
    bodyVolume (L + centeredBody (letterDirection a)) - bodyVolume L =
      volume.real (mapBody (projectionLetter a) L : Set Plane) := by
  apply bodyExtrusion_eq_frame_projection L (projectionFrame 2 (-((a.val : ℝ) + 1),-base s))
    (projectionFrame_measurePreserving 2 (-((a.val : ℝ) + 1),-base s)) (letterDirection a)
  simp [projectionFrame_apply,letterDirection]

theorem extrusion_identity (L : Body 3) :
    bodyVolume (L + centeredBody identityDirection) - bodyVolume L =
      volume.real (mapBody projectionIdentity L : Set Plane) := by
  apply bodyExtrusion_eq_frame_projection L (projectionFrame 2 (0,-1))
    (projectionFrame_measurePreserving 2 (0,-1)) identityDirection
  norm_num [projectionFrame_apply,identityDirection]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.place_state {K : Label s m → Body 3} (hK : Calibrated K) (j : Fin m) :
    K (stateLabel j) = mapBody embedXZ (state K j) := by
  apply ConvexBody.ext
  change _ = embedXZ '' (coordinateProjection 1 '' (K (stateLabel j) : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K (stateLabel j) : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.statePlane j x hx))
    _ = _ := Set.image_id' _

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.place_image {K : Label s m → Body 3} (hK : Calibrated K) (a : Fin s) (j : Fin m) :
    K (imageLabel a j) = mapBody embedXY (imageState K a j) := by
  apply ConvexBody.ext
  change _ = embedXY '' (coordinateProjection 2 '' (K (imageLabel a j) : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K (imageLabel a j) : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXY_coordinateProjection (hK.imagePlane a j x hx))
    _ = _ := Set.image_id' _

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.place_deficit {K : Label s m → Body 3} (hK : Calibrated K) :
    K deficitLabel = mapBody embedXZ (deficit K) := by
  apply ConvexBody.ext
  change _ = embedXZ '' (coordinateProjection 1 '' (K deficitLabel : Set (Space 3)))
  rw [Set.image_image]
  symm
  calc
    _ = id '' (K deficitLabel : Set (Space 3)) :=
      Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.deficitPlane x hx))
    _ = _ := Set.image_id' _

theorem projectionLetter_embedXY (a : Fin s) :
    (projectionLetter a).comp embedXY = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionLetter_apply,embedXY]

theorem projectionIdentity_embedXY :
    projectionIdentity.comp embedXY = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionIdentity_apply,embedXY]

theorem projectionIdentity_embedXZ :
    projectionIdentity.comp embedXZ = ContinuousLinearMap.id ℝ Plane := by
  ext p <;> simp [projectionIdentity_apply,embedXZ]

theorem scaled_projectionLetter_embedXZ (a : Fin s) :
    (rho s / base s) • ((projectionLetter a).comp embedXZ) = transition a := by
  ext p <;> simp [projectionLetter_apply,embedXZ,transition_apply]
  field_simp [(base_pos s).ne']

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.identity_state {K : Label s m → Body 3} (hK : Calibrated K) (j : Fin m) :
    mapBody projectionIdentity (K (stateLabel j)) = state K j := by
  rw [hK.place_state,mapBody_comp,projectionIdentity_embedXZ,ProjectedForcing.mapBody_id]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.identity_image {K : Label s m → Body 3} (hK : Calibrated K) (a : Fin s) (j : Fin m) :
    mapBody projectionIdentity (K (imageLabel a j)) = imageState K a j := by
  rw [hK.place_image,mapBody_comp,projectionIdentity_embedXY,ProjectedForcing.mapBody_id]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.letter_image {K : Label s m → Body 3} (hK : Calibrated K)
    (a b : Fin s) (j : Fin m) :
    mapBody (projectionLetter a) (K (imageLabel b j)) = imageState K b j := by
  rw [hK.place_image,mapBody_comp,projectionLetter_embedXY,ProjectedForcing.mapBody_id]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.scaled_letter_state {K : Label s m → Body 3} (hK : Calibrated K)
    (a : Fin s) (j : Fin m) :
    (rho s / base s) • mapBody (projectionLetter a) (K (stateLabel j)) =
      mapBody (transition a) (state K j) := by
  rw [hK.place_state,mapBody_comp,← ProjectedForcing.mapBody_smul_map,
    scaled_projectionLetter_embedXZ]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.identity_vertical {K : Label s m → Body 3} (hK : Calibrated K) :
    mapBody projectionIdentity (K (axisLabel 1)) = PlanarCorner.unitY := by
  rw [hK.axes,← embedXY_unitY,mapBody_comp,projectionIdentity_embedXY,ProjectedForcing.mapBody_id]

@[simp] theorem canonical_state_projection (A : Data s m) (hs : 0 < s) (j : Fin m) :
    state (canonical A hs) j = stateBody A hs j := by
  change mapBody (coordinateProjection 1) (mapBody embedXZ (stateBody A hs j)) = _
  rw [mapBody_comp]
  have h : (coordinateProjection 1).comp embedXZ = ContinuousLinearMap.id ℝ Plane := by
    ext p <;> simp only [ContinuousLinearMap.comp_apply,coordinateProjection_embedXZ,ContinuousLinearMap.id_apply]
  rw [h,ProjectedForcing.mapBody_id]

@[simp] theorem canonical_image_projection (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    imageState (canonical A hs) a j = mapBody (transition a) (stateBody A hs j) := by
  change mapBody (coordinateProjection 2) (mapBody embedXY _) = _
  rw [mapBody_comp]
  have h : (coordinateProjection 2).comp embedXY = ContinuousLinearMap.id ℝ Plane := by
    ext p <;> simp only [ContinuousLinearMap.comp_apply,coordinateProjection_embedXY,ContinuousLinearMap.id_apply]
  rw [h,ProjectedForcing.mapBody_id]

def BaseSameVolume (K L : Label s m → Body 3) : Prop :=
  ∀ w : Label s m → ℝ, (∀ i, 0 ≤ w i) → w deficitLabel = 0 →
    bodyVolume (sumBody K w) = bodyVolume (sumBody L w)

theorem BaseSameVolume.of_sameVolume {K L M : Label s m → Body 3}
    (h : BaseSameVolume K M) (heq : SameVolume L K) : BaseSameVolume L M :=
  fun w hw hz => (heq w hw).trans (h w hw hz)

def weight (i : Label s m) (r : ℝ) : Label s m → ℝ := r • unitWeight i

theorem weight_nonneg (i : Label s m) {r : ℝ} (hr : 0 ≤ r) : ∀ j, 0 ≤ weight i r j :=
  fun j => mul_nonneg hr (unitWeight_nonneg i j)

@[simp] theorem sumBody_weight (K : Label s m → Body 3) (i : Label s m) (r : ℝ) :
    sumBody K (weight i r) = r • K i := by
  simp only [sumBody,weight,Pi.smul_apply,smul_eq_mul,← smul_smul,← Finset.smul_sum]
  rw [show (∑ j, unitWeight i j • K j) = K i from sumBody_unit K i]

theorem weight_deficit (i : Label s m) (r : ℝ) (hi : i ≠ deficitLabel) :
    weight i r deficitLabel = 0 := by
  simp [weight,unitWeight,Pi.single_apply,Ne.symm hi]

theorem projected_area_eq {K L : Label s m → Body 3} (h : BaseSameVolume K L)
    (r : Reference s) (v : Space 3) (π : Space 3 →L[ℝ] Plane)
    (hK : K (ref r) = centeredBody v) (hL : L (ref r) = centeredBody v)
    (hext : ∀ B : Body 3, bodyVolume (B + centeredBody v) - bodyVolume B =
      volume.real (mapBody π B : Set Plane))
    (w : Label s m → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : w deficitLabel = 0) :
    volume.real (mapBody π (sumBody K w) : Set Plane) =
      volume.real (mapBody π (sumBody L w) : Set Plane) := by
  have hz' : (w + (unitWeight (ref r) : Label s m → ℝ)) deficitLabel = 0 := by
    change w deficitLabel + unitWeight (ref r) deficitLabel = 0
    rw [hz]
    simp [unitWeight,ref,deficitLabel]
  have hp := h (w + unitWeight (ref r))
    (fun i => add_nonneg (hw i) (unitWeight_nonneg _ i)) hz'
  rw [sumBody_add K _ _ hw (unitWeight_nonneg _),sumBody_unit,hK,
    sumBody_add L _ _ hw (unitWeight_nonneg _),sumBody_unit,hL] at hp
  rw [← hext,← hext,hp,h w hw hz]

/-- The two projected competitors are translates whenever their complete
quadratic area polynomial agrees with two copies of one positive-area body. -/
theorem projected_translates {K L : Label s m → Body 3} (h : BaseSameVolume K L)
    (r : Reference s) (v : Space 3) (π : Space 3 →L[ℝ] Plane)
    (hK : K (ref r) = centeredBody v) (hL : L (ref r) = centeredBody v)
    (hext : ∀ B : Body 3, bodyVolume (B + centeredBody v) - bodyVolume B =
      volume.real (mapBody π B : Set Plane))
    (w u : Label s m → ℝ) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i)
    (hwz : w deficitLabel = 0) (huz : u deficitLabel = 0)
    (heq : mapBody π (sumBody L w) = mapBody π (sumBody L u))
    (hpos : 0 < volume.real (mapBody π (sumBody L w) : Set Plane)) :
    ∃ q : Plane, mapBody π (sumBody K u) = translateBody q (mapBody π (sumBody K w)) := by
  have ha := projected_area_eq h r v π hK hL hext w hw hwz
  have hb := projected_area_eq h r v π hK hL hext u hu huz
  have hc := projected_area_eq h r v π hK hL hext (w + u)
    (fun i => add_nonneg (hw i) (hu i)) (by simp only [Pi.add_apply,hwz,huz,add_zero])
  rw [sumBody_add K _ _ hw hu,sumBody_add L _ _ hw hu,mapBody_add,mapBody_add,← heq] at hc
  have hdouble : mapBody π (sumBody L w) + mapBody π (sumBody L w) =
      (2 : ℝ) • mapBody π (sumBody L w) := by
    simpa only [one_smul,one_add_one_eq_two] using
      (body_add_smul (mapBody π (sumBody L w)) zero_le_one zero_le_one).symm
  rw [hdouble,PlanarCorner.area_smul _ (by norm_num)] at hc
  obtain ⟨q,hq⟩ := equal_area_translates
    (mapBody π (sumBody K w)).convex (mapBody π (sumBody K w)).isCompact
    (mapBody π (sumBody K u)).convex (mapBody π (sumBody K u)).isCompact
    (by rw [ha]; exact hpos) (by rw [hb,ha,heq]) (by
      rw [← ConvexBody.coe_add]
      rw [hc,ha]
      norm_num)
  exact ⟨q,ConvexBody.ext (by simpa only [coe_translateBody] using hq)⟩

theorem images_forced (A : Data s m) (hs : 0 < s) {K : Label s m → Body 3}
    (hbase : BaseSameVolume K (canonical A hs)) (hK : Calibrated K)
    (a : Fin s) (j : Fin m) :
    ∃ q : Plane, imageState K a j = translateBody q (mapBody (transition a) (state K j)) := by
  let w : Label s m → ℝ := weight (stateLabel j) (rho s / base s)
  let u : Label s m → ℝ := weight (imageLabel a j) 1
  have hw : ∀ i, 0 ≤ w i := weight_nonneg _ (div_nonneg (rho_pos hs).le (base_pos s).le)
  have hu : ∀ i, 0 ≤ u i := weight_nonneg _ zero_le_one
  have hsimp (M : Label s m → Body 3) (hM : Calibrated M) :
      mapBody (projectionLetter a) (sumBody M w) = mapBody (transition a) (state M j) := by
    rw [sumBody_weight,mapBody_smul,hM.scaled_letter_state]
  have husimp (M : Label s m → Body 3) (hM : Calibrated M) :
      mapBody (projectionLetter a) (sumBody M u) = imageState M a j := by
    rw [sumBody_weight,one_smul,hM.letter_image]
  have hc := canonical_calibrated A hs
  have heq : mapBody (projectionLetter a) (sumBody (canonical A hs) w) =
      mapBody (projectionLetter a) (sumBody (canonical A hs) u) := by
    rw [hsimp _ hc,husimp _ hc,canonical_state_projection,canonical_image_projection]
  have hpos : 0 < volume.real (mapBody (projectionLetter a) (sumBody (canonical A hs) w) : Set Plane) := by
    rw [hsimp _ hc,canonical_state_projection,PlanarEdges.area_mapBody,MomentGeometry.transition_det,
      abs_of_nonneg (MomentGeometry.imageFactor_nonneg hs)]
    exact mul_pos (div_pos (sq_pos_of_pos (rho_pos hs)) (base_pos s)) (state_area_pos A hs j)
  obtain ⟨q,hq⟩ := projected_translates hbase (letterRef a) (letterDirection a)
    (projectionLetter a) (hK.letters a) (canonical_letter A hs a) (extrusion_letter a)
    w u hw hu (weight_deficit _ _ (by simp [stateLabel,deficitLabel]))
    (weight_deficit _ _ (by simp [imageLabel,deficitLabel])) heq hpos
  rw [hsimp _ hK,husimp _ hK] at hq
  exact ⟨q,hq⟩


def recurrenceWeight (A : Data s m) (j : Fin m) : Label s m → ℝ
  | .inl (.inl i) => if i = 1 then 1 + A.f j else 0
  | .inr (.inr (.inl (a,k))) => A.P a j k
  | _ => 0

theorem recurrenceWeight_nonneg (A : Data s m) (j : Fin m) :
    ∀ i, 0 ≤ recurrenceWeight A j i := by
  intro i
  rcases i with (i | a | ⟨⟩) | k | ⟨a,k⟩ | ⟨⟩
  · dsimp [recurrenceWeight]
    split_ifs <;> linarith [A.f_nonneg j]
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact A.P_nonneg a j k
  · exact le_rfl

theorem sumBody_recurrenceWeight (A : Data s m) (K : Label s m → Body 3) (j : Fin m) :
    sumBody K (recurrenceWeight A j) =
      (1 + A.f j) • K (axisLabel 1) + ∑ a, ∑ k, A.P a j k • K (imageLabel a k) := by
  simp [sumBody,recurrenceWeight,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_three,axisLabel,ref,axisRef,imageLabel]

def recurrenceBody (A : Data s m) (K : Label s m → Body 3) (j : Fin m) : ConvexBody Plane :=
  (1 + A.f j) • PlanarCorner.unitY + ∑ a, ∑ k, A.P a j k • imageState K a k

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.identity_recurrence {K : Label s m → Body 3} (hK : Calibrated K)
    (A : Data s m) (j : Fin m) :
    mapBody projectionIdentity (sumBody K (recurrenceWeight A j)) = recurrenceBody A K j := by
  rw [sumBody_recurrenceWeight,mapBody_add,mapBody_smul,hK.identity_vertical]
  change _ = (1 + A.f j) • PlanarCorner.unitY + _
  congr 1
  rw [show mapBody projectionIdentity (∑ a, ∑ k, A.P a j k • K (imageLabel a k)) =
      ∑ a, mapBody projectionIdentity (∑ k, A.P a j k • K (imageLabel a k)) from
    map_sum (mapBodyHom projectionIdentity) _ _]
  apply Finset.sum_congr rfl
  intro a _
  rw [show mapBody projectionIdentity (∑ k, A.P a j k • K (imageLabel a k)) =
      ∑ k, mapBody projectionIdentity (A.P a j k • K (imageLabel a k)) from
    map_sum (mapBodyHom projectionIdentity) _ _]
  simp only [mapBody_smul,hK.identity_image]

theorem canonical_recurrence (A : Data s m) (hs : 0 < s) (j : Fin m) :
    recurrenceBody A (canonical A hs) j = stateBody A hs j := by
  simp only [recurrenceBody,canonical_image_projection]
  exact (state_equation A hs j).symm

theorem recurrences_forced (A : Data s m) (hs : 0 < s) {K : Label s m → Body 3}
    (hbase : BaseSameVolume K (canonical A hs)) (hK : Calibrated K) (j : Fin m) :
    ∃ q : Plane, recurrenceBody A K j = translateBody q (state K j) := by
  let w : Label s m → ℝ := weight (stateLabel j) 1
  let u : Label s m → ℝ := recurrenceWeight A j
  have hw : ∀ i, 0 ≤ w i := weight_nonneg _ zero_le_one
  have hu : ∀ i, 0 ≤ u i := recurrenceWeight_nonneg A j
  have hsimp (M : Label s m → Body 3) (hM : Calibrated M) :
      mapBody projectionIdentity (sumBody M w) = state M j := by
    rw [sumBody_weight,one_smul,hM.identity_state]
  have hc := canonical_calibrated A hs
  have heq : mapBody projectionIdentity (sumBody (canonical A hs) w) =
      mapBody projectionIdentity (sumBody (canonical A hs) u) := by
    rw [hsimp _ hc,hc.identity_recurrence,canonical_state_projection,canonical_recurrence]
  have hpos : 0 < volume.real (mapBody projectionIdentity (sumBody (canonical A hs) w) : Set Plane) := by
    rw [hsimp _ hc,canonical_state_projection]
    exact state_area_pos A hs j
  obtain ⟨q,hq⟩ := projected_translates hbase identityRef identityDirection projectionIdentity
    hK.identity (canonical_identity A hs) extrusion_identity w u hw hu
    (weight_deficit _ _ (by simp [stateLabel,deficitLabel])) rfl heq hpos
  rw [hsimp _ hK,hK.identity_recurrence] at hq
  exact ⟨q,hq⟩

theorem recurrenceBody_translation (A : Data s m) (K : Label s m → Body 3)
    (q : Fin s → Fin m → Plane)
    (hq : ∀ a k, imageState K a k = translateBody (q a k)
      (mapBody (transition a) (state K k))) (j : Fin m) :
    recurrenceBody A K j = translateBody (∑ a, ∑ k, A.P a j k • q a k)
      (BodyContraction.bodyOperator A (state K) j) := by
  simp only [recurrenceBody,hq,ProjectedForcing.smul_translateBody]
  simp_rw [sum_translateBody]
  change (1 + A.f j) • PlanarCorner.unitY +
      translateBody (∑ a, ∑ k, A.P a j k • q a k)
        (∑ a, ∑ k, A.P a j k • mapBody (transition a) (state K k)) = _
  rw [← translateBody_zero ((1 + A.f j) • PlanarCorner.unitY),translateBody_add,zero_add]
  rfl

/-- The complete base cubic forces every state body to be the canonical word
zonoid up to translation.  All geometric normalizations and the contraction
uniqueness theorem are used with their proved hypotheses. -/
theorem states_forced (A : Data s m) (hs : 0 < s) {K : Label s m → Body 3}
    (hbase : BaseSameVolume K (canonical A hs)) (hK : Calibrated K) :
    ∃ t : Fin m → Plane, ∀ j, state K j = translateBody (t j) (stateBody A hs j) := by
  classical
  choose q hq using fun a k => images_forced A hs hbase hK a k
  choose z hz using fun j => recurrences_forced A hs hbase hK j
  have he (j : Fin m) : state K j =
      translateBody ((∑ a, ∑ k, A.P a j k • q a k) - z j)
        (BodyContraction.bodyOperator A (state K) j) := by
    have h := congrArg (translateBody (-z j)) (hz j)
    rw [translateBody_translate,neg_add_cancel,translateBody_zero] at h
    rw [recurrenceBody_translation A K q hq j,translateBody_translate] at h
    simpa only [sub_eq_add_neg,add_comm] using h.symm
  exact solution_up_to_translation A hs (state K) _ he

end MixedVolume.GeneralForcing

end
