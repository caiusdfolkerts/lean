module

public import mixed_volume.general.target_tests

/-! The signed cubic's remaining area equality forces the deficit to be an
actual Minkowski summand.  Combined with the exposed-face theorem, this gives
the universal cutpoint inequality for every finite word. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralDeficit

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords AutomatonZonoids
open GeneralLabels GeneralCalibration GeneralNormalization CanonicalGeometry GeneralTarget
open GeneralForcing GeneralTargetTests PlanarRestriction Set MeasureTheory Matrix
open scoped BigOperators Pointwise

abbrev Plane := AutomatonWords.Plane
variable {s m : ℕ}

theorem gamma_nonneg (A : Data s m) : 0 ≤ A.gamma := by
  unfold Data.gamma dotProduct
  exact Finset.sum_nonneg fun j _ => mul_nonneg (A.stationary_probability.1 j) (A.f_nonneg j)

theorem gamma_le_one (A : Data s m) : A.gamma ≤ 1 := by
  calc
    A.gamma ≤ ∑ j, A.stationary j * 1 :=
      by
        unfold Data.gamma dotProduct
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (A.f_le_one j) (A.stationary_probability.1 j)
    _ = 1 := by simp only [mul_one,A.stationary_probability.2]

def eta (A : Data s m) (theta : ℝ) : ℝ := (1 + theta) / (1 + A.gamma)
def targetDelta (A : Data s m) (p : Fin m → ℝ) (theta : ℝ) (j : Fin m) : ℝ :=
  eta A theta * A.stationary j - p j

theorem eta_pos (A : Data s m) {theta : ℝ} (htheta : 0 < theta) : 0 < eta A theta :=
  div_pos (by linarith) (by linarith [gamma_nonneg A])

theorem eta_mul_gamma (A : Data s m) (theta : ℝ) : eta A theta * (1 + A.gamma) = 1 + theta := by
  unfold eta
  exact div_mul_cancel₀ _ (by linarith [gamma_nonneg A])

def stationaryWeights (A : Data s m) (theta : ℝ) (j : Fin m) : ℝ := eta A theta * A.stationary j

theorem stationaryWeights_nonneg (A : Data s m) {theta : ℝ} (htheta : 0 < theta) :
    ∀ j, 0 ≤ stationaryWeights A theta j :=
  fun j => mul_nonneg (eta_pos A htheta).le (A.stationary_probability.1 j)

theorem stationary_scaled (A : Data s m) (hs : 0 < s) (theta : ℝ) :
    (∑ j, stationaryWeights A theta j • stateBody A hs j) = (1 + theta) • baseBody hs := by
  simp only [stationaryWeights,← smul_smul,← Finset.smul_sum]
  rw [stationary_body,smul_smul,eta_mul_gamma]

def baseData (s : ℕ) : Data s 1 where
  P _ _ _ := 1
  P_nonneg _ _ _ := zero_le_one
  P_sum _ _ := by simp
  f _ := 0
  f_nonneg _ := le_rfl
  f_le_one _ := zero_le_one
  stationary _ := 1
  stationary_probability := ⟨fun _ => zero_le_one,by simp⟩
  stationary_fixed _ := by ext j; simp [Matrix.vecMul,dotProduct]

theorem baseData_state (hs : 0 < s) : stateBody (baseData s) hs 0 = baseBody hs := by
  have hw (w : Word s) : (baseData s).weight w 0 = 1 := by
    simp [Data.weight,Data.value,baseData,Matrix.mulVec,dotProduct]
  unfold stateBody baseBody
  congr 1
  funext w
  rw [hw,one_smul]

theorem base_area_pos (hs : 0 < s) : 0 < volume.real (baseBody hs : Set Plane) := by
  rw [← baseData_state hs]
  exact state_area_pos (baseData s) hs 0

theorem stationary_scaled_area_pos (A : Data s m) (hs : 0 < s) {theta : ℝ} (htheta : 0 < theta) :
    0 < volume.real (↑(∑ j, stationaryWeights A theta j • stateBody A hs j) : Set Plane) := by
  rw [stationary_scaled,PlanarCorner.area_smul _ (by linarith)]
  exact mul_pos (sq_pos_of_pos (by linarith)) (base_area_pos hs)

theorem shiftWeight_add (δ : Fin m → ℝ) (w u : Label s m → ℝ) :
    shiftWeight δ (w + u) = shiftWeight δ w + shiftWeight δ u := by
  funext i
  rcases i with r | j | aj | u <;> simp [shiftWeight,Pi.add_apply] <;> ring

theorem shiftWeight_unitRef (δ : Fin m → ℝ) (r : Reference s) :
    shiftWeight δ (unitWeight (ref r)) = (unitWeight (ref r) : Label s m → ℝ) := by
  funext i
  rcases i with r' | j | aj | u <;>
    simp [shiftWeight,unitWeight,ref,stateLabel,deficitLabel,Pi.single_apply]

theorem safe_projected_identity {A : Data s m} {hs : 0 < s} {δ : Fin m → ℝ}
    {K : Label s m → Body 3} (h : RealizesTarget A hs δ K) (hK : Calibrated K)
    (w : Label s m → ℝ) (hw : ∀ i, 0 ≤ w i) (hshift : ∀ i, 0 ≤ shiftWeight δ w i) :
    volume.real (mapBody projectionIdentity (sumBody K w) : Set Plane) =
      volume.real (mapBody projectionIdentity (sumBody (canonical A hs) (shiftWeight δ w)) : Set Plane) := by
  have hsafe := (realizesTarget_iff_safe A hs δ K).mp h
  have hs' : ∀ i, 0 ≤ shiftWeight δ (w + unitWeight identityLabel) i := by
    rw [shiftWeight_add,show identityLabel = ref (identityRef (s := s)) from rfl,shiftWeight_unitRef]
    exact fun i => add_nonneg (hshift i) (unitWeight_nonneg _ i)
  have hp := hsafe (w + unitWeight identityLabel)
    (fun i => add_nonneg (hw i) (unitWeight_nonneg _ i)) hs'
  rw [sumBody_add K _ _ hw (unitWeight_nonneg _),sumBody_unit,hK.identity,
    shiftWeight_add,show identityLabel = ref (identityRef (s := s)) from rfl,shiftWeight_unitRef,
    sumBody_add (canonical A hs) _ _ hshift (unitWeight_nonneg _),sumBody_unit,canonical_ref] at hp
  rw [← extrusion_identity,← extrusion_identity,hp,hsafe w hw hshift]
  rfl

def stateWeight (c : Fin m → ℝ) : Label s m → ℝ
  | .inr (.inl j) => c j
  | _ => 0

theorem stateWeight_nonneg (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∀ i : Label s m, 0 ≤ stateWeight c i := by
  intro i
  rcases i with r | j | aj | u
  · exact le_rfl
  · exact hc j
  · exact le_rfl
  · exact le_rfl

@[simp] theorem stateWeight_deficit (c : Fin m → ℝ) : (stateWeight c : Label s m → ℝ) deficitLabel = 0 := rfl

theorem sumBody_stateWeight (K : Label s m → Body 3) (c : Fin m → ℝ) :
    sumBody K (stateWeight c) = ∑ j, c j • K (stateLabel j) := by
  simp [sumBody,stateWeight,Fintype.sum_sum_type,stateLabel]

def leftWeight (p : Fin m → ℝ) : Label s m → ℝ := unitWeight deficitLabel + stateWeight p

def leftBody (K : Label s m → Body 3) (p : Fin m → ℝ) : ConvexBody Plane :=
  deficit K + ∑ j, p j • state K j

def rightBody (K : Label s m → Body 3) (c : Fin m → ℝ) : ConvexBody Plane :=
  ∑ j, c j • state K j

theorem mapBody_fin_sum {ι : Type*} [Fintype ι] (f : Space 3 →L[ℝ] Plane)
    (B : ι → Body 3) : mapBody f (∑ i, B i) = ∑ i, mapBody f (B i) :=
  map_sum (mapBodyHom f) _ _

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.right_projection {K : Label s m → Body 3} (hK : Calibrated K) (c : Fin m → ℝ) :
    mapBody projectionIdentity (sumBody K (stateWeight c)) = rightBody K c := by
  rw [sumBody_stateWeight,mapBody_fin_sum]
  simp only [mapBody_smul,hK.identity_state,rightBody]

theorem _root_.MixedVolume.GeneralNormalization.Calibrated.left_projection {K : Label s m → Body 3} (hK : Calibrated K)
    (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) :
    mapBody projectionIdentity (sumBody K (leftWeight p)) = leftBody K p := by
  rw [leftWeight,sumBody_add K _ _ (unitWeight_nonneg _) (stateWeight_nonneg p hp),
    sumBody_unit,mapBody_add,hK.right_projection]
  change mapBody projectionIdentity (K deficitLabel) + rightBody K p = _
  rw [hK.place_deficit,mapBody_comp,projectionIdentity_embedXZ,ProjectedForcing.mapBody_id]
  rfl

theorem shift_left (A : Data s m) (p : Fin m → ℝ) (theta : ℝ) :
    shiftWeight (targetDelta A p theta) (leftWeight p) =
      unitWeight deficitLabel + (stateWeight (stationaryWeights A theta) : Label s m → ℝ) := by
  funext i
  rcases i with r | j | aj | u <;>
    simp [shiftWeight,leftWeight,stateWeight,unitWeight,ref,stateLabel,deficitLabel,
      Pi.single_apply,targetDelta,stationaryWeights] <;> ring

theorem canonical_left_shift (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    {theta : ℝ} (htheta : 0 < theta) :
    mapBody projectionIdentity
      (sumBody (canonical A hs) (shiftWeight (targetDelta A p theta) (leftWeight p))) =
      ∑ j, stationaryWeights A theta j • stateBody A hs j := by
  rw [shift_left,sumBody_add _ _ _ (unitWeight_nonneg _)
    (stateWeight_nonneg _ (stationaryWeights_nonneg A htheta)),sumBody_unit,canonical_deficit,zero_add]
  rw [(canonical_calibrated A hs).right_projection]
  simp only [rightBody,canonical_state_projection]

theorem canonical_right_shift (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (theta : ℝ) :
    mapBody projectionIdentity
      (sumBody (canonical A hs) (shiftWeight (targetDelta A p theta) (stateWeight (stationaryWeights A theta)))) =
      ∑ j, stationaryWeights A theta j • stateBody A hs j := by
  rw [shiftWeight_zero_deficit _ _ rfl,(canonical_calibrated A hs).right_projection]
  simp only [rightBody,canonical_state_projection]

theorem deficit_translates (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ) (hp : ProbabilityRow p)
    (theta : ℝ) (htheta : 0 < theta) {K : Label s m → Body 3}
    (h : RealizesTarget A hs (targetDelta A p theta) K) (hK : Calibrated K) :
    ∃ q : Plane, rightBody K (stationaryWeights A theta) = translateBody q (leftBody K p) := by
  let δ := targetDelta A p theta
  let w : Label s m → ℝ := leftWeight p
  let u : Label s m → ℝ := stateWeight (stationaryWeights A theta)
  let M : ConvexBody Plane := ∑ j, stationaryWeights A theta j • stateBody A hs j
  have hw : ∀ i, 0 ≤ w i := fun i => add_nonneg (unitWeight_nonneg _ i) (stateWeight_nonneg p hp.1 i)
  have hu : ∀ i, 0 ≤ u i := stateWeight_nonneg _ (stationaryWeights_nonneg A htheta)
  have hsw : ∀ i, 0 ≤ shiftWeight δ w i := by
    rw [show shiftWeight δ w = unitWeight deficitLabel + stateWeight (stationaryWeights A theta) from shift_left A p theta]
    exact fun i => add_nonneg (unitWeight_nonneg _ i) (hu i)
  have hsu : ∀ i, 0 ≤ shiftWeight δ u i := by
    rw [shiftWeight_zero_deficit _ _ rfl]
    exact hu
  have ha := safe_projected_identity h hK w hw hsw
  have hb := safe_projected_identity h hK u hu hsu
  rw [hK.left_projection p hp.1,canonical_left_shift A hs p htheta] at ha
  rw [hK.right_projection,canonical_right_shift] at hb
  have hc := safe_projected_identity h hK (w + u) (fun i => add_nonneg (hw i) (hu i)) (by
    rw [shiftWeight_add]
    exact fun i => add_nonneg (hsw i) (hsu i))
  rw [sumBody_add _ _ _ hw hu,mapBody_add,hK.left_projection p hp.1,hK.right_projection,
    shiftWeight_add,sumBody_add _ _ _ hsw hsu,mapBody_add,
    canonical_left_shift A hs p htheta,canonical_right_shift] at hc
  change volume.real (↑(leftBody K p + rightBody K (stationaryWeights A theta)) : Set Plane) =
    volume.real (↑(M + M) : Set Plane) at hc
  have hdouble : M + M = (2 : ℝ) • M := by
    simpa only [one_smul,one_add_one_eq_two] using (body_add_smul M zero_le_one zero_le_one).symm
  rw [hdouble,PlanarCorner.area_smul _ (by norm_num)] at hc
  obtain ⟨q,hq⟩ := equal_area_translates (leftBody K p).convex (leftBody K p).isCompact
    (rightBody K (stationaryWeights A theta)).convex (rightBody K (stationaryWeights A theta)).isCompact
    (by rw [ha]; exact stationary_scaled_area_pos A hs htheta) (by rw [ha,hb]) (by
      rw [← ConvexBody.coe_add,hc,ha]
      norm_num [M])
  exact ⟨q,ConvexBody.ext (by simpa only [coe_translateBody] using hq)⟩

theorem weighted_states_translate {K : Label s m → Body 3} (A : Data s m) (hs : 0 < s)
    (t : Fin m → Plane) (ht : ∀ j, state K j = translateBody (t j) (stateBody A hs j))
    (c : Fin m → ℝ) :
    (∑ j, c j • state K j) = translateBody (∑ j, c j • t j) (∑ j, c j • stateBody A hs j) := by
  simp only [ht,ProjectedForcing.smul_translateBody]
  exact sum_translateBody _ _

/-- The full geometric converse, including all input quantifiers and every
finite word, is obtained from an arbitrary realization of the complete cubic. -/
theorem realization_implies_cutpoint (A : Data s m) (hs : 0 < s) (p : Fin m → ℝ)
    (hp : ProbabilityRow p) (theta : ℝ) (htheta₀ : 0 < theta) (htheta₁ : theta < 1)
    {K : Label s m → Body 3} (h : RealizesTarget A hs (targetDelta A p theta) K) :
    A.UniversalCutpoint p theta := by
  obtain ⟨L,hL,hcal,t,ht⟩ := normalize_target h
  obtain ⟨q,hq⟩ := deficit_translates A hs p hp theta htheta₀ hL hcal
  let tp : Plane := ∑ j, p j • t j
  let tt : Plane := ∑ j, stationaryWeights A theta j • t j
  have hpbody := weighted_states_translate A hs t ht p
  have htBody := weighted_states_translate A hs t ht (stationaryWeights A theta)
  change rightBody L (stationaryWeights A theta) = translateBody q (leftBody L p) at hq
  rw [rightBody,htBody,leftBody,hpbody] at hq
  have hleft : deficit L + translateBody tp (∑ j, p j • stateBody A hs j) =
      translateBody tp (deficit L + ∑ j, p j • stateBody A hs j) := by
    simp only [translateBody]
    ac_rfl
  change translateBody tt (∑ j, stationaryWeights A theta j • stateBody A hs j) =
    translateBody q (deficit L + translateBody tp (∑ j, p j • stateBody A hs j)) at hq
  rw [hleft,translateBody_translate] at hq
  have hh := congrArg (translateBody (-(q + tp))) hq
  rw [translateBody_translate,translateBody_translate,neg_add_cancel,translateBody_zero,
    stationary_scaled] at hh
  apply (summand_iff_universalCutpoint A hs p hp theta htheta₀ htheta₁).mp
  exact ⟨deficit L,-(q + tp) + tt,hh.symm⟩

end MixedVolume.GeneralDeficit

end
