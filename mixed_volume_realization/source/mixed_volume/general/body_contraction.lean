module

public import mixed_volume.general.automaton_words
public import mixed_volume.general.series_support

/-! Quantitative contraction and translation-error removal for the full finite
stochastic system of actual compact convex planar bodies. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.BodyContraction

open VolumePolynomials AutomatonWords Set Metric
open scoped Pointwise BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_close (K L : ConvexBody E) {x : E} (hx : x ∈ K) :
    ∃ y ∈ L, dist x y ≤ dist K L := by
  obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  refine ⟨y, hy, ?_⟩
  rw [← hxy]
  exact infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top

theorem dist_add_le (K L K' L' : ConvexBody E) :
    dist (K + L) (K' + L') ≤ dist K K' + dist L L' := by
  apply hausdorffDist_le_of_mem_dist (add_nonneg dist_nonneg dist_nonneg)
  · rintro x ⟨u, hu, v, hv, rfl⟩
    obtain ⟨u', hu', hdu⟩ := exists_close K K' hu
    obtain ⟨v', hv', hdv⟩ := exists_close L L' hv
    refine ⟨u' + v', ⟨u', hu', v', hv', rfl⟩, ?_⟩
    exact (dist_add_add_le u v u' v').trans (add_le_add hdu hdv)
  · rintro x ⟨u', hu', v', hv', rfl⟩
    obtain ⟨u, hu, hdu⟩ := exists_close K' K hu'
    obtain ⟨v, hv, hdv⟩ := exists_close L' L hv'
    refine ⟨u + v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
    have h := (dist_add_add_le u' v' u v).trans (add_le_add hdu hdv)
    simpa only [dist_comm K' K, dist_comm L' L] using h

theorem dist_map_le (f : E →L[ℝ] F) (K L : ConvexBody E) :
    dist (mapBody f K) (mapBody f L) ≤ ‖f‖ * dist K L := by
  apply hausdorffDist_le_of_mem_dist (mul_nonneg (norm_nonneg f) dist_nonneg)
  · rintro x ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hd⟩ := exists_close K L hu
    refine ⟨f v, ⟨v, hv, rfl⟩, ?_⟩
    calc
      dist (f u) (f v) = ‖f (u - v)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖f‖ * ‖u - v‖ := f.le_opNorm _
      _ ≤ ‖f‖ * dist K L := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hd (norm_nonneg f)
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hd⟩ := exists_close L K hv
    refine ⟨f u, ⟨u, hu, rfl⟩, ?_⟩
    calc
      dist (f v) (f u) = ‖f (v - u)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖f‖ * ‖v - u‖ := f.le_opNorm _
      _ ≤ ‖f‖ * dist L K := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hd (norm_nonneg f)
      _ = ‖f‖ * dist K L := by rw [dist_comm L K]

theorem dist_smul_le (K L : ConvexBody E) (r : ℝ) (hr : 0 ≤ r) :
    dist (r • K) (r • L) ≤ r * dist K L := by
  apply hausdorffDist_le_of_mem_dist (mul_nonneg hr dist_nonneg)
  · rintro x ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hd⟩ := exists_close K L hu
    refine ⟨r • v, ⟨v, hv, rfl⟩, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hd hr
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hd⟩ := exists_close L K hv
    refine ⟨r • u, ⟨u, hu, rfl⟩, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr, dist_comm K L]
    exact mul_le_mul_of_nonneg_left hd hr

theorem dist_sum_le {κ : Type*} (q : Finset κ) (K L : κ → ConvexBody E) :
    dist (∑ j ∈ q, K j) (∑ j ∈ q, L j) ≤ ∑ j ∈ q, dist (K j) (L j) := by
  classical
  induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih =>
    simp only [Finset.sum_insert hj]
    exact (dist_add_le _ _ _ _).trans (add_le_add le_rfl ih)

theorem dist_translate_le (K L : ConvexBody E) (v : E) :
    dist (translateBody v K) (translateBody v L) ≤ dist K L := by
  have h := dist_add_le (pointBody v) K (pointBody v) L
  simpa only [translateBody, dist_self, zero_add] using h

variable {s m : ℕ}

theorem transition_norm_le (hs : 0 < s) (a : Fin s) : ‖transition a‖ ≤ rho s := by
  apply ContinuousLinearMap.opNorm_le_bound _ (rho_pos hs).le
  intro p
  have hx : |p.1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le p
  have hy : |p.2| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le p
  have ha : 0 ≤ (a.val : ℝ) + 1 := by positivity
  have haq : (a.val : ℝ) + 2 ≤ base s := by
    dsimp [base]
    have h : a.val + 2 ≤ s + 1 := by omega
    exact_mod_cast h
  have hsum : |p.1 + ((a.val : ℝ) + 1) * p.2| ≤ base s * ‖p‖ := by
    have h := norm_add_le p.1 (((a.val : ℝ) + 1) * p.2)
    simp only [Real.norm_eq_abs] at h
    rw [abs_mul, abs_of_nonneg ha] at h
    have hmul := mul_le_mul_of_nonneg_left hy ha
    have hq := mul_le_mul_of_nonneg_right haq (norm_nonneg p)
    nlinarith
  change max ‖rho s / base s * (p.1 + ((a.val : ℝ) + 1) * p.2)‖
    ‖rho s * p.2‖ ≤ rho s * ‖p‖
  apply max_le
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (rho_pos hs).le (base_pos s).le)]
    calc
      rho s / base s * |p.1 + ((a.val : ℝ) + 1) * p.2| ≤
          rho s / base s * (base s * ‖p‖) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (rho_pos hs).le (base_pos s).le)
      _ = rho s * ‖p‖ := by field_simp [(base_pos s).ne']
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rho_pos hs)]
    exact mul_le_mul_of_nonneg_left hy (rho_pos hs).le

theorem stochastic_sum_bound (A : Data s m) (hs : 0 < s) (j : Fin m)
    (b : Fin s → Fin m → ℝ) (R : ℝ)
    (hb : ∀ a k, b a k ≤ A.P a j k * (rho s * R)) :
    (∑ a, ∑ k, b a k) ≤ (1 / 4 : ℝ) * R := by
  calc
    (∑ a, ∑ k, b a k) ≤ ∑ a, ∑ k, A.P a j k * (rho s * R) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun k _ => hb a k))
    _ = (s : ℝ) * (rho s * R) := by
      simp only [← Finset.sum_mul, A.P_sum, one_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = (1 / 4 : ℝ) * R := by rw [← mul_assoc, card_mul_rho hs]

def vectorOperator (A : Data s m) : (Fin m → Plane) →ₗ[ℝ] (Fin m → Plane) where
  toFun z j := ∑ a, ∑ k, A.P a j k • transition a (z k)
  map_add' z t := by
    funext j
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext j
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm _ _ _

theorem vectorOperator_norm (A : Data s m) (hs : 0 < s) (z : Fin m → Plane) :
    ‖vectorOperator A z‖ ≤ (1 / 4 : ℝ) * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  calc
    ‖(vectorOperator A z) j‖ ≤ ∑ a, ‖∑ k, A.P a j k • transition a (z k)‖ := by
      change ‖∑ a, ∑ k, A.P a j k • transition a (z k)‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ a, ∑ k, ‖A.P a j k • transition a (z k)‖ :=
      Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ (1 / 4 : ℝ) * ‖z‖ := by
      apply stochastic_sum_bound A hs j
      intro a k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (A.P_nonneg a j k)]
      apply mul_le_mul_of_nonneg_left _ (A.P_nonneg a j k)
      exact ((transition a).le_opNorm (z k)).trans
        ((mul_le_mul_of_nonneg_right (transition_norm_le hs a) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm z k) (rho_pos hs).le))

/-- The translation error is solved by a bijective finite-dimensional linear
map.  Surjectivity follows from the proved contraction estimate. -/
theorem translation_centers (A : Data s m) (hs : 0 < s) (v : Fin m → Plane) :
    ∃ z : Fin m → Plane, z = v + vectorOperator A z := by
  let J : (Fin m → Plane) →ₗ[ℝ] (Fin m → Plane) := LinearMap.id - vectorOperator A
  have hinj : Function.Injective J := by
    apply (injective_iff_map_eq_zero J).2
    intro z hz
    change z - vectorOperator A z = 0 at hz
    have heq : z = vectorOperator A z := sub_eq_zero.mp hz
    have h := vectorOperator_norm A hs z
    rw [← heq] at h
    apply norm_eq_zero.mp
    linarith [norm_nonneg z]
  obtain ⟨z, hz⟩ := (LinearMap.surjective_of_injective hinj) v
  refine ⟨z, ?_⟩
  change z - vectorOperator A z = v at hz
  exact sub_eq_iff_eq_add.mp hz

def bodyOperator (A : Data s m) (K : Fin m → ConvexBody Plane) (j : Fin m) : ConvexBody Plane :=
  (1 + A.f j) • PlanarCorner.unitY + ∑ a, ∑ k, A.P a j k • mapBody (transition a) (K k)

theorem bodyOperator_dist (A : Data s m) (hs : 0 < s)
    (K L : Fin m → ConvexBody Plane) :
    dist (bodyOperator A K) (bodyOperator A L) ≤ (1 / 4 : ℝ) * dist K L := by
  apply (dist_pi_le_iff (by positivity)).2
  intro j
  have h₀ := dist_add_le ((1 + A.f j) • PlanarCorner.unitY)
    (∑ a, ∑ k, A.P a j k • mapBody (transition a) (K k))
    ((1 + A.f j) • PlanarCorner.unitY)
    (∑ a, ∑ k, A.P a j k • mapBody (transition a) (L k))
  simp only [dist_self, zero_add] at h₀
  refine h₀.trans ((dist_sum_le _ _ _).trans ?_)
  calc
    (∑ a, dist (∑ k, A.P a j k • mapBody (transition a) (K k))
        (∑ k, A.P a j k • mapBody (transition a) (L k))) ≤
      ∑ a, ∑ k, dist (A.P a j k • mapBody (transition a) (K k))
        (A.P a j k • mapBody (transition a) (L k)) :=
          Finset.sum_le_sum fun a _ => dist_sum_le _ _ _
    _ ≤ (1 / 4 : ℝ) * dist K L := by
      apply stochastic_sum_bound A hs j
      intro a k
      refine (dist_smul_le _ _ _ (A.P_nonneg a j k)).trans ?_
      apply mul_le_mul_of_nonneg_left _ (A.P_nonneg a j k)
      refine (dist_map_le _ _ _).trans ?_
      exact (mul_le_mul_of_nonneg_right (transition_norm_le hs a) dist_nonneg).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist K L k) (rho_pos hs).le)

theorem bodyOperator_unique (A : Data s m) (hs : 0 < s)
    (K L : Fin m → ConvexBody Plane)
    (hK : ∀ j, K j = bodyOperator A K j) (hL : ∀ j, L j = bodyOperator A L j) : K = L := by
  have h := bodyOperator_dist A hs K L
  rw [← funext hK, ← funext hL] at h
  apply dist_eq_zero.mp
  linarith [dist_nonneg (x := K) (y := L)]

theorem bodyOperator_translate (A : Data s m) (K : Fin m → ConvexBody Plane)
    (z : Fin m → Plane) (j : Fin m) :
    bodyOperator A (fun k => translateBody (z k) (K k)) j =
      translateBody (vectorOperator A z j) (bodyOperator A K j) := by
  unfold bodyOperator
  simp_rw [mapBody_translate, ProjectedForcing.smul_translateBody, sum_translateBody]
  change (1 + A.f j) • PlanarCorner.unitY +
    translateBody (vectorOperator A z j)
      (∑ a, ∑ k, A.P a j k • mapBody (transition a) (K k)) = _
  dsimp [translateBody]
  ac_rfl

theorem translated_bodyOperator_unique (A : Data s m) (hs : 0 < s)
    (K L : Fin m → ConvexBody Plane) (v : Fin m → Plane)
    (hK : ∀ j, K j = translateBody (v j) (bodyOperator A K j))
    (hL : ∀ j, L j = translateBody (v j) (bodyOperator A L j)) : K = L := by
  have heach (j : Fin m) : dist (K j) (L j) ≤ dist (bodyOperator A K j) (bodyOperator A L j) := by
    rw [hK j, hL j]
    exact dist_translate_le _ _ _
  have h₁ : dist K L ≤ dist (bodyOperator A K) (bodyOperator A L) := by
    apply (dist_pi_le_iff dist_nonneg).2
    intro j
    exact (heach j).trans (dist_le_pi_dist _ _ j)
  have h₂ := bodyOperator_dist A hs K L
  apply dist_eq_zero.mp
  linarith [dist_nonneg (x := K) (y := L)]

/-- Translation errors can always be absorbed into independent centres, with
no hypothesis on their size. -/
theorem unique_up_to_translations (A : Data s m) (hs : 0 < s)
    (canonical K : Fin m → ConvexBody Plane)
    (hcanonical : ∀ j, canonical j = bodyOperator A canonical j)
    (v : Fin m → Plane)
    (hK : ∀ j, K j = translateBody (v j) (bodyOperator A K j)) :
    ∃ z : Fin m → Plane, ∀ j, K j = translateBody (z j) (canonical j) := by
  obtain ⟨z, hz⟩ := translation_centers A hs v
  refine ⟨z, ?_⟩
  have hL (j : Fin m) : translateBody (z j) (canonical j) =
      translateBody (v j) (bodyOperator A (fun k => translateBody (z k) (canonical k)) j) := by
    rw [bodyOperator_translate, translateBody_translate, ← hcanonical j]
    congr 1
    exact congrFun hz j
  have heq := translated_bodyOperator_unique A hs K
    (fun j => translateBody (z j) (canonical j)) v hK hL
  exact congrFun heq

end MixedVolume.BodyContraction

end
