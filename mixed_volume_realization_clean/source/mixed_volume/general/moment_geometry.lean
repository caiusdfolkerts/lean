module

public import mixed_volume.general.automaton_moments

/-! Exact geometric meaning of the word moments and the mixed areas of
transition images with distinct first-letter directions. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.MomentGeometry

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonMoments SeriesMixedArea
open VolumePolynomials.PlanarMixedForm Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

theorem linearWidth_series (hs : 0 < s) (l : Plane →L[ℝ] ℝ) (u : Word s → Plane)
    (hu : Summable fun w => ‖u w‖) :
    ReferenceExpansion.linearWidth l (IndexedSeries.segmentSeriesBody u hu) =
      ∑' w, |l (u w)| := by
  let e := wordEnumeration hs
  rw [← reindex_body e u hu, indexed_nat_eq]
  change volume.real (l '' VolumePolynomials.segmentSeries (fun n => u (e n))) = _
  rw [SeriesProjection.length_image_segmentSeries l _ (e.summable_iff.mpr hu)]
  exact e.tsum_eq (fun w => |l (u w)|)

theorem weighted_generator (A : Data s m) (j : Fin m) (w : Word s) :
    A.weight w j • generator w = (firstTerm A j w, massTerm A j w) := by
  ext <;> simp only [generator, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    firstTerm, massTerm] <;> ring

theorem firstTerm_nonneg (A : Data s m) (hs : 0 < s) (j : Fin m) (w : Word s) :
    0 ≤ firstTerm A j w := mul_nonneg (massTerm_nonneg A hs j w) (tag_nonneg w)

theorem state_height (A : Data s m) (hs : 0 < s) (j : Fin m) :
    PlanarCorner.height (stateBody A hs j) = mass A j := by
  change ReferenceExpansion.linearWidth (ContinuousLinearMap.snd ℝ ℝ ℝ) (stateBody A hs j) = _
  rw [stateBody, linearWidth_series hs]
  change (∑' w, |(A.weight w j • generator w).2|) = _
  simp_rw [weighted_generator, abs_of_nonneg (massTerm_nonneg A hs j _)]
  rfl

theorem state_width (A : Data s m) (hs : 0 < s) (j : Fin m) :
    PlanarCorner.width (stateBody A hs j) = first A j := by
  change ReferenceExpansion.linearWidth (ContinuousLinearMap.fst ℝ ℝ ℝ) (stateBody A hs j) = _
  rw [stateBody, linearWidth_series hs]
  change (∑' w, |(A.weight w j • generator w).1|) = _
  simp_rw [weighted_generator, abs_of_nonneg (firstTerm_nonneg A hs j _)]
  rfl

theorem image_width (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m) :
    PlanarCorner.width (mapBody (transition a) (stateBody A hs j)) =
      rho s / base s * (first A j + ((a.val : ℝ) + 1) * mass A j) := by
  rw [stateBody, IndexedSeries.map_segmentSeriesBody]
  change ReferenceExpansion.linearWidth (ContinuousLinearMap.fst ℝ ℝ ℝ) _ = _
  rw [linearWidth_series hs]
  have hterm (w : Word s) :
      |(ContinuousLinearMap.fst ℝ ℝ ℝ) (transition a (A.weight w j • generator w))| =
        rho s / base s * (firstTerm A j w + ((a.val : ℝ) + 1) * massTerm A j w) := by
    rw [weighted_generator]
    change |rho s / base s * (firstTerm A j w + ((a.val : ℝ) + 1) * massTerm A j w)| = _
    apply abs_of_nonneg
    exact mul_nonneg (div_nonneg (rho_pos hs).le (base_pos s).le)
      (add_nonneg (firstTerm_nonneg A hs j w)
        (mul_nonneg (by positivity) (massTerm_nonneg A hs j w)))
  simp_rw [hterm]
  rw [tsum_mul_left, Summable.tsum_add (first_summable A hs j)
    ((mass_summable A hs j).mul_left _), tsum_mul_left]
  rfl

def imageFactor (s : ℕ) : ℝ := rho s ^ 2 / base s

theorem imageFactor_nonneg (hs : 0 < s) : 0 ≤ imageFactor s :=
  div_nonneg (sq_nonneg _) (base_pos s).le

theorem transition_det (a : Fin s) : LinearMap.det (transition a).toLinearMap = imageFactor s := by
  have heq : (transition a).toLinearMap =
      PlanarExtrusion.frameMap (rho s / base s, 0)
        (rho s / base s * ((a.val : ℝ) + 1), rho s) := by
    ext p <;> dsimp [transition, PlanarExtrusion.frameMap] <;> ring
  rw [heq, PlanarExtrusion.frameMap_det]
  dsimp [imageFactor, PlanarExtrusion.determinant]
  ring

theorem mixed_same_image (A : Data s m) (hs : 0 < s) (a : Fin s) (j k : Fin m) :
    2 * mixedArea volume (mapBody (transition a) (stateBody A hs j))
      (mapBody (transition a) (stateBody A hs k)) =
        imageFactor s * (2 * mixedArea volume (stateBody A hs j) (stateBody A hs k)) := by
  rw [PlanarEdges.mixedArea_mapBody, transition_det,
    abs_of_nonneg (imageFactor_nonneg hs)]
  ring

theorem determinant_images (A : Data s m) (a b : Fin s) (j k : Fin m) (u v : Word s) :
    det (transition a (A.weight u j • generator u))
      (transition b (A.weight v k • generator v)) =
      imageFactor s * massTerm A j u * massTerm A k v *
        (tag u - tag v + (a.val : ℝ) - (b.val : ℝ)) := by
  simp only [weighted_generator, transition_apply]
  dsimp [det, PlanarExtrusion.determinant, imageFactor, firstTerm]
  ring

theorem abs_determinant_images_lt (A : Data s m) (hs : 0 < s)
    (a b : Fin s) (hab : a < b) (j k : Fin m) (u v : Word s) :
    |det (transition a (A.weight u j • generator u))
      (transition b (A.weight v k • generator v))| =
      imageFactor s * (((b.val : ℝ) - (a.val : ℝ)) * massTerm A j u * massTerm A k v +
        massTerm A j u * firstTerm A k v - firstTerm A j u * massTerm A k v) := by
  rw [determinant_images]
  have hsign : tag u - tag v + (a.val : ℝ) - (b.val : ℝ) ≤ 0 := by
    have ha : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast hab
    linarith [tag_lt_one u, tag_nonneg v]
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (imageFactor_nonneg hs) (massTerm_nonneg A hs j u))
      (massTerm_nonneg A hs k v)) hsign)]
  dsimp [firstTerm]
  ring

theorem signed_pair_sum (A : Data s m) (hs : 0 < s) (j k : Fin m) (d : ℝ) :
    (∑' u, ∑' v, (d * massTerm A j u * massTerm A k v +
      massTerm A j u * firstTerm A k v - firstTerm A j u * massTerm A k v)) =
      d * mass A j * mass A k + mass A j * first A k - first A j * mass A k := by
  have hi (u : Word s) :
      (∑' v, (d * massTerm A j u * massTerm A k v +
        massTerm A j u * firstTerm A k v - firstTerm A j u * massTerm A k v)) =
        d * massTerm A j u * mass A k + massTerm A j u * first A k - firstTerm A j u * mass A k := by
    rw [Summable.tsum_sub
      (((mass_summable A hs k).mul_left _).add ((first_summable A hs k).mul_left _))
      ((mass_summable A hs k).mul_left _),
      Summable.tsum_add ((mass_summable A hs k).mul_left _)
        ((first_summable A hs k).mul_left _)]
    simp only [tsum_mul_left, mass, first]
  simp_rw [hi]
  rw [Summable.tsum_sub
    ((((mass_summable A hs j).mul_left d).mul_right (mass A k)).add
      ((mass_summable A hs j).mul_right (first A k)))
    ((first_summable A hs j).mul_right (mass A k)),
    Summable.tsum_add (((mass_summable A hs j).mul_left d).mul_right (mass A k))
      ((mass_summable A hs j).mul_right (first A k))]
  simp only [tsum_mul_left, tsum_mul_right, mass, first]

/-- Distinct first-letter cylinders have a fixed determinant sign; their full
mixed areas therefore reduce to the already computed linear moments. -/
theorem mixed_distinct_images_lt (A : Data s m) (hs : 0 < s)
    (a b : Fin s) (hab : a < b) (j k : Fin m) :
    2 * mixedArea volume (mapBody (transition a) (stateBody A hs j))
      (mapBody (transition b) (stateBody A hs k)) =
      imageFactor s * (((b.val : ℝ) - (a.val : ℝ)) * mass A j * mass A k +
        mass A j * first A k - first A j * mass A k) := by
  rw [stateBody, stateBody, IndexedSeries.map_segmentSeriesBody,
    IndexedSeries.map_segmentSeriesBody, twice_mixed_words hs]
  simp_rw [abs_determinant_images_lt A hs a b hab j k, tsum_mul_left]
  rw [signed_pair_sum A hs j k]

end MixedVolume.MomentGeometry

end
