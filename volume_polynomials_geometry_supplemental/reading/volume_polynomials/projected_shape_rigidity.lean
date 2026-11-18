module

public import VolumePolynomials.PlanarComparison
public import VolumePolynomials.ProjectionCycle
public import VolumePolynomials.ProjectionCoordinates
public import VolumePolynomials.ExtrusionTransport
public import VolumePolynomials.PlanarLinearExtrusion

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

theorem lift_projected_translation (e : Plane ≃L[ℝ] Plane)
    (A B : Set Plane) (v : Plane) (h : e '' B = v +ᵥ A) :
    B = e.symm v +ᵥ e.symm '' A := by
  first
  | have hi := congrArg (Set.image e.symm) h
    simpa only [linear_image_vadd, Set.image_image, Function.comp_apply,
      e.symm_apply_apply, Set.image_id'] using hi

def lastProjectedSet (lam : ℝ) (C : Set Plane) : Set Plane :=
  centeredSegment (1, 0) + lastTransport lam '' C

theorem lastProjectedSet_isCompact (lam : ℝ) (C : Set Plane) (hC : IsCompact C) :
    IsCompact (lastProjectedSet lam C) :=
  (centeredSegment_isCompact (1, 0)).add (hC.image (lastTransport lam).continuous)

theorem lastProjectedSet_convex (lam : ℝ) (C : Set Plane) (hC : Convex ℝ C) :
    Convex ℝ (lastProjectedSet lam C) :=
  (centeredSegment_convex (1, 0)).add (hC.linear_image (lastTransport lam).toLinearMap)

/-- The exact three planar area comparisons force the return equation. All three
equality cases are obtained from the proved Brunn–Minkowski equality theorem. -/
theorem projected_comparisons_force_shape
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A B C : Set Plane)
    (hAc : IsCompact A) (hA : Convex ℝ A)
    (hBc : IsCompact B) (hB : Convex ℝ B)
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (hApos : 0 < volume.real A)
    (hAB : volume.real (transport01 '' B) = volume.real A)
    (hABsum : volume.real (A + transport01 '' B) = 4 * volume.real A)
    (hBpos : 0 < volume.real B)
    (hBC : volume.real (transport12 '' C) = volume.real B)
    (hBCsum : volume.real (B + transport12 '' C) = 4 * volume.real B)
    (hAD : volume.real (lastProjectedSet lam C) = volume.real A)
    (hADsum : volume.real (A + lastProjectedSet lam C) = 4 * volume.real A) :
    ∃ a₀ b₀ c₀ : Plane,
      A = a₀ +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      B = b₀ +ᵥ transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      C = c₀ +ᵥ transport12 ''
        (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | obtain ⟨b, hb⟩ := equal_area_translates hA hAc
      (hB.linear_image transport01.toLinearMap) (hBc.image transport01.continuous)
      hApos hAB hABsum
    have hb' : B = transport01 b +ᵥ transport01 '' A :=
      lift_projected_translation transport01 A B b hb
    obtain ⟨c, hc⟩ := equal_area_translates hB hBc
      (hC.linear_image transport12.toLinearMap) (hCc.image transport12.continuous)
      hBpos hBC hBCsum
    have hc' : C = transport12 c +ᵥ transport12 '' B :=
      lift_projected_translation transport12 B C c hc
    obtain ⟨d, hd⟩ := equal_area_translates hA hAc
      (lastProjectedSet_convex lam C hC) (lastProjectedSet_isCompact lam C hCc)
      hApos hAD hADsum
    have hd' : A = -d +ᵥ lastProjectedSet lam C := by
      rw [hd]
      simp only [vadd_vadd, vadd_eq_add, neg_add_cancel, zero_vadd]
    have hAn : A.Nonempty := by
      by_contra hn
      have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he] at hApos
    exact projection_cycle_forces_three_bodies lam hlam₀ hlam₁ A B C hAc hAn
      (transport01 b) (transport12 c) (-d) hb' hc' hd'

theorem extrusionV_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionV) - volume.real K =
      volume.real (projectionV '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameV
      frameV_measurePreserving hKc hK frameV_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

theorem extrusionW_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionW) - volume.real K =
      volume.real (projectionW '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameW
      frameW_measurePreserving hKc hK frameW_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

theorem extrusionZ_eq_projected_area (K : Set ThreeSpace)
    (hKc : IsCompact K) (hK : Convex ℝ K) :
    volume.real (K + centeredSegment directionZ) - volume.real K =
      volume.real (projectionZ '' K) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment frameZ
      frameZ_measurePreserving hKc hK frameZ_direction
    rw [← centeredSegment_eq_image] at h
    rw [h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl


end VolumePolynomials.Holonomy
