module

public import Continuation.Geometry.OriginalLatticeSubdivision

@[expose] public section

/-!
# Every ray of the original canonical seed

This proof transports the complete one-dimensional-cone characterization.
The labels are the literal original integral vectors, with no rescaling,
finite-instance restriction, or assumption about a chosen ray enumeration.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical NNReal

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

private theorem map_coordinate_ray (w : N) :
    (PointedCone.hull ℝ {PaperVerification.ToricGeometry.embed n (b.equivFun w)}).map
        (realCoordinates b hi).symm.toLinearMap = PointedCone.hull ℝ {ι w} := by
  change Submodule.map ((realCoordinates b hi).symm.toLinearMap.restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 {PaperVerification.ToricGeometry.embed n (b.equivFun w)}) = _
  rw [Submodule.map_span]
  change PointedCone.hull ℝ
    ((realCoordinates b hi).symm '' {PaperVerification.ToricGeometry.embed n (b.equivFun w)}) = _
  rw [Set.image_singleton, realCoordinates_symm_lattice, LinearEquiv.symm_apply_apply]

theorem transported_seed_rays (U : Finset N)
    (Ψ : Fan (Unimodular.FanBridge.standardEmbedding n))
    (hΨ : ∀ R : PointedCone ℝ (Ambient n),
      (R ∈ Ψ.cones ∧ Module.finrank ℝ (Submodule.span ℝ (R : Set (Ambient n))) = 1) ↔
        ∃ w ∈ U.image b.equivFun,
          R = PointedCone.hull ℝ {PaperVerification.ToricGeometry.embed n w}) :
    ∀ R : PointedCone ℝ V,
      (R ∈ (transportFan b hi Ψ).cones ∧
        Module.finrank ℝ (Submodule.span ℝ (R : Set V)) = 1) ↔
          ∃ w ∈ U, R = PointedCone.hull ℝ {ι w} := by
  intro R
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hd⟩
    change Module.finrank ℝ (Submodule.span ℝ
      ((C.map (realCoordinates b hi).symm.toLinearMap : PointedCone ℝ V) : Set V)) = 1 at hd
    rw [PointedCone.coe_map, Submodule.span_image,
      (realCoordinates b hi).symm.finrank_map_eq] at hd
    obtain ⟨w, hw, rfl⟩ := (hΨ C).mp ⟨hC, hd⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨z, hz, map_coordinate_ray b hi z⟩
  · rintro ⟨w, hw, rfl⟩
    have hc := (hΨ (PointedCone.hull ℝ
      {PaperVerification.ToricGeometry.embed n (b.equivFun w)})).mpr
        ⟨b.equivFun w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, rfl⟩
    rw [← map_coordinate_ray b hi w]
    refine ⟨⟨_, hc.1, rfl⟩, ?_⟩
    rw [PointedCone.coe_map, Submodule.span_image,
      (realCoordinates b hi).symm.finrank_map_eq]
    exact hc.2

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.transported_seed_rays
