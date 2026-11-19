module

public import ToricPower.CompletedStarPacking
public import ToricPower.LiftedSubfanIntersections
public import ToricPower.FanAttachmentOldFaces

/-!
# The packing retains the original fan as the full subfan on its rays

For an original cone outside the selected star, the actual separating
character removes every new-ray contribution. For an original cone in
the star, the exact quotient old-face intersection theorem applies.
Together these identify every old intersection, including all faces
of the attached cones.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)
  (completion : SmoothDivisorialCompletion (canonicalRayStar fan ray))

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "q" => Submodule.mkQ (Submodule.span ℝ {i a})
local notation "star" => canonicalRayStar fan ray

theorem completedStarCone_oldFace (M : ℕ) (σ : completion.fan.cones) :
    completedStarCone fan regular ray completion M
      (subfanConeEmbedding star completion.fan completion.contains
        (completionStarOldFace fan ray completion σ)) =
      (completionOriginalStarFace fan ray completion σ).val.val := by
  rw [← completionOriginalStarFace_projection fan ray completion σ]
  exact completedStarCone_old fan regular ray completion M _

theorem completedStarCone_inf_old (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M)
    (σ : completion.fan.cones) (τ : fan.cones) :
    completedStarCone fan regular ray completion M σ ⊓ τ.val =
      (completionOriginalStarFace fan ray completion σ).val.val ⊓ τ.val := by
  by_cases contains : ray.toCone ≤ τ
  · let old : OriginalRayStarCone fan ray := ⟨τ,contains⟩
    have calculation := liftedCone_inf_oldFace_eq star completion.fan completion.contains
      completion.regular ((isFullOnRays_iff_local star completion.fan).mpr completion.oldRayClosed)
      (i a) (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) q
      (selectedRay_projection_zero fan ray)
      (completedStarRayLift_real_projects fan regular ray completion M)
      σ (originalStarProjection fan ray old)
    change completedStarCone fan regular ray completion M σ ⊓
        completedStarCone fan regular ray completion M
          (subfanConeEmbedding star completion.fan completion.contains
            (originalStarProjection fan ray old)) =
      completedStarCone fan regular ray completion M
          (subfanConeEmbedding star completion.fan completion.contains
            (completionStarOldFace fan ray completion σ)) ⊓
        completedStarCone fan regular ray completion M
          (subfanConeEmbedding star completion.fan completion.contains
            (originalStarProjection fan ray old)) at calculation
    rw [completedStarCone_old fan regular ray completion M old,
      completedStarCone_oldFace] at calculation
    exact calculation
  · let old := completionOriginalStarFace fan ray completion σ
    let p : StarSeparatorIndex fan ray := ⟨(old.val,τ),old.property,contains⟩
    let m := starSeparator fan ray p
    let form := fan.lattice.realCharacter m
    let newRays := newConeRayLifts star completion.fan
      (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) σ
    have spec := starSeparator_spec fan ray p
    have nonnegative : ∀ x ∈ old.val.val, 0 ≤ form x :=
      (mem_dualSemigroup fan.lattice m).mp spec.1
    have nonpositive : ∀ x ∈ τ.val, form x ≤ 0 := by
      intro x member
      have value := (mem_dualSemigroup fan.lattice (-m)).mp spec.2.1 member
      rw [map_neg,LinearMap.neg_apply] at value
      exact neg_nonneg.mp value
    have positive : ∀ v ∈ newRays, 0 < form v := by
      rintro _ ⟨ρ,⟨_,newRay⟩,rfl⟩
      change 0 < fan.lattice.realCharacter m
        (i (completedStarRayLift fan regular ray completion M ρ))
      rw [fan.lattice.realCharacter_apply]
      exact_mod_cast completedStarPacking_positive fan regular ray completion M large p ρ newRay
    rw [completedStarCone_split]
    exact FanPacking.adjoining_positive_generators_inf old.val.val τ.val form
      nonnegative nonpositive newRays positive

theorem completedStarPackedFan_fullOnRays (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M) :
    IsFullOnRays fan (completedStarPackedFan fan regular ray completion M large) := by
  apply attachFiniteCones_fullOnRays fan (completedStarCone fan regular ray completion M)
    (fun σ => (completedStarCone_regular fan regular ray completion M σ).toIsToricCone)
    (completedStarCone_intersections fan regular ray completion M)
    (completedStarCone_old_intersections fan regular ray completion M large)
    (fun σ => (completionOriginalStarFace fan ray completion σ).val)
  exact completedStarCone_inf_old fan regular ray completion M large

end ToricPower.FanSubdivision
end

