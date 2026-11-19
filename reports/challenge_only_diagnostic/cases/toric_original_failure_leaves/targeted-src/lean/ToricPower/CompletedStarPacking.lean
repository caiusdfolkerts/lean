module

public import ToricPower.CompletedStarRayLifts
public import ToricPower.RegularLiftedFan
public import ToricPower.FiniteFanAttachment

/-!
# Attaching a completed quotient star without changing the original fan

This is the actual one-ray packing construction. Its sole inductive
input is a regular divisorial completion of the lower-rank quotient star.
The new integral rays and all face-intersection proofs are constructed
explicitly. Every original cone remains a cone in the same lattice.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "qZ" => Submodule.mkQ (Submodule.span ℤ {a})
local notation "q" => Submodule.mkQ (Submodule.span ℝ {i a})
local notation "star" => canonicalRayStar fan ray

variable (completion : SmoothDivisorialCompletion (canonicalRayStar fan ray))

def completedStarCone (M : ℕ) (σ : completion.fan.cones) : PointedCone ℝ V :=
  liftedCone completion.fan (i a)
    (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) σ

theorem completedStarCone_regular (M : ℕ) (σ : completion.fan.cones) :
    IsRegularCone i (completedStarCone fan regular ray completion M σ) :=
  liftedCone_isRegular fan.lattice completion.fan completion.regular a
    (selectedRay_isPrimitive fan ray) qZ (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _)
    (completedStarRayLift fan regular ray completion M)
    (completedStarRayLift_projects fan regular ray completion M) σ

theorem completedStarCone_intersections (M : ℕ) (σ τ : completion.fan.cones) :
    (completedStarCone fan regular ray completion M σ ⊓
      completedStarCone fan regular ray completion M τ).IsFaceOf
        (completedStarCone fan regular ray completion M σ) := by
  apply liftedCone_inf_isFaceOf completion.fan (i a)
    (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) q
    (selectedRay_projection_zero fan ray)
  intro ρ
  exact completedStarRayLift_real_projects fan regular ray completion M ρ

theorem completedStarCone_old (M : ℕ) (σ : OriginalRayStarCone fan ray) :
    completedStarCone fan regular ray completion M
      (subfanConeEmbedding star completion.fan completion.contains
        (originalStarProjection fan ray σ)) = σ.val.val := by
  unfold completedStarCone
  rw [liftedCone_subfan_old star completion.fan completion.contains (i a)
    (fun ρ => i (canonicalOldStarRayLift fan regular ray ρ))
    (fun ρ => i (completedStarRayLift fan regular ray completion M ρ))
    (fun ρ => congrArg i (completedStarRayLift_old fan regular ray completion M ρ))]
  exact canonicalOldStarLiftedCone_eq fan regular ray σ

def completionStarOldFace (σ : completion.fan.cones) : (star).cones :=
  subfanOldRayFace star completion.fan completion.regular
    ((isFullOnRays_iff_local star completion.fan).mpr completion.oldRayClosed) σ

def completionOriginalStarFace (σ : completion.fan.cones) : OriginalRayStarCone fan ray :=
  (originalStarOrderIso fan ray).symm (completionStarOldFace fan ray completion σ)

theorem completionOriginalStarFace_projection (σ : completion.fan.cones) :
    originalStarProjection fan ray (completionOriginalStarFace fan ray completion σ) =
      completionStarOldFace fan ray completion σ :=
  (originalStarOrderIso fan ray).apply_symm_apply _

theorem completedStarCone_split (M : ℕ) (σ : completion.fan.cones) :
    completedStarCone fan regular ray completion M σ =
      (completionOriginalStarFace fan ray completion σ).val.val ⊔
        PointedCone.hull ℝ (newConeRayLifts star completion.fan
          (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) σ) := by
  unfold completedStarCone
  rw [liftedCone_subfan_split star completion.fan completion.contains (i a)
    (fun ρ => i (canonicalOldStarRayLift fan regular ray ρ))
    (fun ρ => i (completedStarRayLift fan regular ray completion M ρ))
    (fun ρ => congrArg i (completedStarRayLift_old fan regular ray completion M ρ))
    completion.regular ((isFullOnRays_iff_local star completion.fan).mpr completion.oldRayClosed)]
  have old := canonicalOldStarLiftedCone_eq fan regular ray
    (completionOriginalStarFace fan ray completion σ)
  rw [completionOriginalStarFace_projection] at old
  exact congrArg (fun C => C ⊔ PointedCone.hull ℝ
    (newConeRayLifts star completion.fan
      (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) σ)) old

def completedStarPackingThreshold : ℕ :=
  (exists_completedStar_packing_bound fan regular ray completion).choose

theorem completedStarPacking_positive (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M)
    (p : StarSeparatorIndex fan ray) (ρ : completion.fan.Ray)
    (newRay : ρ.toCone.val ∉ (star).cones) :
    0 < starSeparator fan ray p (completedStarRayLift fan regular ray completion M ρ) :=
  (exists_completedStar_packing_bound fan regular ray completion).choose_spec M large p ρ newRay

theorem completedStarCone_old_intersections (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M)
    (σ : completion.fan.cones) (τ : fan.cones) :
    (completedStarCone fan regular ray completion M σ ⊓ τ.val).IsFaceOf
        (completedStarCone fan regular ray completion M σ) ∧
      (completedStarCone fan regular ray completion M σ ⊓ τ.val).IsFaceOf τ.val := by
  by_cases contains : ray.toCone ≤ τ
  · let old : OriginalRayStarCone fan ray := ⟨τ,contains⟩
    let projected := subfanConeEmbedding star completion.fan completion.contains
      (originalStarProjection fan ray old)
    have same : completedStarCone fan regular ray completion M projected = τ.val :=
      completedStarCone_old fan regular ray completion M old
    rw [← same]
    refine ⟨completedStarCone_intersections fan regular ray completion M σ projected,?_⟩
    simpa only [inf_comm] using
      completedStarCone_intersections fan regular ray completion M projected σ
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
    constructor
    · exact FanPacking.adjoining_positive_inf_isFaceOf old.val.val τ.val form
        nonnegative nonpositive spec.2.2.2 newRays positive
    · rw [FanPacking.adjoining_positive_generators_inf old.val.val τ.val form
        nonnegative nonpositive newRays positive]
      exact fan.inf_isFaceOf_right old.val.property τ.property

/-- The actual regular one-ray packing extension. Its kernel checks
include all old/new and new/new fan intersections. -/
def completedStarPackedFan (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M) : Fan i :=
  attachFiniteCones fan (completedStarCone fan regular ray completion M)
    (fun σ => (completedStarCone_regular fan regular ray completion M σ).toIsToricCone)
    (completedStarCone_intersections fan regular ray completion M)
    (completedStarCone_old_intersections fan regular ray completion M large)

theorem completedStarPackedFan_contains (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M) :
    fan.cones ⊆ (completedStarPackedFan fan regular ray completion M large).cones :=
  attachFiniteCones_contains_original _ _ _ _ _

theorem completedStarPackedFan_contains_lift (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M)
    (σ : completion.fan.cones) :
    completedStarCone fan regular ray completion M σ ∈
      (completedStarPackedFan fan regular ray completion M large).cones :=
  attachFiniteCones_contains_new _ _ _ _ _ σ

theorem completedStarPackedFan_regular (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M) :
    (completedStarPackedFan fan regular ray completion M large).IsRegular :=
  attachFiniteCones_regular _ _ _ _ _ regular
    (completedStarCone_regular fan regular ray completion M)

end ToricPower.FanSubdivision
end

