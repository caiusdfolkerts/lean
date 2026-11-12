module

public import ToricPower.CanonicalRayStarRays
public import ToricPower.FanLiftedConeProfiles

/-!
# Exact integral lifts of the original quotient star

The quotient-ray bijection selects the original primitive vector, so
lifting an original quotient cone recovers its original cone literally.
The proofs use the order isomorphism of actual cones and their genuine
primitive-ray generators.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "star" => canonicalRayStar fan ray

theorem oldStarRayProjection_le_iff (other : OriginalStarLinkRay fan ray)
    (σ : OriginalRayStarCone fan ray) :
    (oldStarRayProjection fan regular ray other).toCone ≤ originalStarProjection fan ray σ ↔
      other.val.toCone ≤ σ.val := by
  exact (original_star_projection_le_iff fan ray
    (oldStarPairCone fan regular ray other) σ).trans
      (oldStarPairCone_le_iff fan regular ray other σ)

/-- The original primitive ray, selected by the exact quotient-ray bijection. -/
def canonicalOldStarRayLift (ρ : (star).Ray) : N :=
  fanRayPrimitiveGenerator fan ((originalStarRayEquiv fan regular ray).symm ρ).val

theorem canonicalOldStarRayLift_projects (ρ : (star).Ray) :
    (Submodule.span ℤ {a}).mkQ (canonicalOldStarRayLift fan regular ray ρ) =
      fanRayPrimitiveGenerator star ρ := by
  have result := oldStarRayProjection_primitive fan regular ray
    ((originalStarRayEquiv fan regular ray).symm ρ)
  change (Submodule.span ℤ {a}).mkQ (canonicalOldStarRayLift fan regular ray ρ) =
    fanRayPrimitiveGenerator star
      ((originalStarRayEquiv fan regular ray)
        ((originalStarRayEquiv fan regular ray).symm ρ)) at result
  simpa only [Equiv.apply_symm_apply] using result

theorem canonicalOldStarRayLift_of_old (other : OriginalStarLinkRay fan ray) :
    canonicalOldStarRayLift fan regular ray (oldStarRayProjection fan regular ray other) =
      fanRayPrimitiveGenerator fan other.val := by
  change fanRayPrimitiveGenerator fan
      ((originalStarRayEquiv fan regular ray).symm
        ((originalStarRayEquiv fan regular ray) other)).val = _
  rw [Equiv.symm_apply_apply]

theorem canonicalOldStarRayLift_mem (σ : OriginalRayStarCone fan ray)
    (ρ : (star).Ray) (below : ρ.toCone ≤ originalStarProjection fan ray σ) :
    i (canonicalOldStarRayLift fan regular ray ρ) ∈ σ.val.val := by
  let other := (originalStarRayEquiv fan regular ray).symm ρ
  have projected : oldStarRayProjection fan regular ray other = ρ :=
    (originalStarRayEquiv fan regular ray).apply_symm_apply ρ
  have contained : other.val.toCone ≤ σ.val :=
    (oldStarRayProjection_le_iff fan regular ray other σ).mp (projected.symm ▸ below)
  exact contained (fanRayRealVector_mem fan other.val)

/-- Every cone containing the selected ray is recovered exactly, without
subdivision or changing any of its primitive generators. -/
theorem canonicalOldStarLiftedCone_eq (σ : OriginalRayStarCone fan ray) :
    liftedCone star (i a) (fun ρ => i (canonicalOldStarRayLift fan regular ray ρ))
      (originalStarProjection fan ray σ) = σ.val.val := by
  apply le_antisymm
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact σ.property (fanRayRealVector_mem fan ray)
    · apply Submodule.span_le.mpr
      rintro _ ⟨ρ,below,rfl⟩
      exact canonicalOldStarRayLift_mem fan regular ray σ ρ below
  · rw [← (fan.isToricCone σ.val.property).hull_primitiveGenerator fan.lattice]
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨ν,rfl⟩,rfl⟩
    let ρ := Fan.Ray.ofToricRay fan σ.val ν
    have below : ρ.toCone ≤ σ.val := Fan.Ray.toCone_ofToricRay_le fan σ.val ν
    rw [← fanRayPrimitiveGenerator_ofToricRay fan σ.val ν]
    change fanRayRealVector fan ρ ∈ liftedCone star (i a)
      (fun δ => i (canonicalOldStarRayLift fan regular ray δ))
        (originalStarProjection fan ray σ)
    by_cases same : ρ = ray
    · rw [same]
      exact generator_mem_liftedCone star (i a)
        (fun δ => i (canonicalOldStarRayLift fan regular ray δ)) _
    · let other : OriginalStarLinkRay fan ray := ⟨ρ,same,σ,below⟩
      have member := rayLift_mem_liftedCone star (i a)
        (fun δ => i (canonicalOldStarRayLift fan regular ray δ))
        (originalStarProjection fan ray σ) (oldStarRayProjection fan regular ray other)
        ((oldStarRayProjection_le_iff fan regular ray other σ).mpr below)
      rw [canonicalOldStarRayLift_of_old] at member
      exact member

end ToricPower.FanSubdivision
end
