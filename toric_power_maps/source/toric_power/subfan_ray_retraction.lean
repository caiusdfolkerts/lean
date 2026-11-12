module

public import ToricPower.FanRayComplex
public import ToricPower.FanRayPrimitive

/-!
# The actual old-ray face of a regular fan extension

If a subfan contains every cone whose rays it contains, each cone of a
regular extension has a unique face consisting of its old rays. These
faces lie in the original fan and form a surjective, meet-preserving
retraction on its cones. The ray and primitive-vector identifications
are literal in the unchanged lattice.
-/

@[expose] public noncomputable section

open TauCeti.Toric Set

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

def subfanConeEmbedding : fan.cones ↪ extension.cones where
  toFun σ := ⟨σ.val,included σ.property⟩
  inj' _ _ h := Subtype.ext (congrArg (fun σ : extension.cones => σ.val) h)

def subfanRayEmbedding : fan.Ray ↪ extension.Ray where
  toFun ρ := ⟨subfanConeEmbedding fan extension included ρ.toCone,ρ.property⟩
  inj' _ _ h := Subtype.ext (Subtype.ext (congrArg (fun ρ => ρ.toCone.val) h))

/-- The original primitive vector is unchanged by an actual subfan inclusion. -/
theorem subfanRayEmbedding_primitive (ρ : fan.Ray) :
    fanRayPrimitiveGenerator extension (subfanRayEmbedding fan extension included ρ) =
      fanRayPrimitiveGenerator fan ρ := rfl

/-- Rays of the original fan are exactly the old rays of the extension. -/
def subfanOldRayEquiv : fan.Ray ≃ {ρ : extension.Ray // ρ.toCone.val ∈ fan.cones} where
  toFun ρ := ⟨subfanRayEmbedding fan extension included ρ,ρ.toCone.property⟩
  invFun ρ := ⟨⟨ρ.val.toCone.val,ρ.property⟩,ρ.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include included in
theorem subfan_isRegular (regular : extension.IsRegular) : fan.IsRegular := by
  rw [Fan.isRegular_iff] at regular ⊢
  intro σ hσ
  exact regular σ (included hσ)

omit extension included in
/-- A cone is determined by its actual ray cones, including the zero cone. -/
theorem fanCone_le_of_rays (σ τ : fan.cones)
    (contained : ∀ ρ : fan.Ray, ρ.toCone ≤ σ → ρ.toCone ≤ τ) : σ ≤ τ := by
  change σ.val ≤ τ.val
  rw [← (fan.isToricCone σ.property).hull_primitiveGenerator fan.lattice]
  apply Submodule.span_le.mpr
  rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
  exact contained (Fan.Ray.ofToricRay fan σ ρ) (Fan.Ray.toCone_ofToricRay_le fan σ ρ)
    (primitiveGenerator_mem fan.lattice (fan.isToricCone σ.property) ρ)

/-- This is the precise divisorial-boundary combinatorial condition. -/
def IsFullOnRays : Prop :=
  ∀ σ ∈ extension.cones,
    (∀ ρ : extension.Ray, ρ.toCone.val ≤ σ → ρ.toCone.val ∈ fan.cones) → σ ∈ fan.cones

/-- The local-ray and global-ray formulations are equivalent. -/
theorem isFullOnRays_iff_local : IsFullOnRays fan extension ↔
    ∀ σ ∈ extension.cones,
      (∀ ρ : ToricRay σ, ρ.toPointedCone ∈ fan.cones) → σ ∈ fan.cones := by
  constructor
  · intro full σ member all
    exact full σ member (fun ρ below => all (ρ.toToricRay extension ⟨σ,member⟩ below))
  · intro full σ member all
    exact full σ member (fun ρ => all (Fan.Ray.ofToricRay extension ⟨σ,member⟩ ρ)
      (Fan.Ray.toCone_ofToricRay_le extension ⟨σ,member⟩ ρ))

variable (regular : extension.IsRegular) (rayFull : IsFullOnRays fan extension)

include regular rayFull in
theorem exists_subfanOldRayFace (σ : extension.cones) :
    ∃ τ : fan.cones, τ.val ≤ σ.val ∧ ∀ ρ : extension.Ray,
      ρ.toCone.val ≤ τ.val ↔ ρ.toCone.val ∈ fan.cones ∧ ρ.toCone ≤ σ := by
  obtain ⟨τ,below,exactRays⟩ := exists_cone_raySet_eq_of_subset extension regular σ
    {ρ | ρ.toCone.val ∈ fan.cones ∧ ρ.toCone ≤ σ} (fun _ h => h.2)
  have old : τ.val ∈ fan.cones :=
    rayFull τ.val τ.property (fun ρ h => ((exactRays ρ).mp h).1)
  exact ⟨⟨τ.val,old⟩,below,exactRays⟩

/-- The actual face consisting of every old ray of the given cone. -/
def subfanOldRayFace (σ : extension.cones) : fan.cones :=
  Classical.choose (exists_subfanOldRayFace fan extension regular rayFull σ)

theorem subfanOldRayFace_le (σ : extension.cones) :
    (subfanOldRayFace fan extension regular rayFull σ).val ≤ σ.val :=
  (Classical.choose_spec (exists_subfanOldRayFace fan extension regular rayFull σ)).1

theorem subfanOldRayFace_rays (σ : extension.cones) (ρ : extension.Ray) :
    ρ.toCone.val ≤ (subfanOldRayFace fan extension regular rayFull σ).val ↔
      ρ.toCone.val ∈ fan.cones ∧ ρ.toCone ≤ σ :=
  (Classical.choose_spec (exists_subfanOldRayFace fan extension regular rayFull σ)).2 ρ

theorem subfanOldRayFace_oldRay (σ : extension.cones) (ρ : fan.Ray) :
    ρ.toCone ≤ subfanOldRayFace fan extension regular rayFull σ ↔
      (subfanRayEmbedding fan extension included ρ).toCone ≤ σ := by
  exact (subfanOldRayFace_rays fan extension regular rayFull σ
    (subfanRayEmbedding fan extension included ρ)).trans
      (and_iff_right ρ.toCone.property)

/-- Every original cone is retained exactly, so this is a genuine retraction. -/
theorem subfanOldRayFace_retract (σ : fan.cones) :
    subfanOldRayFace fan extension regular rayFull (subfanConeEmbedding fan extension included σ) = σ := by
  apply Subtype.ext
  apply le_antisymm
  · exact subfanOldRayFace_le fan extension regular rayFull _
  · apply fanCone_le_of_rays extension (subfanConeEmbedding fan extension included σ)
      (subfanConeEmbedding fan extension included
        (subfanOldRayFace fan extension regular rayFull (subfanConeEmbedding fan extension included σ)))
    intro ρ hρ
    apply (subfanOldRayFace_rays fan extension regular rayFull _ ρ).mpr
    refine ⟨?_,hρ⟩
    exact fan.mem_of_isFaceOf σ.property
      (extension.isFaceOf_of_le (included σ.property) ρ.toCone.property hρ)

include included in
theorem subfanOldRayFace_surjective :
    Function.Surjective (subfanOldRayFace fan extension regular rayFull) :=
  fun σ => ⟨subfanConeEmbedding fan extension included σ,
    subfanOldRayFace_retract fan extension included regular rayFull σ⟩

include included in
/-- The exact old-ray incidence determines all original face inclusions. -/
theorem subfanOldRayFace_monotone : Monotone (subfanOldRayFace fan extension regular rayFull) := by
  intro σ τ h
  apply fanCone_le_of_rays fan
  intro ρ hρ
  apply (subfanOldRayFace_oldRay fan extension included regular rayFull τ ρ).mpr
  exact ((subfanOldRayFace_oldRay fan extension included regular rayFull σ ρ).mp hρ).trans h

include included in
/-- Actual intersections are preserved, as required by the Čech chart cover. -/
theorem subfanOldRayFace_inf (σ τ : extension.cones) :
    subfanOldRayFace fan extension regular rayFull (σ ⊓ τ) =
      subfanOldRayFace fan extension regular rayFull σ ⊓
        subfanOldRayFace fan extension regular rayFull τ := by
  apply le_antisymm
  · exact le_inf (subfanOldRayFace_monotone fan extension included regular rayFull inf_le_left)
      (subfanOldRayFace_monotone fan extension included regular rayFull inf_le_right)
  · apply fanCone_le_of_rays fan
    intro ρ hρ
    rw [subfanOldRayFace_oldRay fan extension included regular rayFull,le_inf_iff]
    exact ⟨(subfanOldRayFace_oldRay fan extension included regular rayFull σ ρ).mp (hρ.trans inf_le_left),
      (subfanOldRayFace_oldRay fan extension included regular rayFull τ ρ).mp (hρ.trans inf_le_right)⟩

end ToricPower

end
