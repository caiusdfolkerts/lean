module

public import ToricPower.SubfanBoundaryCharacters
public import ToricPower.SubfanLinearTests
public import ToricPower.RestrictedFanIncidence

/-!
# Boundary rays and twists on the actual saturated-subspace fans

Restriction uses the original saturated lattice trace. The full-on-rays
condition descends to that fan, and boundary twisting commutes with the
literal restriction of divisor coefficients. No finite-index lattice
replacement is involved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric Set

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (W : Submodule ℝ V) (rational : IsRationalSubspace i W)

omit extension included in
/-- Membership in the actual restricted fan is exactly ambient-cone membership. -/
theorem restrictedFan_cone_mem_iff_ambient (σ : PointedCone ℝ W) :
    σ ∈ (restrictedFan fan W rational).cones ↔ σ.map W.subtype ∈ fan.cones := by
  constructor
  · intro member
    exact restrictedFan_cone_map_mem fan W rational ⟨σ,member⟩
  · intro member
    apply (mem_restrictedFan_cones fan W rational σ).mpr
    refine ⟨σ.map W.subtype,member,?_,cone_comap_map_subtype W σ⟩
    rintro _ ⟨x,hx,rfl⟩
    exact x.property

/-- An old ray of the restricted extension is exactly a retained ambient old ray. -/
theorem restrictedSubfanRay_old_iff (ρ : (restrictedFan extension W rational).Ray) :
    ρ.toCone.val ∈ (restrictedFan fan W rational).cones ↔
      (restrictedFanRayEquiv extension W rational ρ).val.toCone.val ∈ fan.cones :=
  restrictedFan_cone_mem_iff_ambient fan W rational ρ.toCone.val

/-- The divisorial-boundary condition survives every rational restriction. -/
theorem isFullOnRays_restricted (full : IsFullOnRays fan extension) :
    IsFullOnRays (restrictedFan fan W rational) (restrictedFan extension W rational) := by
  intro σ member old
  apply (restrictedFan_cone_mem_iff_ambient fan W rational σ).mpr
  apply full (σ.map W.subtype) (restrictedFan_cone_map_mem extension W rational ⟨σ,member⟩)
  intro ρ below
  have inW : ρ.toCone.val ≤ (W : PointedCone ℝ V) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := below hx
    exact y.property
  let retained := fanRayRestrict extension W rational ρ inW
  have retainedBelow : retained.toCone.val ≤ σ := by
    intro x hx
    obtain ⟨y,hy,equal⟩ := below hx
    have same : y = x := Subtype.ext equal
    exact same ▸ hy
  have ambientOld := (restrictedFan_cone_mem_iff_ambient fan W rational retained.toCone.val).mp
    (old retained retainedBelow)
  change (ρ.toCone.val.comap W.subtype).map W.subtype ∈ fan.cones at ambientOld
  rwa [cone_map_comap_subtype W ρ.toCone.val inW] at ambientOld

/-- The two genuine ray-inclusion paths have the same ambient cone. -/
theorem restrictedSubfanRay_embedding_square (ρ : (restrictedFan fan W rational).Ray) :
    (restrictedFanRayEquiv extension W rational
      (subfanRayEmbedding (restrictedFan fan W rational) (restrictedFan extension W rational)
        (restrictedFan_cones_subset fan extension included W rational) ρ)).val =
      subfanRayEmbedding fan extension included (restrictedFanRayEquiv fan W rational ρ).val := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The actual boundary coefficient on a restricted ray is the original
boundary coefficient of that ray. -/
theorem restrictedSubfanBoundaryCoefficients (ρ : (restrictedFan extension W rational).Ray) :
    restrictedFanRayCoefficients extension W rational
        (subfanBoundaryCoefficients fan extension) ρ =
      subfanBoundaryCoefficients (restrictedFan fan W rational)
        (restrictedFan extension W rational) ρ := by
  unfold restrictedFanRayCoefficients subfanBoundaryCoefficients
  rw [← restrictedSubfanRay_old_iff fan extension W rational ρ]

/-- Literal restriction commutes with every nonnegative integer boundary twist. -/
theorem restrictedSubfanBoundaryTwist (b : fan.Ray → ℤ) (a : ℕ) :
    restrictedFanRayCoefficients extension W rational (subfanBoundaryTwist fan extension b a) =
      subfanBoundaryTwist (restrictedFan fan W rational) (restrictedFan extension W rational)
        (restrictedFanRayCoefficients fan W rational b) a := by
  funext ρ
  by_cases old : ρ.toCone.val ∈ (restrictedFan fan W rational).cones
  · have ambientOld := (restrictedSubfanRay_old_iff fan extension W rational ρ).mp old
    dsimp only [restrictedFanRayCoefficients,subfanBoundaryTwist]
    rw [dif_pos old,dif_pos ambientOld]
    rfl
  · have ambientNew : (restrictedFanRayEquiv extension W rational ρ).val.toCone.val ∉ fan.cones :=
      fun h => old ((restrictedSubfanRay_old_iff fan extension W rational ρ).mpr h)
    dsimp only [restrictedFanRayCoefficients,subfanBoundaryTwist]
    rw [dif_neg old,dif_neg ambientNew]

end ToricPower

end
