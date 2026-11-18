module

public import ToricPower.CanonicalFanRayStar

/-!
# The quotient-star order isomorphism

The faces added by the quotient fan constructor are exactly the images
of original cones containing the chosen ray. Projection gives an order
isomorphism between those original cones and the actual quotient fan.
This prevents any ambiguity when a completed quotient fan is lifted
back while retaining every old star cone.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Pulling a face back inside its original cone gives a face there,
even when the ambient linear map has a kernel. -/
theorem face_preimage_inter (projection : V →ₗ[ℝ] W)
    (σ : PointedCone ℝ V) (δ : PointedCone ℝ W)
    (face : δ.IsFaceOf (PointedCone.map projection σ)) :
    (σ ⊓ PointedCone.comap projection δ).IsFaceOf σ := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  refine ⟨hx,?_⟩
  apply face.mem_of_smul_add_mem
    (PointedCone.mem_map.mpr ⟨x,hx,rfl⟩)
    (PointedCone.mem_map.mpr ⟨y,hy,rfl⟩) positive
  have projected : projection (r • x + y) ∈ δ := combined.2
  simpa only [map_smul,map_add] using projected

theorem map_face_preimage_inter (projection : V →ₗ[ℝ] W)
    (σ : PointedCone ℝ V) (δ : PointedCone ℝ W)
    (face : δ.IsFaceOf (PointedCone.map projection σ)) :
    PointedCone.map projection (σ ⊓ PointedCone.comap projection δ) = δ := by
  apply le_antisymm
  · rintro z member
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp member
    exact hx.2
  · intro z member
    obtain ⟨x,hx,evaluate⟩ := PointedCone.mem_map.mp (face.le member)
    exact PointedCone.mem_map.mpr
      ⟨x,⟨hx,(show projection x ∈ δ from evaluate.symm ▸ member)⟩,evaluate⟩

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  (fan : Fan i) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "q" => Submodule.mkQ (Submodule.span ℝ {i a})

abbrev OriginalRayStarCone := {σ : fan.cones // ray.toCone ≤ σ}

/-- Every cone of the quotient star is the exact image of a retained
original cone containing the chosen ray. -/
theorem exists_original_star_cone (δ : (canonicalRayStar fan ray).cones) :
    ∃ σ : OriginalRayStarCone fan ray, PointedCone.map q σ.val.val = δ.val := by
  obtain ⟨σ,member,contains,face⟩ := (mem_canonicalRayStar_iff fan ray δ.val).mp δ.property
  let F := σ ⊓ PointedCone.comap q δ.val
  have faceF : F.IsFaceOf σ := face_preimage_inter q σ δ.val face
  have memberF : F ∈ fan.cones := fan.mem_of_isFaceOf member faceF
  have containsF : ray.toCone.val ≤ F := by
    intro x hx
    refine ⟨contains hx,?_⟩
    have xKernel : x ∈ (Submodule.span ℝ {i a}) := by
      rw [fanRay_eq_hull_realVector] at hx
      obtain ⟨r,_,rfl⟩ := PointedCone.mem_hull_singleton.mp hx
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self (R := ℝ) (i a))
    have zero : q x = 0 := LinearMap.mem_ker.mp (by rwa [Submodule.ker_mkQ])
    change q x ∈ δ.val
    rw [zero]
    exact δ.val.zero_mem
  refine ⟨⟨⟨F,memberF⟩,containsF⟩,?_⟩
  exact map_face_preimage_inter q σ δ.val face

/-- Projection is order-reflecting on the original star. The exact
kernel and the original fan's common-face axiom are both used. -/
theorem original_star_projection_le_iff (σ τ : OriginalRayStarCone fan ray) :
    PointedCone.map q σ.val.val ≤ PointedCone.map q τ.val.val ↔ σ ≤ τ := by
  constructor
  · intro below x hx
    have rayσ : fanRayRealVector fan ray ∈ σ.val.val :=
      σ.property (fanRayRealVector_mem fan ray)
    have rayτ : fanRayRealVector fan ray ∈ τ.val.val :=
      τ.property (fanRayRealVector_mem fan ray)
    have common : q x ∈ PointedCone.map q (σ.val.val ⊓ τ.val.val) := by
      rw [map_inf_of_ray_mem q (fanRayRealVector fan ray)
        (rayQuotient_real_kernel i a) σ.val.val τ.val.val rayσ rayτ]
      have projected : q x ∈ PointedCone.map q σ.val.val :=
        PointedCone.mem_map.mpr ⟨x,hx,rfl⟩
      exact ⟨projected,below projected⟩
    exact ((mem_face_iff_projection_mem q (fanRayRealVector fan ray)
      (rayQuotient_real_kernel i a) σ.val.val (σ.val.val ⊓ τ.val.val)
      (fan.inf_isFaceOf_left σ.val.property τ.val.property) ⟨rayσ,rayτ⟩ hx).mpr common).2
  · intro below z member
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp member
    exact PointedCone.mem_map.mpr ⟨x,below hx,rfl⟩

def originalStarProjection (σ : OriginalRayStarCone fan ray) :
    (canonicalRayStar fan ray).cones :=
  ⟨PointedCone.map q σ.val.val,(mem_canonicalRayStar_iff fan ray _).mpr
    ⟨σ.val.val,σ.val.property,σ.property,PointedCone.IsFaceOf.refl _⟩⟩

/-- The canonical quotient star is precisely the old star with its
kernel ray removed, including all order and face incidences. -/
def originalStarOrderIso : OriginalRayStarCone fan ray ≃o (canonicalRayStar fan ray).cones where
  toEquiv := Equiv.ofBijective (originalStarProjection fan ray) (by
    constructor
    · intro σ τ same
      have eq := congrArg (fun δ : (canonicalRayStar fan ray).cones => δ.val) same
      apply le_antisymm
      · exact (original_star_projection_le_iff fan ray σ τ).mp (le_of_eq eq)
      · exact (original_star_projection_le_iff fan ray τ σ).mp (le_of_eq eq.symm)
    · intro δ
      obtain ⟨σ,eq⟩ := exists_original_star_cone fan ray δ
      exact ⟨σ,Subtype.ext eq⟩)
  map_rel_iff' := original_star_projection_le_iff fan ray _ _

end ToricPower.FanSubdivision
end
