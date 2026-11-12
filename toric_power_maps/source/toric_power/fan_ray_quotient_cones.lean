module

public import TauCeti.Geometry.Convex.Cone.Face.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Abel

/-!
# Intersections and faces in the quotient by a fan ray

Two cones containing the same positive ray have intersection compatible
with quotienting by its real span. Faces containing that ray descend to
faces, with exact membership detected before quotienting. These are the
geometric assertions needed to construct a quotient star as an actual
fan, rather than assuming its fan axioms.
-/

@[expose] public noncomputable section

namespace ToricPower.FanSubdivision

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (projection : V →ₗ[ℝ] W) (ray : V)
  (kernel : LinearMap.ker projection = Submodule.span ℝ {ray})

include kernel in
theorem eq_add_ray_of_projection_eq {x y : V}
    (same : projection x = projection y) :
    ∃ t : ℝ, x = y + t • ray := by
  have member : x-y ∈ LinearMap.ker projection := by
    change projection (x-y) = 0
    rw [map_sub, same, sub_self]
  rw [kernel] at member
  obtain ⟨t, evaluate⟩ := Submodule.mem_span_singleton.mp member
  refine ⟨t, ?_⟩
  calc
    x = (x-y)+y := (sub_add_cancel x y).symm
    _ = t • ray+y := by rw [evaluate]
    _ = y+t • ray := add_comm _ _

include kernel in
/-- Images commute with intersections on the collection of cones
containing the chosen positive ray. This fails for unrestricted cones. -/
theorem map_inf_of_ray_mem (σ τ : PointedCone ℝ V)
    (rayσ : ray ∈ σ) (rayτ : ray ∈ τ) :
    PointedCone.map projection (σ ⊓ τ) =
      PointedCone.map projection σ ⊓ PointedCone.map projection τ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp hz
    exact ⟨PointedCone.mem_map.mpr ⟨x,hx.1,rfl⟩,
      PointedCone.mem_map.mpr ⟨x,hx.2,rfl⟩⟩
  · intro z hz
    obtain ⟨x,hx,xValue⟩ := PointedCone.mem_map.mp hz.1
    obtain ⟨y,hy,yValue⟩ := PointedCone.mem_map.mp hz.2
    obtain ⟨t,xEquals⟩ := eq_add_ray_of_projection_eq projection ray kernel
      (xValue.trans yValue.symm)
    by_cases nonnegative : 0 ≤ t
    · have xτ : x ∈ τ := by
        rw [xEquals]
        exact τ.add_mem hy (τ.smul_mem nonnegative rayτ)
      exact PointedCone.mem_map.mpr ⟨x,⟨hx,xτ⟩,xValue⟩
    · have yEquals : y = x + (-t) • ray := by
        rw [xEquals, neg_smul]
        abel
      have yσ : y ∈ σ := by
        rw [yEquals]
        exact σ.add_mem hx (σ.smul_mem (neg_nonneg.mpr (le_of_not_ge nonnegative)) rayσ)
      exact PointedCone.mem_map.mpr ⟨y,⟨yσ,hy⟩,yValue⟩

include kernel in
/-- A face containing the ray is saturated for the quotient, within
its parent cone. The conclusion concerns the original literal point. -/
theorem mem_face_iff_projection_mem (σ F : PointedCone ℝ V)
    (face : F.IsFaceOf σ) (rayF : ray ∈ F) {x : V} (member : x ∈ σ) :
    x ∈ F ↔ projection x ∈ PointedCone.map projection F := by
  constructor
  · intro hx
    exact PointedCone.mem_map.mpr ⟨x,hx,rfl⟩
  · intro hx
    obtain ⟨y,hy,same⟩ := PointedCone.mem_map.mp hx
    obtain ⟨t,xEquals⟩ := eq_add_ray_of_projection_eq projection ray kernel same.symm
    by_cases nonnegative : 0 ≤ t
    · rw [xEquals]
      exact F.add_mem hy (F.smul_mem nonnegative rayF)
    · have yEquals : y = x + (-t) • ray := by
        rw [xEquals, neg_smul]
        abel
      exact face.mem_of_add_mem_left member
        (σ.smul_mem (neg_nonneg.mpr (le_of_not_ge nonnegative)) (face.le rayF))
        (yEquals ▸ hy)

include kernel in
/-- The image of a face containing the quotient ray is an actual face
of the image cone. Injectivity of the projection is not assumed. -/
theorem face_map_of_ray_mem (σ F : PointedCone ℝ V)
    (face : F.IsFaceOf σ) (rayF : ray ∈ F) :
    (PointedCone.map projection F).IsFaceOf (PointedCone.map projection σ) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp hz
    exact PointedCone.mem_map.mpr ⟨x,face.le hx,rfl⟩
  · intro x y a hx hy positive combined
    obtain ⟨x',hx',rfl⟩ := PointedCone.mem_map.mp hx
    obtain ⟨y',hy',rfl⟩ := PointedCone.mem_map.mp hy
    have original : a • x' + y' ∈ F :=
      (mem_face_iff_projection_mem projection ray kernel σ F face rayF
        (σ.add_mem (σ.smul_mem positive.le hx') hy')).mpr (by
          simpa only [map_add, map_smul] using combined)
    exact PointedCone.mem_map.mpr
      ⟨x',face.mem_of_smul_add_mem hx' hy' positive original,rfl⟩

/-- The quotient image is pointed whenever its kernel cuts out a face.
This criterion is used with the chosen ray as that face. -/
theorem map_salient_of_kernel_face (σ : PointedCone ℝ V)
    (face : (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker projection)).IsFaceOf σ) :
    (PointedCone.map projection σ : ConvexCone ℝ W).Salient := by
  intro z hz nonzero negative
  obtain ⟨x,hx,xValue⟩ := PointedCone.mem_map.mp hz
  obtain ⟨y,hy,yValue⟩ := PointedCone.mem_map.mp negative
  have sumMember : x+y ∈ σ ⊓ PointedCone.ofSubmodule (LinearMap.ker projection) := by
    refine ⟨σ.add_mem hx hy, ?_⟩
    change projection (x+y) = 0
    rw [map_add,xValue,yValue,add_neg_cancel]
  have xKernel := (face.mem_of_add_mem_left hx hy sumMember).2
  have zero : projection x = 0 := xKernel
  exact nonzero (xValue.symm.trans zero)

/-- A pointed cone meets the line through one of its nonzero positive
vectors in exactly the positive ray. -/
theorem cone_inf_span_ray_eq (σ : PointedCone ℝ V)
    (salient : (σ : ConvexCone ℝ V).Salient)
    (rayMember : ray ∈ σ) (nonzero : ray ≠ 0) :
    σ ⊓ PointedCone.ofSubmodule (Submodule.span ℝ {ray}) =
      PointedCone.hull ℝ {ray} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t,value⟩ := Submodule.mem_span_singleton.mp hx.2
    by_cases positive : 0 ≤ t
    · rw [← value]
      exact (PointedCone.hull ℝ {ray}).smul_mem positive
        (PointedCone.subset_hull (Set.mem_singleton ray))
    · have member : t • ray ∈ σ := by rw [value]; exact hx.1
      have negativeMember : -(t • ray) ∈ σ := by
        rw [← neg_smul]
        exact σ.smul_mem (neg_nonneg.mpr (le_of_not_ge positive)) rayMember
      exact False.elim (salient (t • ray) member
        (smul_ne_zero (lt_of_not_ge positive).ne nonzero) negativeMember)
  · refine le_inf ?_ (PointedCone.hull_le_span ℝ {ray})
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr rayMember)

include kernel in
/-- For a ray face, the kernel of the quotient projection cuts out
precisely that face, so its image cone is pointed. -/
theorem kernel_face_of_ray_face (σ : PointedCone ℝ V)
    (salient : (σ : ConvexCone ℝ V).Salient)
    (rayMember : ray ∈ σ) (nonzero : ray ≠ 0)
    (face : (PointedCone.hull ℝ {ray}).IsFaceOf σ) :
    (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker projection)).IsFaceOf σ := by
  rw [kernel, cone_inf_span_ray_eq ray σ salient rayMember nonzero]
  exact face

end ToricPower.FanSubdivision
end
