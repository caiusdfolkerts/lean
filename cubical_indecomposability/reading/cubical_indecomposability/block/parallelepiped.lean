import cubical_indecomposability.block.interfaces

/-!
# The disjoint facet is already a parallelepiped

Its eight vertices are the unit three-cube in the hyperplane x₃ = 0.
We give the affine embedding of the standard cube and prove equality of
the entire convex bodies, not only agreement on a list of points.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- The linear part of the standard-cube parametrization of G. -/
def GcubeLinear : E 3 →ₗ[ℝ] E 4 where
  toFun x := (EuclideanSpace.equiv (Fin 4) ℝ).symm
    ![x 0 / 2, x 1 / 2, x 2 / 2, 0]
  map_add' x y := by
    ext i
    fin_cases i
    · change (x 0 + y 0) / 2 = x 0 / 2 + y 0 / 2
      ring
    · change (x 1 + y 1) / 2 = x 1 / 2 + y 1 / 2
      ring
    · change (x 2 + y 2) / 2 = x 2 / 2 + y 2 / 2
      ring
    · change (0 : ℝ) = 0 + 0
      ring
  map_smul' r x := by
    ext i
    fin_cases i
    · change (r * x 0) / 2 = r * (x 0 / 2)
      ring
    · change (r * x 1) / 2 = r * (x 1 / 2)
      ring
    · change (r * x 2) / 2 = r * (x 2 / 2)
      ring
    · change (0 : ℝ) = r * 0
      ring

def GcubeOffset : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![1 / 2, 1 / 2, 1 / 2, 0]

/-- An injective affine map from [-1,1]³ onto the distinguished facet. -/
def Gcube : E 3 →ᵃ[ℝ] E 4 :=
  GcubeLinear.toAffineMap + AffineMap.const ℝ (E 3) GcubeOffset

@[simp] theorem Gcube_apply (x : E 3) (i : Fin 3) :
    Gcube x i.castSucc = (x i + 1) / 2 := by
  fin_cases i
  · change x 0 / 2 + 1 / 2 = (x 0 + 1) / 2
    ring
  · change x 1 / 2 + 1 / 2 = (x 1 + 1) / 2
    ring
  · change x 2 / 2 + 1 / 2 = (x 2 + 1) / 2
    ring

theorem Gcube_injective : Function.Injective Gcube := by
  intro x y h
  ext i
  have hi := congrArg (fun z : E 4 => z i.castSucc) h
  rw [Gcube_apply, Gcube_apply] at hi
  linarith

/-- Exact correspondence of the eight geometric vertices. -/
theorem Gcube_vertex (b : Fin 8) :
    Gcube (vertIper (bitsOfFin8 b)) = p (cubeVertex 1 b) := by
  fin_cases b
  · ext i
    fin_cases i
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (-1 : ℝ) / 2 + 1 / 2 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (1 : ℝ) / 2 + 1 / 2 = ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num
    · change (0 : ℝ) + 0 = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
      norm_num

/-- The affine map carries exactly the standard cube vertices to the G vertices. -/
theorem Gcube_image_vertices :
    Gcube '' ((standardCube 3).vertices : Set (E 3)) =
      p '' (facetLabels 1 : Set (Fin 32)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := mem_verticiIper.mp hy
    obtain ⟨b, rfl⟩ := bitsOfFin8_bijective.2 s
    rw [Gcube_vertex]
    refine ⟨cubeVertex 1 b, ?_, rfl⟩
    change cubeVertex 1 b ∈ facetLabels 1
    rw [← cubeVertex_image 1]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Finset.univ.image (cubeVertex 1) := by
      rwa [cubeVertex_image 1]
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv'
    exact ⟨vertIper (bitsOfFin8 b), mem_verticiIper.mpr ⟨_, rfl⟩, Gcube_vertex b⟩

/-- Equality of the actual convex bodies follows by affine transport of convex hulls. -/
theorem Gcube_image_body : Gcube '' (standardCube 3).toSet = G := by
  change Gcube '' convexHull ℝ ((standardCube 3).vertices : Set (E 3)) = G
  rw [AffineMap.image_convexHull, Gcube_image_vertices]
  exact (facet_eq_hull 1).symm

/-- Stronger than projective equivalence: G itself is an affine three-cube. -/
theorem G_affine_cube :
    ∃ φ : E 3 →ᵃ[ℝ] E 4, Function.Injective φ ∧
      φ '' (standardCube 3).toSet = G :=
  ⟨Gcube, Gcube_injective, Gcube_image_body⟩

end CubicalIndecomposability.Block
