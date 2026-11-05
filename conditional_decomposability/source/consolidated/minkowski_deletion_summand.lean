module
public import consolidated_dev.minkowski_map_core

set_option Elab.async false

section BundlePart0
/- Source: Papers/MinkowskiDeletionSummand.lean -/






@[expose] public section

/-!
# A summand persists after deleting the unique extra vertex

The linear map is constant on the first summand. Select those vertices
of the second summand whose translated images are vertices of the image
polytope. Their convex hull is the remaining summand. Actual exposed
vertex fibers show that every sum of selected vertices survives deletion;
actual vertex decomposition proves the reverse inclusion.
-/

noncomputable section
namespace Papers.MinkowskiDeletionSummand
open Set Module AffineSubspace
open Papers.Polytopes Papers.MinkowskiVertexMap Papers.LinearImageFibers
open Papers.FiniteHullPolytope Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise
variable {n : ℕ}

theorem summand_persists_after_unique_extra_deletion
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (π : E n →L[ℝ] E n) (hker : vectorSpan ℝ A.toSet ≤ π.ker)
    (x : E n) (hx : x∈P.vertices)
    (hxextra : π x∉(imagePolytope P π).vertices)
    (hother : ∀ y∈P.vertices,y≠x→π y∈(imagePolytope P π).vertices)
    (hne : (P.vertices.erase x).Nonempty) :
    ∃ B' : ConvexPolytope n, (deleteVertex P x hne).toSet=A.toSet+B'.toSet := by
  obtain ⟨a₀,ha₀⟩ := A.vertices_nonempty
  have ha₀body : a₀∈A.toSet := subset_convexHull ℝ _ ha₀
  have hπ (a : E n) (ha : a∈A.toSet) : π a=π a₀ := by
    have hm := hker (vsub_mem_vectorSpan ℝ ha ha₀body)
    change π (a-a₀)=0 at hm
    rw [map_sub] at hm
    exact sub_eq_zero.mp hm
  let T := B.vertices.filter (fun b => π (a₀+b)∈(imagePolytope P π).vertices)
  have hdecomp (y : E n) (hy : y∈P.vertices.erase x) :
      ∃ a∈A.vertices,∃ b∈T,a+b=y := by
    obtain ⟨hyx,hyP⟩ := Finset.mem_erase.mp hy
    obtain ⟨a,ha,b,hb,hab⟩ := vertex_decomposition P A B hsum hyP
    refine ⟨a,ha,b,Finset.mem_filter.mpr ⟨hb,?_⟩,hab⟩
    have he : π (a₀+b)=π y := by
      rw [←hab,map_add,map_add,hπ a (subset_convexHull ℝ _ ha)]
    rw [he]
    exact hother y hyP hyx
  have hT : T.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    obtain ⟨a,ha,b,hb,hab⟩ := hdecomp y hy
    exact ⟨b,hb⟩
  let B' := finiteHullPolytope T hT
  refine ⟨B',?_⟩
  rw [deleteVertex_toSet]
  have hB' : B'.toSet=convexHull ℝ (T : Set (E n)) := finiteHullPolytope_toSet T hT
  apply le_antisymm
  · apply convexHull_min
    · intro y hy
      obtain ⟨a,ha,b,hb,rfl⟩ := hdecomp y hy
      apply Set.mem_add.mpr
      refine ⟨a,subset_convexHull ℝ _ ha,b,?_,rfl⟩
      rw [hB']
      exact subset_convexHull ℝ _ hb
    · exact (convex_convexHull ℝ _).add (convex_convexHull ℝ _)
  · rw [hB']
    change convexHull ℝ (A.vertices : Set (E n)) + convexHull ℝ (T : Set (E n)) ⊆ _
    rw [←convexHull_add]
    apply convexHull_min ?_ (convex_convexHull ℝ _)
    intro y hy
    obtain ⟨a,ha,b,hb,rfl⟩ := Set.mem_add.mp hy
    obtain ⟨hbB,hbq⟩ := Finset.mem_filter.mp hb
    let q : (imagePolytope P π).vertices := ⟨π (a₀+b),hbq⟩
    have habP : a+b∈P.toSet := by
      rw [hsum]
      exact Set.mem_add.mpr ⟨a,subset_convexHull ℝ _ ha,b,subset_convexHull ℝ _ hbB,rfl⟩
    have habq : π (a+b)=q.val := by
      change π (a+b)=π (a₀+b)
      rw [map_add,map_add,hπ a (subset_convexHull ℝ _ ha)]
    have habF : a+b∈(vertexFiber P π q).toSet := by
      rw [vertexFiber,facePolytope_toSet,fiberFunctional_face]
      exact ⟨habP,habq⟩
    have hsub : ((vertexFiber P π q).vertices : Set (E n)) ⊆
        (P.vertices.erase x : Set (E n)) := by
      intro z hz
      rw [vertexFiber_vertices] at hz
      obtain ⟨hzP,hzq⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_erase.mpr
      refine ⟨?_,hzP⟩
      intro hzx
      have hxq : π x=q.val := hzx ▸ hzq
      exact hxextra (hxq.symm ▸ q.property)
    exact (convexHull_mono hsub) habF

end Papers.MinkowskiDeletionSummand

end
end
end BundlePart0

