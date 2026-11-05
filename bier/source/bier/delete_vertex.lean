import bier.geometry
import bier.polytopal_relabel

/-! Deleting an extreme vertex and recognizing exposed faces from vertex values. -/

noncomputable section

namespace Bier

open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ}

def deleteVertex (P : ConvexPolytope n) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) : ConvexPolytope n where
  vertices := P.vertices.erase v.val
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      apply inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))
      exact ⟨subset_convexHull ℝ _ hx, P.vertices_eq_extremePoints ▸
        (Finset.mem_of_mem_erase hx : x ∈ P.vertices)⟩
    · exact extremePoints_convexHull_subset

theorem deleteVertex_subset (P : ConvexPolytope n) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) : (deleteVertex P v hne).toSet ⊆ P.toSet :=
  convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))

def deleteVertexEmbedding (P : ConvexPolytope n) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) : VertexType (deleteVertex P v hne) ↪ VertexType P where
  toFun w := ⟨w.val, Finset.mem_of_mem_erase w.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun q : VertexType P => q.val) h)

@[simp] theorem deleteVertexEmbedding_val (P : ConvexPolytope n) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) (w : VertexType (deleteVertex P v hne)) :
    (deleteVertexEmbedding P v hne w).val = w.val := rfl

theorem max_on_hull_vertices (P : ConvexPolytope n) (l : E n →L[ℝ] ℝ) (c : ℝ)
    (h : ∀ v : VertexType P, l v.val ≤ c) : ∀ x ∈ P.toSet, l x ≤ c := by
  apply convexHull_min
  · intro x hx
    exact h ⟨x, hx⟩
  · exact convex_halfSpace_le l.toLinearMap.isLinear c

theorem vertexHull_exposed (P : ConvexPolytope n) (s : Finset (VertexType P))
    (hne : s.Nonempty) (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hle : ∀ v : VertexType P, l v.val ≤ c)
    (heq : ∀ v : VertexType P, l v.val = c ↔ v ∈ s) :
    P.IsFace (vertexHull P s) := by
  obtain ⟨v, hv⟩ := hne
  have hvc : l v.val = c := (heq v).mpr hv
  have hmax := max_on_hull_vertices P l c hle
  have hsub : vertexHull P s ⊆ P.toSet := convexHull_mono (by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact w.property)
  have hconst : ∀ x ∈ vertexHull P s, l x = c := by
    apply convexHull_min
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      exact (heq w).mpr hw
    · exact (convex_singleton c).linear_preimage l.toLinearMap
  have hverts : {x ∈ (P.vertices : Set (E n)) | l x = c} =
      ((s.image (fun w => w.val) : Finset (E n)) : Set (E n)) := by
    ext x
    constructor
    · rintro ⟨hx, hxc⟩
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, (heq ⟨x, hx⟩).mp hxc, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨w.property, (heq w).mpr hw⟩
  refine ⟨?_, ⟨v.val, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩⟩
  intro _
  refine ⟨l, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hsub hx, fun y hy => (hmax y hy).trans_eq (hconst x hx).symm⟩
  · rintro x ⟨hxP, hxmax⟩
    have hxc : l x = c := le_antisymm (hmax x hxP)
      (hvc ▸ hxmax v.val (subset_convexHull ℝ _ v.property))
    have hx := PlatoniciL3.faccia_argmax P.vertices l hxP hxmax
    rw [hxc, hverts] at hx
    exact hx

theorem face_vertex_exposer (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    ∃ (l : E n →L[ℝ] ℝ) (c : ℝ),
      (∀ v : VertexType P, l v.val ≤ c) ∧
      (∀ v : VertexType P, l v.val = c ↔ v.val ∈ F) := by
  obtain ⟨l, hl⟩ := hF.1 hF.2
  obtain ⟨x, hx⟩ := hF.2
  have hxmax := (hl ▸ hx).2
  refine ⟨l, l x, fun v => hxmax v.val (subset_convexHull ℝ _ v.property), ?_⟩
  intro v
  constructor
  · intro h
    rw [hl]
    exact ⟨subset_convexHull ℝ _ v.property, fun y hy => (hxmax y hy).trans_eq h.symm⟩
  · intro hv
    have hvmax := (hl ▸ hv).2
    exact le_antisymm (hxmax _ (subset_convexHull ℝ _ v.property)) (hvmax _ ((hl ▸ hx).1))

end Bier
