import cubical_indecomposability.block.actual_edges
import cubical_indecomposability.block.interfaces
import cubical_indecomposability.block.rigidity
import cubical_indecomposability.face_restrictions

/-!
# The determining facets and the two-dimensional restriction image

The exact linear identities are applied to arbitrary real redrawings on the
actual exposed edges. Restriction then descends to the quotient by translations.
The two coordinates used on F are differences from vertex 24, so the dimension
bound concerns precisely the quotient space in Proposition 5(iii).
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- Restrict an actual vertex redrawing to the explicit vertex labels. -/
def assignment (h : redrawingSpace polytope) : Rigidity.Assignment :=
  fun v i => h (labelledVertex v) i

theorem labelledVertex_surjective : Function.Surjective labelledVertex := by
  intro v
  have hv := (Finset.ext_iff.mp polytope_vertices (v : E 4)).mp v.property
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
  exact ⟨w, Subtype.ext hw⟩

/-- The exact primitive direction spans the direction of the actual edge. -/
theorem edge_difference (e : Fin 80) (i : Fin 4) :
    p (edgeVertex e 1) i - p (edgeVertex e 0) i =
      (Rigidity.multiplier e : ℝ) /
        ((q (edgeVertex e 0) 4 : ℝ) * (q (edgeVertex e 1) 4 : ℝ)) *
          (Rigidity.direction e i : ℝ) := by
  have h0 : (q (edgeVertex e 0) 4 : ℝ) ≠ 0 :=
    ne_of_gt (homogeneous_last_real_pos _)
  have h1 : (q (edgeVertex e 1) 4 : ℝ) ≠ 0 :=
    ne_of_gt (homogeneous_last_real_pos _)
  have hs :
      (q (edgeVertex e 1) i.castSucc : ℝ) * (q (edgeVertex e 0) 4 : ℝ) -
        (q (edgeVertex e 0) i.castSucc : ℝ) * (q (edgeVertex e 1) 4 : ℝ) =
          (Rigidity.multiplier e : ℝ) * (Rigidity.direction e i : ℝ) := by
    exact_mod_cast Rigidity.direction_scale e i
  simp only [p_apply]
  field_simp [h0, h1]
  nlinarith [hs]

/-- Geometric parallelism implies all the certified real linear equations. -/
theorem constraints_of_redrawing (h : redrawingSpace polytope) :
    Rigidity.Constraints (assignment h) := by
  intro e i
  obtain ⟨a, ha⟩ := h.property (labelledVertex (edgeVertex e 0))
    (labelledVertex (edgeVertex e 1)) (declaredEdge e)
  have hc (j : Fin 4) :
      assignment h (edgeVertex e 1) j - assignment h (edgeVertex e 0) j =
        a * (p (edgeVertex e 1) j - p (edgeVertex e 0) j) := by
    have hj := congrArg (fun x : E 4 => x j) ha
    simpa only [assignment, labelledVertex, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] using hj
  unfold Rigidity.crossRow
  rw [hc i, hc (Rigidity.pivot e), edge_difference e i,
    edge_difference e (Rigidity.pivot e)]
  ring

/-- A labelled point of a face, as an actual extreme vertex of that face. -/
def labelledFaceVertex {S : Set (E 4)} (hS : polytope.IsFace S)
    (v : Fin 32) (hv : p v ∈ S) : Vertex (facePolytope polytope hS) :=
  ⟨p v, Finset.mem_filter.mpr ⟨vertex_mem v, hv⟩⟩

@[simp] theorem faceVertex_labelledFaceVertex {S : Set (E 4)}
    (hS : polytope.IsFace S) (v : Fin 32) (hv : p v ∈ S) :
    faceVertex polytope hS (labelledFaceVertex hS v hv) = labelledVertex v := rfl

/-- The algebraic zero-restriction criterion implies the paper's genuine
quotient-space definition of a determining facet. -/
theorem determines_of_label_kernel (f : Fin 24)
    (hcert : ∀ h : Rigidity.Assignment, Rigidity.Constraints h →
      (∀ v ∈ facetLabels f, ∀ i, h v i = 0) → ∀ v i, h v i = 0) :
    FaceDetermines polytope (facet_isFace f) := by
  apply determines_of_vanishing polytope (facet_isFace f)
  intro h hz v
  obtain ⟨w, rfl⟩ := labelledVertex_surjective v
  ext i
  apply hcert (assignment h) (constraints_of_redrawing h) ?_ w i
  intro u hu j
  have huf : p u ∈ facet f := (vertex_mem_facet_iff f u).mpr hu
  have hj := congrArg (fun x : E 4 => x j)
    (hz (labelledFaceVertex (facet_isFace f) u huf))
  exact hj

/-- Proposition 5(ii): H determines the full deformation space. -/
theorem H_determines : FaceDetermines polytope H_isFace :=
  determines_of_label_kernel 21 Rigidity.determined_by_H

/-- Proposition 5(ii): G determines the full deformation space. -/
theorem G_determines : FaceDetermines polytope G_isFace :=
  determines_of_label_kernel 1 Rigidity.determined_by_G

/-- The common anchor for the two translation-invariant F coordinates. -/
def Fanchor : Vertex (facePolytope polytope F_isFace) :=
  labelledFaceVertex F_isFace 24 ((vertex_mem_F 24).mpr (by decide))

def FdifferenceVertices : Fin 2 → Vertex (facePolytope polytope F_isFace) :=
  ![labelledFaceVertex F_isFace 25 ((vertex_mem_F 25).mpr (by decide)),
    labelledFaceVertex F_isFace 28 ((vertex_mem_F 28).mpr (by decide))]

def FdifferenceCoordinates : Fin 2 → Fin 4 := ![0, 1]

/-- Vanishing of the six displayed scalar values forces vanishing on F. -/
theorem vanishes_on_F_of_seed_values (h : Rigidity.Assignment)
    (hc : Rigidity.Constraints h) (h24 : ∀ i, h 24 i = 0)
    (h25 : h 25 0 = 0) (h28 : h 28 1 = 0)
    (v : Fin 32) (hv : v ∈ facetLabels 5) (i : Fin 4) : h v i = 0 :=
  Rigidity.zero_on_F_of_six h hc h24 h25 h28 v hv i

/-- Proposition 5(iii), stated as the finrank of the actual quotient restriction image. -/
theorem F_restriction_dimension :
    Module.finrank ℝ (deformationRestriction polytope F_isFace).range ≤ 2 := by
  apply restriction_rank_le_of_difference_determination polytope F_isFace
    Fanchor FdifferenceVertices FdifferenceCoordinates
  intro h heval v
  let k : redrawingSpace polytope := h - translationMap polytope (h (labelledVertex 24))
  have h24 (i : Fin 4) : assignment k 24 i = 0 := by
    change h (labelledVertex 24) i - h (labelledVertex 24) i = 0
    exact sub_self _
  have h25 : assignment k 25 0 = 0 := heval 0
  have h28 : assignment k 28 1 = 0 := heval 1
  obtain ⟨w, hw⟩ := labelledVertex_surjective (faceVertex polytope F_isFace v)
  have hwF : w ∈ facetLabels 5 := by
    apply (vertex_mem_facet_iff 5 w).mp
    have hmem := faceVertex_mem polytope F_isFace v
    rwa [← hw] at hmem
  have hk (i : Fin 4) : assignment k w i = 0 :=
    vanishes_on_F_of_seed_values (assignment k) (constraints_of_redrawing k)
      h24 h25 h28 w hwF i
  ext i
  have hi := hk i
  change h (labelledVertex w) i - h (labelledVertex 24) i = 0 at hi
  rw [hw] at hi
  exact sub_eq_zero.mp hi

end CubicalIndecomposability.Block
