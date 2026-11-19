module
public import Papers.ActualEdgeSupports
public import Papers.SupportFormIndependence
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Three actual incident edges cannot lie in an affine plane

Restrict the three actual edge support forms to the direction span.
Their zero-diagonal, strictly positive off-diagonal evaluation matrix
makes three linear forms independent. A plane has dual dimension at
most two. This proof uses no lower-bound or decomposability theorem.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open ExposedEdgeCenters
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem no_three_actual_edges_in_dim_two_set
    (P : ConvexPolytope d) (S : Set (E d)) (hS : faceDim S ≤ 2)
    (u : P.vertices) (hu : u.val ∈ S)
    (x : Fin 3 → P.vertices) (hinj : Function.Injective x)
    (hxS : ∀ i, (x i).val ∈ S)
    (hedge : ∀ i, GeneralVertexStep P u.val (x i).val) :
    False := by
  let L := vectorSpan ℝ S
  let v : Fin 3 → L := fun i =>
    ⟨(x i).val - u.val,vsub_mem_vectorSpan ℝ (hxS i) hu⟩
  let g : Fin 3 → E d →ᵃ[ℝ] ℝ := fun i =>
    Classical.choose (exists_nonnegative_affine_edge_form P u.property (hedge i))
  have hs (i : Fin 3) :
      (∀ z ∈ P.toSet, 0 ≤ g i z) ∧
      (∀ z ∈ P.toSet, g i z = 0 ↔ z ∈ segment ℝ u.val (x i).val) :=
    Classical.choose_spec (exists_nonnegative_affine_edge_form P u.property (hedge i))
  have hgu (i : Fin 3) : g i u.val = 0 :=
    ((hs i).2 u.val (vertex_mem_body_of_mem_vertices P u.property)).mpr
      (left_mem_segment ℝ _ _)
  have hgx (i : Fin 3) : g i (x i).val = 0 :=
    ((hs i).2 (x i).val (vertex_mem_body_of_mem_vertices P (x i).property)).mpr
      (right_mem_segment ℝ _ _)
  let f : Fin 3 → L →ₗ[ℝ] ℝ := fun i => (g i).linear.comp L.subtype
  have heval (i j : Fin 3) : f j (v i) = g j (x i).val := by
    change (g j).linear ((x i).val - u.val) = g j (x i).val
    have h := (g j).map_vadd u.val ((x i).val - u.val)
    change g j (((x i).val - u.val) + u.val) =
      (g j).linear ((x i).val - u.val) + g j u.val at h
    rw [sub_add_cancel,hgu j,add_zero] at h
    exact h.symm
  have hzero : ∀ i, f i (v i) = 0 := by
    intro i
    rw [heval,hgx]
  have hpositive : ∀ i j, i ≠ j → 0 < f j (v i) := by
    intro i j hij
    rw [heval]
    have hn := (hs j).1 (x i).val (vertex_mem_body_of_mem_vertices P (x i).property)
    have hne : g j (x i).val ≠ 0 := by
      intro hzero
      have hseg := ((hs j).2 (x i).val
        (vertex_mem_body_of_mem_vertices P (x i).property)).mp hzero
      rcases extreme_point_on_segment P.toSet
        (vertex_mem_body_extremePoints P (x i).property)
        (vertex_mem_body_of_mem_vertices P u.property)
        (vertex_mem_body_of_mem_vertices P (x j).property) hseg with h | h
      · exact (hedge i).2.1 h.symm
      · exact hij (hinj (Subtype.ext h))
    exact lt_of_le_of_ne hn hne.symm
  have hlin := Papers.RationalityTen.three_linearForms_independent_of_evaluations
    f v hzero hpositive
  have hmono := Submodule.finrank_mono
    (show Submodule.span ℝ (Set.range f) ≤ (⊤ : Submodule ℝ (L →ₗ[ℝ] ℝ)) from le_top)
  have hdual : finrank ℝ (L →ₗ[ℝ] ℝ) = finrank ℝ L :=
    LinearEquiv.finrank_eq (Basis.ofVectorSpace ℝ L).toDualEquiv.symm
  rw [finrank_span_eq_card hlin,Fintype.card_fin,finrank_top,hdual] at hmono
  change finrank ℝ L ≤ 2 at hS
  omega

theorem no_three_actual_edges_in_plane
    (P : ConvexPolytope d) {w x y z : E d}
    (hw : w ∈ P.vertices) (hx : x ∈ P.vertices)
    (hy : y ∈ P.vertices) (hz : z ∈ P.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : GeneralVertexStep P w x) (hwy : GeneralVertexStep P w y)
    (hwz : GeneralVertexStep P w z)
    (hplane : finrank ℝ (vectorSpan ℝ ({w,x,y,z} : Set (E d))) ≤ 2) :
    False := by
  let pts : Fin 3 → P.vertices := ![⟨x,hx⟩,⟨y,hy⟩,⟨z,hz⟩]
  apply no_three_actual_edges_in_dim_two_set P {w,x,y,z} hplane ⟨w,hw⟩
    (by simp) pts
  · intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [pts]
  · intro i
    fin_cases i <;> simp [pts]
  · intro i
    fin_cases i
    · exact hwx
    · exact hwy
    · exact hwz

end Papers.Polytopes

