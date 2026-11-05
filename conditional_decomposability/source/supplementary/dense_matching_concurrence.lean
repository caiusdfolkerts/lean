module

public import consolidated_dev.projective_crossing_geometry

@[expose] public section

/-!
# Dense concurrence for an arbitrary matching of actual edges

This is the unrestricted concurrence statement of Lemma 2. The selected
matching is indexed independently of any coloring. Its cofacial graph may
use any witnessing two-faces, provided each witness contains exactly the
two selected matching edges that it joins.

The proof starts with the intersection of two cofacial edge lines. A line
outside that point cannot have two neighbors passing through it: their
witnessing two-faces would coincide and contain three selected edges.
The already proved dense graph closure lemma then gives the whole family.
-/

noncomputable section

namespace Papers.Polytopes.DenseMatchingConcurrence

open Set Module Papers.Coordinates
open ExposedEdgeCenters ExposedLineRanks ExposedProjectiveBridge
open HomogeneousFaceSpans CrossingLineGeometry
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d : ℕ} {I : Type*} [Fintype I]

/-- A matching of actual polytope-edge lines is concurrent under the
dense degree bound, with no coloring or complete-family hypothesis.

The witnessing-face condition says that an adjacent pair lies in an
actual two-face and that no third selected edge lies in that face.
The conclusion is projective concurrence, including points at infinity.
-/
theorem concurrent_of_dense_cofacial_matching
    (P : ConvexPolytope d) (left right : I → VertexType P)
    (hedge : ∀ i, GeneralVertexStep P (left i).val (right i).val)
    (hmatching : ∀ i j, i ≠ j →
      Disjoint ({(left i).val, (right i).val} : Set (E d))
        {(left j).val, (right j).val})
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hwitness : ∀ i j, G.Adj i j →
      ∃ F : Set (E d), P.IsFace F ∧ faceDim F = 2 ∧
        (left i).val ∈ F ∧ (right i).val ∈ F ∧
        (left j).val ∈ F ∧ (right j).val ∈ F ∧
        ∀ q, (left q).val ∈ F → (right q).val ∈ F → q = i ∨ q = j)
    (k : ℕ) (hdegree : ∀ i, k ≤ G.degree i)
    (hdense : Fintype.card I < 2 * k) :
    ∃ J : Submodule ℝ (E d × ℝ), finrank ℝ J = 1 ∧
      ∀ i, J ≤ edgeProjectiveLine (left i).val (right i).val := by
  classical
  let L : I → Submodule ℝ (E d × ℝ) :=
    fun i => edgeProjectiveLine (left i).val (right i).val
  have hline (i : I) : finrank ℝ (L i) = 2 := by
    have h := edgeLine_finrank_eq_two (hedge i).2.1
    rw [exposed_edgeLine_eq_edgeProjectiveLine] at h
    exact h
  let support (i : I) : E d →ᵃ[ℝ] ℝ :=
    Classical.choose
      (exists_nonnegative_affine_edge_form P (left i).property (hedge i))
  have hzero (i : I) (x : E d) (hx : x ∈ P.toSet) :
      support i x = 0 ↔ x ∈ segment ℝ (left i).val (right i).val :=
    (Classical.choose_spec
      (exists_nonnegative_affine_edge_form P (left i).property (hedge i))).2 x hx
  have hleft (i : I) : support i (left i).val = 0 :=
    (hzero i _ (vertex_mem_body_of_mem_vertices P (left i).property)).mpr
      (left_mem_segment ℝ _ _)
  have hright (i : I) : support i (right i).val = 0 :=
    (hzero i _ (vertex_mem_body_of_mem_vertices P (right i).property)).mpr
      (right_mem_segment ℝ _ _)
  have hpair (i j : I) (hij : i ≠ j) :
      3 ≤ finrank ℝ ↥(L i ⊔ L j) := by
    have hll : (left i).val ≠ (left j).val := by
      intro he
      exact Set.disjoint_left.mp (hmatching i j hij)
        (show (left i).val ∈ ({(left i).val, (right i).val} : Set (E d)) by simp)
        (by simp [he])
    have hlr : (left i).val ≠ (right j).val := by
      intro he
      exact Set.disjoint_left.mp (hmatching i j hij)
        (show (left i).val ∈ ({(left i).val, (right i).val} : Set (E d)) by simp)
        (by simp [he])
    have h := matching_lines_joint_rank_ge_three
      (y := (right i).val) P.toSet (support j)
      (vertex_mem_body_extremePoints P (left i).property)
      (vertex_mem_body_of_mem_vertices P (left j).property)
      (vertex_mem_body_of_mem_vertices P (right j).property)
      (hedge j).2.1 (hleft j) (hright j) (hzero j) hll hlr
    rw [exposed_edgeLine_eq_edgeProjectiveLine,
      exposed_edgeLine_eq_edgeProjectiveLine] at h
    exact h
  have hcofacial (i j : I) (hij : G.Adj i j) :
      finrank ℝ ↥(L i ⊔ L j) ≤ 3 := by
    obtain ⟨F, hF, hFdim, hiL, hiR, hjL, hjR, _⟩ := hwitness i j hij
    have hle : L i ⊔ L j ≤ homogeneousSpan (K := ℝ) F :=
      sup_le (line_le_span hiL hiR) (line_le_span hjL hjR)
    have hdim := Submodule.finrank_mono hle
    rwa [twoFace_homogeneousSpan_rank F hF.2 hFdim] at hdim
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let e : I := Classical.choice inferInstance
    have hk : 0 < k := by omega
    have hn : (G.neighborFinset e).Nonempty := by
      apply Finset.card_pos.mp
      have h := hdegree e
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        (show 0 < G.degree e by omega)
    obtain ⟨f, hf⟩ := hn
    have hef : G.Adj e f := (G.mem_neighborFinset e f).mp hf
    have hspan : finrank ℝ ↥(L e ⊔ L f) = 3 :=
      le_antisymm (hcofacial e f hef) (hpair e f hef.ne)
    obtain ⟨J, hJ, hJe, hJf⟩ :=
      common_point_of_coplanar_distinct_lines (L e) (L f) (hline e) (hline f) hspan
    let S : Set I := {i | J ≤ L i}
    have hS : 2 ≤ Nat.card S := by
      let se : S := ⟨e, hJe⟩
      let sf : S := ⟨f, hJf⟩
      have hne : se ≠ sf := fun h => hef.ne (congrArg Subtype.val h)
      have hc := Finset.card_mono (Finset.subset_univ ({se, sf} : Finset S))
      have hc2 : ({se, sf} : Finset S).card = 2 := by simp [hne]
      rw [hc2, Finset.card_univ] at hc
      simpa only [Nat.card_eq_fintype_card] using hc
    have hclosed : ∀ v ∉ S, ∀ x ∈ S, ∀ y ∈ S,
        G.Adj v x → G.Adj v y → x = y := by
      intro v hv x hx y hy hvx hvy
      by_contra hxy
      obtain ⟨F, hF, hFdim, hvFL, hvFR, hxFL, hxFR, hFexact⟩ :=
        hwitness v x hvx
      obtain ⟨H, hH, hHdim, hvHL, hvHR, hyHL, hyHR, _⟩ :=
        hwitness v y hvy
      have hlow : 3 ≤ finrank ℝ ↥(L v ⊔ J) := by
        by_contra h
        have heq : L v = L v ⊔ J :=
          Submodule.eq_of_le_of_finrank_le le_sup_left (by
            have hd := hline v
            omega)
        apply hv
        change J ≤ L v
        rw [heq]
        exact le_sup_right
      have hJF : J ≤ homogeneousSpan (K := ℝ) F :=
        hx.trans (line_le_span hxFL hxFR)
      have hJH : J ≤ homogeneousSpan (K := ℝ) H :=
        hy.trans (line_le_span hyHL hyHR)
      have hFH : F = H :=
        actual_twoFaces_eq_of_two_lines P F H hF hH hF.2 hH.2 hFdim hHdim
          (L v) J hlow (line_le_span hvFL hvFR) (line_le_span hvHL hvHR) hJF hJH
      have hyF : (left y).val ∈ F ∧ (right y).val ∈ F := by
        rw [hFH]
        exact ⟨hyHL, hyHR⟩
      rcases hFexact y hyF.1 hyF.2 with hyv | hyx
      · exact hv (hyv ▸ hy)
      · exact hxy hyx.symm
    have heqS : S = Set.univ :=
      DenseGraphClosure.eq_univ_of_outside_neighbors_unique G k hdegree hdense S hS hclosed
    refine ⟨J, hJ, ?_⟩
    intro i
    have hi : i ∈ S := by rw [heqS]; trivial
    exact hi
  · refine ⟨Submodule.span ℝ ({homogenize (0 : E d)} : Set (E d × ℝ)), ?_, ?_⟩
    · exact finrank_span_singleton (point_ne_zero (0 : E d))
    · intro i
      exact (hI ⟨i⟩).elim

end Papers.Polytopes.DenseMatchingConcurrence

end
