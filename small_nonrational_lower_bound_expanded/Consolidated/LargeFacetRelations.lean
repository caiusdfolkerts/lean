module
public import Papers.ActualPolygonRelationBudget
public import Papers.MatrixSupportCounts
public import Papers.PolytopeBoundaryIntersections
public import Papers.PolygonDiagonalCounting
public import Mathlib.Tactic.FinCases
public import Papers.PolytopeEulerRadialFigure
public import Mathlib.Data.Fintype.EquivFin
public import Papers.NineVertexFacetShapes
public import Papers.SmallFacetSparseSupport
public import Papers.IncidenceCoreGeometry

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/FourQuadrilateralRelationRank.lean -/







@[expose] public section

/-!
# Four quadrilateral relations have rank at least three

This is the zero-set argument used in Appendix C.1. Four nonzero rows,
each supported on four labels, cannot span a plane if every two supports
meet in at most two labels. In a plane, any two rows span; consequently
an active coordinate can vanish on at most one of the four rows. Counting
entries gives at most five active coordinates, whereas two supports already
use at least six. The actual endpoint derives all support conditions from
actual two-faces and extreme-point independence.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators

/-- A purely linear support obstruction, without geometric hypotheses. -/
theorem four_four_support_rows_rank_ge_three {n : ℕ}
    (C : Fin 4 → Fin n → ℝ)
    (hfour : ∀ i, (vectorSupport (C i)).card = 4)
    (hinter : ∀ i j, i ≠ j →
      (vectorSupport (C i) ∩ vectorSupport (C j)).card ≤ 2) :
    3 ≤ finrank ℝ (Submodule.span ℝ (Set.range C)) := by
  have hnonzero (i : Fin 4) : C i ≠ 0 := by
    intro h
    have hc := hfour i
    rw [h] at hc
    simp [vectorSupport] at hc
  have hpair (i j : Fin 4) (hij : i ≠ j) :
      LinearIndependent ℝ (![C i, C j] : Fin 2 → Fin n → ℝ) := by
    rw [linearIndependent_fin2]
    constructor
    · simpa using hnonzero j
    · intro a heq
      have hex : ∃ k, k ∈ vectorSupport (C i) ∧ k ∉ vectorSupport (C j) := by
        by_contra h
        push_neg at h
        have hb := hinter i j hij
        rw [Finset.inter_eq_left.mpr h, hfour i] at hb
        omega
      obtain ⟨k, hki, hkj⟩ := hex
      have hi : C i k ≠ 0 := (mem_vectorSupport _ _).mp hki
      have hj : C j k = 0 := by simpa using hkj
      have hh := congrFun heq k
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
        smul_eq_mul, hj, mul_zero] at hh
      exact hi hh.symm
  by_contra hge
  have hdim : finrank ℝ (Submodule.span ℝ (Set.range C)) ≤ 2 := by omega
  have hspan (i j : Fin 4) (hij : i ≠ j) :
      Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) =
        Submodule.span ℝ (Set.range C) := by
    have hle : Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) ≤
        Submodule.span ℝ (Set.range C) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.subset_span ⟨j, rfl⟩
    have htwo : finrank ℝ
        (Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ))) = 2 := by
      simpa using finrank_span_eq_card (hpair i j hij)
    have hlow := Submodule.finrank_mono hle
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hcolumn (k : Fin n) (hk : k ∈ activeColumns C) :
      3 ≤ (columnSupport C k).card := by
    by_contra hsmall
    let Z := (Finset.univ : Finset (Fin 4)) \ columnSupport C k
    have hc : Z.card + (columnSupport C k).card = 4 := by
      simpa only [Z, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (columnSupport C k))
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < Z.card by omega)
    have hi0 : C i k = 0 := by
      have h := (Finset.mem_sdiff.mp hi).2
      simpa [columnSupport] using h
    have hj0 : C j k = 0 := by
      have h := (Finset.mem_sdiff.mp hj).2
      simpa [columnSupport] using h
    have hker : Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) ≤
        (LinearMap.proj k : (Fin n → ℝ) →ₗ[ℝ] ℝ).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact hi0
      · exact hj0
    rw [hspan i j hij] at hker
    obtain ⟨a, ha⟩ := (mem_activeColumns C k).mp hk
    exact ha (hker (Submodule.subset_span ⟨a, rfl⟩))
  have hentries : 3 * (activeColumns C).card ≤ 16 := by
    have hcount : 3 * (activeColumns C).card ≤ totalNonzeros C := by
      rw [totalNonzeros_eq_sum_columns]
      calc
        3 * (activeColumns C).card = ∑ _k ∈ activeColumns C, 3 := by simp [mul_comm]
        _ ≤ ∑ k ∈ activeColumns C, (columnSupport C k).card :=
          Finset.sum_le_sum hcolumn
        _ ≤ ∑ k, (columnSupport C k).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
    have hn : totalNonzeros C = 16 := by simp [totalNonzeros, hfour]
    simpa only [hn] using hcount
  have hused : 6 ≤ (activeColumns C).card := by
    have hsub : vectorSupport (C 0) ∪ vectorSupport (C 1) ⊆ activeColumns C := by
      intro k hk
      apply (mem_activeColumns C k).mpr
      rcases Finset.mem_union.mp hk with h | h
      · exact ⟨0, (mem_vectorSupport _ _).mp h⟩
      · exact ⟨1, (mem_vectorSupport _ _).mp h⟩
    have hc := Finset.card_union_add_card_inter (vectorSupport (C 0)) (vectorSupport (C 1))
    rw [hfour, hfour] at hc
    have hi := hinter 0 1 (by decide)
    have hle := Finset.card_le_card hsub
    omega
  omega

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.RationalityTen.SimplicialFiveFacetGeometry Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds
open Papers.PolytopeFacetSurplus Papers.PolytopeBoundaryIntersections

/-- Proper intersections give the support bound used by the linear lemma. -/
theorem actual_two_face_labels_inter_card_le_two {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (R S : Face P 2) (hRS : R ≠ S) :
    (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val).card ≤ 2 := by
  have hc : (faceCode P 2 R ∩ faceCode P 2 S).card ≤ 2 := by
    rcases two_face_intersection P R S hRS with h | ⟨E, _, _, heq⟩
    · omega
    · rw [heq, faceCode_card, one_face_vertex_card]
  have himage : (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val).image e =
      faceCode P 2 R ∩ faceCode P 2 S := by
    ext v
    simp only [Finset.mem_image, Finset.mem_inter, mem_actualFaceLabels,
      faceCode, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨hiR, hiS⟩, rfl⟩
      exact ⟨hiR, hiS⟩
    · intro h
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      simpa using h
  rw [← himage, Finset.card_image_of_injective _ e.injective] at hc
  exact hc

theorem globalRelationSpace_inf {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S T : Finset (Fin n)) :
    globalRelationSpace p S ⊓ globalRelationSpace p T = globalRelationSpace p (S ∩ T) := by
  ext v
  simp only [Submodule.mem_inf, mem_globalRelationSpace_iff]
  constructor
  · rintro ⟨⟨hS, hker⟩, ⟨hT, _⟩⟩
    refine ⟨?_, hker⟩
    intro i hi
    by_cases hiS : i ∈ S
    · exact hT i (fun hiT => hi (Finset.mem_inter.mpr ⟨hiS, hiT⟩))
    · exact hS i hiS
  · rintro ⟨hST, hker⟩
    exact ⟨⟨fun i hi => hST i (fun h => hi (Finset.mem_inter.mp h).1), hker⟩,
      ⟨fun i hi => hST i (fun h => hi (Finset.mem_inter.mp h).2), hker⟩⟩

/-- Distinct polygon relation spaces have zero intersection. Their only
possible shared coefficients lie on at most two extreme vertices. -/
theorem actual_distinct_polygon_relation_spaces_inf {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (hP : 3 ≤ P.vertices.card)
    (R S : Face P 2) (hRS : R ≠ S) :
    globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val) ⊓
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e S.val) = ⊥ := by
  rw [globalRelationSpace_inf]
  apply Submodule.finrank_eq_zero.mp
  have hcard := actual_two_face_labels_inter_card_le_two P e R S hRS
  have hrank := subsetRank_of_independent (vertexCoordinates P e)
    (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val)
    (vertexCoordinates_small_independent P e hP _ (by omega))
  have hdim := globalRelationSpace_finrank (vertexCoordinates P e)
    (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val)
  rw [hrank] at hdim
  omega

/-- The two local polygon ranks add. In particular a pentagon with a
quadrilateral forces rank at least three, and two pentagons force four. -/
theorem actual_distinct_polygon_relations_rank_add {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (R S : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) :
    Nat.card (VerticesOn P R.val.val.carrier) +
      Nat.card (VerticesOn P S.val.val.carrier) ≤ actualPolygonRelationRank P e F + 6 := by
  have hsmall : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  let U := globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val.val)
  let V := globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e S.val.val)
  have hzero : U ⊓ V = ⊥ := actual_distinct_polygon_relation_spaces_inf P e hsmall
    R.val S.val (fun h => hRS (Subtype.ext h))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hzero, finrank_bot, add_zero] at hsum
  have hle : U ⊔ V ≤ polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) := by
    apply sup_le
    · exact globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
        (Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩)
    · exact globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
        (Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩)
  have hdim := Submodule.finrank_mono hle
  have hR := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e R.val.val)
  have hS := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e S.val.val)
  rw [actualFaceLabels_rank, R.val.property, actualFaceLabels_card] at hR
  rw [actualFaceLabels_rank, S.val.property, actualFaceLabels_card] at hS
  change finrank ℝ U + 3 = _ at hR
  change finrank ℝ V + 3 = _ at hS
  change finrank ℝ (U ⊔ V : Submodule ℝ (Fin n → ℝ)) ≤
    actualPolygonRelationRank P e F at hdim
  omega

/-- Appendix C.1 for four distinct quadrilateral two-faces of an actual
facet. The rows are chosen inside their actual homogeneous relation spaces. -/
theorem actual_four_quadrilateral_relation_rank {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (R : Fin 4 → FaceBelow P F.val.carrier 2)
    (hR : Function.Injective R)
    (hfour : ∀ i, Nat.card (VerticesOn P (R i).val.val.carrier) = 4) :
    3 ≤ actualPolygonRelationRank P e F := by
  have hsmall : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  let p := vertexCoordinates P e
  let S := fun i => actualFaceLabels P e (R i).val.val
  have hcard (i : Fin 4) : (S i).card = 4 :=
    (actualFaceLabels_card P e (R i).val.val).trans (hfour i)
  have hex (i : Fin 4) : ∃ v : Fin n → ℝ,
      v ∈ globalRelationSpace p (S i) ∧ v ≠ 0 := by
    have hd := globalRelationSpace_finrank p (S i)
    have hr : subsetRank p (S i) = 3 := by
      simpa only [p, S, actualFaceLabels_rank, (R i).val.property] using
        actualFaceLabels_rank P e (R i).val.val
    rw [hr, hcard i] at hd
    have hne : globalRelationSpace p (S i) ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    exact (globalRelationSpace p (S i)).ne_bot_iff.mp hne
  choose C hC hCne using hex
  have hsupp (i : Fin 4) : vectorSupport (C i) = S i := by
    have hfull := four_relation_full_support p
      (vertexCoordinates_small_independent P e hsmall) (hcard i) (hC i) (hCne i)
    have hout := ((mem_globalRelationSpace_iff p (S i) (C i)).mp (hC i)).1
    ext j
    rw [mem_vectorSupport]
    constructor
    · intro hj
      by_contra hjS
      exact hj (hout j hjS)
    · exact hfull j
  have hthree : 3 ≤ finrank ℝ (Submodule.span ℝ (Set.range C)) := by
    apply four_four_support_rows_rank_ge_three C
    · intro i
      rw [hsupp i, hcard i]
    · intro i j hij
      rw [hsupp i, hsupp j]
      apply actual_two_face_labels_inter_card_le_two P e
      intro h
      exact hij (hR (Subtype.ext h))
  have hspan : Submodule.span ℝ (Set.range C) ≤
      polygonRelationSpan p (polygonLabelsBelow P e F) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply globalRelationSpace_le_polygonRelationSpan p
      (Finset.mem_image.mpr ⟨R i, Finset.mem_univ _, rfl⟩)
    exact hC i
  exact hthree.trans (Submodule.finrank_mono hspan)

def facetQuadrilateralFaces {d : ℕ} (P : ConvexPolytope d) (F : Face P 3) :
    Finset (FaceBelow P F.val.carrier 2) :=
  Finset.univ.filter fun R => Nat.card (VerticesOn P R.val.val.carrier) = 4

theorem facetQuadrilateralFaces_card {d : ℕ} (P : ConvexPolytope d) (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    facetPolygonExcess P F = ((facetQuadrilateralFaces P F).card : ℤ) := by
  have hpoint (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3 =
        if Nat.card (VerticesOn P R.val.val.carrier) = 4 then 1 else 0 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    have hhi := hpolygons R
    split_ifs <;> omega
  rw [Papers.PolytopeFaceRestriction.facetPolygonExcess_eq_sum_faceBelow]
  simp_rw [hpoint]
  simp [facetQuadrilateralFaces]

theorem actual_rank_ge_three_of_four_quadrilateral_faces {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hfour : 4 ≤ (facetQuadrilateralFaces P F).card) :
    3 ≤ actualPolygonRelationRank P e F := by
  obtain ⟨R, hR⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (by simpa only [Fintype.card_fin] using hfour)
  apply actual_four_quadrilateral_relation_rank P hP e F R R.injective
  intro i
  exact (Finset.mem_filter.mp (hR ⟨i, rfl⟩)).2

/-- The stronger seven-vertex bound when every polygon is a triangle or
quadrilateral. This is unconditional actual geometry, including the
rank-two degeneracies of three quadrilateral rows. -/
theorem seven_facet_surplus_ge_two_of_small_polygons {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    2 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  have hsmall : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hgmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hgmax
  have hd := facet_diagonal_count_twice_polygon_excess P F hpolygons
  have hq := facetQuadrilateralFaces_card P F hpolygons
  have hdefect : facetPolygonExcess P F ≤ (actualPolygonRelationRank P e F : ℤ) + 1 := by
    by_cases hzero : actualPolygonRelationRank P e F = 0
    · have hz := actualPolygonRelationRank_zero P e F hzero
      rw [hz] at hd
      omega
    by_cases hone : actualPolygonRelationRank P e F = 1
    · have ho := actualPolygonRelationRank_one P e hsmall F hone
      rw [ho] at hd
      omega
    by_cases hfour : 4 ≤ (facetQuadrilateralFaces P F).card
    · have hr := actual_rank_ge_three_of_four_quadrilateral_faces P hP e F hfour
      omega
    · omega
  have hdQ : (facetDiagonalCount P F : ℚ) = 2 * (facetPolygonExcess P F : ℚ) := by
    exact_mod_cast hd
  have heQ : (facetPolygonExcess P F : ℚ) ≤ (actualPolygonRelationRank P e F : ℚ) + 1 := by
    exact_mod_cast hdefect
  unfold rankSurplus
  rw [hF]
  norm_num only [Nat.cast_ofNat]
  linarith

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/SevenFacetSurplus.lean -/



@[expose] public section

/-!
# The complete seven-vertex facet surplus bound

Appendix C.1 at seven vertices follows from the actual two-face intersection
bound and the four-quadrilateral rank lemma. A hexagon has only triangular
companions. A pentagon has at most two units of remaining polygon excess;
a quadrilateral companion adds an independent relation. No facet catalogue
or genericity hypothesis is used.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds
open Papers.PolytopeFacetSurplus Papers.PolytopeFaceNonedges Papers.PolytopeFaceRestriction

/-- Two different polygon faces use at most all facet vertices plus their
at-most-two shared vertices. -/
theorem actual_two_polygon_vertex_count_bound {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (R S : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) :
    Nat.card (VerticesOn P R.val.val.carrier) + Nat.card (VerticesOn P S.val.val.carrier) ≤
      facetVertexCount P F + 2 := by
  have hinter := actual_two_face_labels_inter_card_le_two P e R.val S.val
    (fun h => hRS (Subtype.ext h))
  have hsub : actualFaceLabels P e R.val.val ∪ actualFaceLabels P e S.val.val ⊆
      actualFaceLabels P e F.val := Finset.union_subset
    (actualFaceLabels_mono P e R.property) (actualFaceLabels_mono P e S.property)
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter
    (actualFaceLabels P e R.val.val) (actualFaceLabels P e S.val.val)
  rw [actualFaceLabels_card, actualFaceLabels_card] at hsum
  rw [actualFaceLabels_card] at hcard
  change _ ≤ facetVertexCount P F at hcard
  omega

/-- Every polygon contributes its whole actual relation space to the local
span, so its number of vertices is at most the local relation rank plus three. -/
theorem actual_polygon_card_le_relation_rank_add_three {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (R : FaceBelow P F.val.carrier 2) :
    Nat.card (VerticesOn P R.val.val.carrier) ≤ actualPolygonRelationRank P e F + 3 := by
  have hinc : globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val.val) ≤
      polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) :=
    globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
      (Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩)
  have hle := Submodule.finrank_mono hinc
  have hdim := globalRelationSpace_finrank (vertexCoordinates P e)
    (actualFaceLabels P e R.val.val)
  rw [actualFaceLabels_rank, R.val.property, actualFaceLabels_card] at hdim
  change _ ≤ actualPolygonRelationRank P e F at hle
  omega

/-- If only one polygon can have diagonals, every allocated diagonal belongs
to that polygon. This includes the pyramid cases without assuming a pyramid
construction theorem. -/
theorem facet_diagonal_count_unique_polygon {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (R : FaceBelow P F.val.carrier 2)
    (hother : ∀ S : FaceBelow P F.val.carrier 2, S ≠ R →
      Nat.card (VerticesOn P S.val.val.carrier) = 3) :
    facetDiagonalCount P F = Nat.card (NonedgesOn P R.val.val.carrier) := by
  have hpoint (S : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P S.val.val.carrier) : ℤ) =
        if S = R then (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) else 0 := by
    by_cases h : S = R
    · subst S
      simp
    · rw [if_neg h]
      have hc := polygon_nonedge_count P S.val
      rw [hother S h] at hc
      norm_num only [Nat.choose] at hc
      exact_mod_cast (show Nat.card (NonedgesOn P S.val.val.carrier) = 0 by omega)
  have h := facetDiagonalCount_eq_sum_polygon_diagonals P F
  have heq : (∑ S : FaceBelow P F.val.carrier 2,
      (Nat.card (NonedgesOn P S.val.val.carrier) : ℤ)) =
      ∑ S : FaceBelow P F.val.carrier 2, if S = R then
        (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) else 0 :=
    Finset.sum_congr rfl (fun S _ => hpoint S)
  rw [heq] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact_mod_cast h

/-- The unique pentagon contributes one additional diagonal beyond twice
polygon excess; every triangle or quadrilateral contributes exactly twice. -/
theorem facet_diagonal_count_one_pentagon {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (R : FaceBelow P F.val.carrier 2)
    (hR : Nat.card (VerticesOn P R.val.val.carrier) = 5)
    (hother : ∀ S : FaceBelow P F.val.carrier 2, S ≠ R →
      Nat.card (VerticesOn P S.val.val.carrier) ≤ 4) :
    (facetDiagonalCount P F : ℤ) = 2 * facetPolygonExcess P F + 1 := by
  have hpoint (S : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P S.val.val.carrier) : ℤ) =
        2 * ((Nat.card (VerticesOn P S.val.val.carrier) : ℤ) - 3) +
          if S = R then 1 else 0 := by
    have hc := polygon_nonedge_count P S.val
    by_cases h : S = R
    · subst S
      rw [hR] at hc
      rw [hR, if_pos rfl]
      norm_num only [Nat.choose] at hc ⊢
      omega
    · have hlo := face_vertices_card_ge_dim_add_one P 2 S.val
      have hhi := hother S h
      have hcard : Nat.card (VerticesOn P S.val.val.carrier) = 3 ∨
          Nat.card (VerticesOn P S.val.val.carrier) = 4 := by omega
      rw [if_neg h]
      rcases hcard with hcard | hcard <;> rw [hcard] at hc ⊢ <;>
        norm_num only [Nat.choose] at hc ⊢ <;> omega
  rw [facetDiagonalCount_eq_sum_polygon_diagonals, facetPolygonExcess_eq_sum_faceBelow]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- The seven-vertex half-integral surplus bound in Appendix C.1. -/
theorem seven_facet_surplus_ge_three_halves {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7) :
    (3 : ℚ) / 2 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  have hmax (R : FaceBelow P F.val.carrier 2) :
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 6 := by
    have h := polygon_card_lt_containing_facet P R.val F R.property
    rw [hF] at h
    omega
  have hpair (R S : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) :
      Nat.card (VerticesOn P R.val.val.carrier) +
        Nat.card (VerticesOn P S.val.val.carrier) ≤ 9 := by
    simpa only [hF] using actual_two_polygon_vertex_count_bound P e F R S hRS
  by_cases hhex : ∃ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) = 6
  · obtain ⟨R, hR⟩ := hhex
    have hother (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
        Nat.card (VerticesOn P S.val.val.carrier) = 3 := by
      have hlo := face_vertices_card_ge_dim_add_one P 2 S.val
      have hi := hpair S R hSR
      rw [hR] at hi
      omega
    have hd := facet_diagonal_count_unique_polygon P F R hother
    have hdiag := polygon_nonedge_count P R.val
    rw [hR] at hdiag
    norm_num only [Nat.choose] at hdiag
    have hge := actual_polygon_card_le_relation_rank_add_three P e F R
    rw [hR] at hge
    have hrQ : (3 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 3 ≤ actualPolygonRelationRank P e F by omega)
    have hd9 : facetDiagonalCount P F = 9 := by omega
    unfold rankSurplus
    rw [hF, hd9]
    norm_num only [Nat.cast_ofNat]
    linarith
  push_neg at hhex
  by_cases hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4
  · exact (show (3 : ℚ) / 2 ≤ 2 by norm_num).trans
      (seven_facet_surplus_ge_two_of_small_polygons P hP e F hF hsmall)
  push_neg at hsmall
  obtain ⟨R, hRlarge⟩ := hsmall
  have hR : Nat.card (VerticesOn P R.val.val.carrier) = 5 := by
    have hRmax := hmax R
    have hRne := hhex R
    omega
  have hother (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
      Nat.card (VerticesOn P S.val.val.carrier) ≤ 4 := by
    have h := hpair S R hSR
    rw [hR] at h
    omega
  by_cases hquad : ∃ S : FaceBelow P F.val.carrier 2,
      S ≠ R ∧ Nat.card (VerticesOn P S.val.val.carrier) = 4
  · obtain ⟨S, hSR, hS⟩ := hquad
    have hr := actual_distinct_polygon_relations_rank_add P hP e F R S hSR.symm
    rw [hR, hS] at hr
    have hrQ : (3 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 3 ≤ actualPolygonRelationRank P e F by omega)
    have hd := facet_diagonal_count_one_pentagon P F R hR hother
    have hg := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
    rw [hF] at hg
    have hdQ : (facetDiagonalCount P F : ℚ) ≤ 9 := by exact_mod_cast (show (facetDiagonalCount P F : ℤ) ≤ 9 by omega)
    unfold rankSurplus
    rw [hF]
    norm_num only [Nat.cast_ofNat]
    linarith
  · push_neg at hquad
    have htri (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
        Nat.card (VerticesOn P S.val.val.carrier) = 3 := by
      have hlo := face_vertices_card_ge_dim_add_one P 2 S.val
      have hhi := hother S hSR
      have hne := hquad S hSR
      omega
    have hd := facet_diagonal_count_unique_polygon P F R htri
    have hdiag := polygon_nonedge_count P R.val
    rw [hR] at hdiag
    norm_num only [Nat.choose] at hdiag
    have hge := actual_polygon_card_le_relation_rank_add_three P e F R
    rw [hR] at hge
    have hrQ : (2 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 2 ≤ actualPolygonRelationRank P e F by omega)
    have hd5 : facetDiagonalCount P F = 5 := by omega
    unfold rankSurplus
    rw [hF, hd5]
    norm_num only [Nat.cast_ofNat]
    linarith

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/PolygonCompanionCounts.lean -/



@[expose] public section

/-!
# Companion polygons in an actual three-dimensional facet

Three different polygons in a three-dimensional polytope cannot contain the
same two vertices. Their intersection would be an edge with three incident
facets. Applied inside an eight-vertex facet, this gives at most two
quadrilateral companions of a hexagon. All incidences below are actual
exposed faces, not a supplied abstract boundary.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceRestriction Papers.PolytopeBoundaryIntersections

/-- The actual two-face intersection lemma with arbitrary vertex labels. -/
theorem actual_two_face_intersection_labels {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (R S : Face P 2) (hRS : R ≠ S) :
    (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val).card ≤ 1 ∨
      ∃ E : Face P 1, E.val.carrier ⊆ R.val.carrier ∧ E.val.carrier ⊆ S.val.carrier ∧
        actualFaceLabels P e E.val = actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val := by
  rcases two_face_intersection P R S hRS with hsmall | ⟨E, hER, hES, hE⟩
  · left
    have himage : (actualFaceLabels P e R.val ∩ actualFaceLabels P e S.val).image e =
        faceCode P 2 R ∩ faceCode P 2 S := by
      ext v
      simp only [Finset.mem_image, Finset.mem_inter, mem_actualFaceLabels,
        faceCode, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, ⟨hiR, hiS⟩, rfl⟩
        exact ⟨hiR, hiS⟩
      · intro h
        refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
        simpa using h
    rw [← himage, Finset.card_image_of_injective _ e.injective] at hsmall
    exact hsmall
  · right
    refine ⟨E, hER, hES, ?_⟩
    ext i
    have h : e i ∈ faceCode P 1 E ↔ e i ∈ faceCode P 2 R ∩ faceCode P 2 S := by rw [hE]
    simpa only [faceCode, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and, mem_actualFaceLabels] using h

/-- An actual edge inside a three-dimensional facet has exactly two polygon
cofaces there. The intrinsic face-polytope correspondence preserves carriers. -/
theorem actual_edge_polygon_cofaces_card {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (E : Face P 1)
    (hEF : E.val.carrier ⊆ F.val.carrier) :
    Nat.card {R : FaceBelow P F.val.carrier 2 // E.val.carrier ⊆ R.val.val.carrier} = 2 := by
  let Q := facePolytope P F.val.isFace
  let E' : Face Q 1 := faceBelowEquiv P F.val.isFace 1 ⟨E, hEF⟩
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  let f : {R : FaceBelow P F.val.carrier 2 // E.val.carrier ⊆ R.val.val.carrier} ≃
      Coface Q E'.val.carrier 2 :=
    { toFun R := ⟨faceBelowEquiv P F.val.isFace 2 R.val, R.property⟩
      invFun R := ⟨(faceBelowEquiv P F.val.isFace 2).symm R.val, R.property⟩
      left_inv R := by apply Subtype.ext; exact (faceBelowEquiv P F.val.isFace 2).symm_apply_apply R.val
      right_inv R := by apply Subtype.ext; exact (faceBelowEquiv P F.val.isFace 2).apply_symm_apply R.val }
  rw [Nat.card_congr f]
  exact ridge_coface_card Q 1 hQ E'

/-- Three distinct polygons of one actual facet share at most one vertex. -/
theorem actual_three_polygons_common_labels_card_le_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (R : Fin 3 → FaceBelow P F.val.carrier 2) (hR : Function.Injective R)
    (T : Finset (Fin n)) (hT : ∀ i, T ⊆ actualFaceLabels P e (R i).val.val) :
    T.card ≤ 1 := by
  by_contra hlarge
  have h01 : (R 0).val ≠ (R 1).val := by
    intro h
    have h' := hR (Subtype.ext h)
    exact (by decide : (0 : Fin 3) ≠ 1) h'
  have hTI : T ⊆ actualFaceLabels P e (R 0).val.val ∩ actualFaceLabels P e (R 1).val.val :=
    Finset.subset_inter (hT 0) (hT 1)
  rcases actual_two_face_intersection_labels P e (R 0).val (R 1).val h01 with
      hsmall | ⟨E, hE0, _, hEI⟩
  · have hc := Finset.card_le_card hTI
    omega
  have hTE : T ⊆ actualFaceLabels P e E.val := by rwa [hEI]
  have hEcard : (actualFaceLabels P e E.val).card = 2 := by
    rw [actualFaceLabels_card, one_face_vertex_card]
  have hTeq : T = actualFaceLabels P e E.val :=
    Finset.eq_of_subset_of_card_le hTE (by omega)
  have hER (i : Fin 3) : E.val.carrier ⊆ (R i).val.val.carrier := by
    apply (actualFaceLabels_subset_iff P e E.val (R i).val.val).mp
    rw [← hTeq]
    exact hT i
  have hEF : E.val.carrier ⊆ F.val.carrier := hE0.trans (R 0).property
  let f : Fin 3 → {S : FaceBelow P F.val.carrier 2 // E.val.carrier ⊆ S.val.val.carrier} :=
    fun i => ⟨R i, hER i⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hR (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
    actual_edge_polygon_cofaces_card P F E hEF] at hcard
  omega

/-- In an eight-vertex facet, a quadrilateral companion of a hexagon must
contain both vertices outside the hexagon. -/
theorem eight_facet_hexagon_outside_subset_quadrilateral {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hF : facetVertexCount P F = 8) (H Q : FaceBelow P F.val.carrier 2)
    (hH : Nat.card (VerticesOn P H.val.val.carrier) = 6)
    (hQ : Nat.card (VerticesOn P Q.val.val.carrier) = 4) :
    actualFaceLabels P e F.val \ actualFaceLabels P e H.val.val ⊆
      actualFaceLabels P e Q.val.val := by
  let T := actualFaceLabels P e F.val \ actualFaceLabels P e H.val.val
  have hHsub := actualFaceLabels_mono P e H.property
  have hT : T.card = 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hHsub
    rw [actualFaceLabels_card, actualFaceLabels_card] at h
    change T.card + _ = facetVertexCount P F at h
    rw [hH, hF] at h
    omega
  have hQH : Q.val ≠ H.val := by
    intro h
    rw [h] at hQ
    omega
  have hinter := actual_two_face_labels_inter_card_le_two P e Q.val H.val hQH
  have hdiff := Finset.card_inter_add_card_sdiff
    (actualFaceLabels P e Q.val.val) (actualFaceLabels P e H.val.val)
  rw [actualFaceLabels_card, hQ] at hdiff
  have hsub : actualFaceLabels P e Q.val.val \ actualFaceLabels P e H.val.val ⊆ T := by
    intro i hi
    obtain ⟨hiQ, hiH⟩ := Finset.mem_sdiff.mp hi
    exact Finset.mem_sdiff.mpr ⟨actualFaceLabels_mono P e Q.property hiQ, hiH⟩
  have heq : actualFaceLabels P e Q.val.val \ actualFaceLabels P e H.val.val = T :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  change T ⊆ actualFaceLabels P e Q.val.val
  rw [← heq]
  exact Finset.sdiff_subset

/-- The hexagon row of Appendix C.1: at most two quadrilateral companions. -/
theorem eight_facet_hexagon_quadrilateral_count_le_two {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hF : facetVertexCount P F = 8) (H : FaceBelow P F.val.carrier 2)
    (hH : Nat.card (VerticesOn P H.val.val.carrier) = 6) :
    (facetQuadrilateralFaces P F).card ≤ 2 := by
  by_contra hlarge
  obtain ⟨Q, hQ⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (show Fintype.card (Fin 3) ≤ (facetQuadrilateralFaces P F).card by
      rw [Fintype.card_fin]
      omega)
  let T := actualFaceLabels P e F.val \ actualFaceLabels P e H.val.val
  have hT : T.card = 2 := by
    have h := Finset.card_sdiff_add_card_eq_card (actualFaceLabels_mono P e H.property)
    rw [actualFaceLabels_card, actualFaceLabels_card] at h
    change T.card + _ = facetVertexCount P F at h
    rw [hH, hF] at h
    omega
  have hbound := actual_three_polygons_common_labels_card_le_one P e F Q Q.injective T
    (fun i => eight_facet_hexagon_outside_subset_quadrilateral P e F hF H (Q i) hH
      (Finset.mem_filter.mp (hQ ⟨i, rfl⟩)).2)
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/PentagonQuadrilateralRank.lean -/



@[expose] public section

/-!
# A pentagon with three quadrilateral companions forces rank four

The pentagon relation space has dimension two. If the complete polygon
relation span had dimension at most three, restriction to the coordinates
outside the pentagon would have dimension at most one. Every quadrilateral
row has at least two nonzero outside coordinates. Proportional nonzero rows
then have a common outside support of size at least two, contradicting the
actual two-polygons-per-edge property. In particular this proves the
pentagon-plus-four-quadrilateral rank bound required in Appendix C.1.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators

/-- Coordinate restriction outside a finite set, retained in the same
coefficient space by filling the deleted positions with zero. -/
def maskOutside {n : ℕ} (S : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := if i ∈ S then 0 else v i
  map_add' v w := by ext i; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : i ∈ S <;> simp [hi]

theorem maskOutside_support {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ℝ) :
    vectorSupport (maskOutside S v) = vectorSupport v \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [vectorSupport, maskOutside, hi]

theorem maskOutside_global_relation_zero {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    {v : Fin n → ℝ} (hv : v ∈ globalRelationSpace p S) : maskOutside S v = 0 := by
  have hs := ((mem_globalRelationSpace_iff p S v).mp hv).1
  ext i
  by_cases hi : i ∈ S <;> simp [maskOutside, hi, hs i]

/-- Rank-nullity with the entire chosen polygon relation space in the
kernel. No equality of kernels or hidden full-rank premise is needed. -/
theorem outside_polygon_rank_budget {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) (hS : S ∈ L) :
    finrank ℝ ((maskOutside S).domRestrict (polygonRelationSpan p L)).range +
      finrank ℝ (globalRelationSpace p S) ≤ finrank ℝ (polygonRelationSpan p L) := by
  let U := polygonRelationSpan p L
  let W := globalRelationSpace p S
  have hWU : W ≤ U := globalRelationSpace_le_polygonRelationSpan p hS
  have hker : W.comap U.subtype ≤ ((maskOutside S).domRestrict U).ker := by
    intro v hv
    exact maskOutside_global_relation_zero p S hv
  have hdim := Submodule.finrank_mono hker
  have hW : finrank ℝ (W.comap U.subtype) = finrank ℝ W :=
    (Submodule.comapSubtypeEquivOfLe hWU).finrank_eq
  rw [hW] at hdim
  have hnullity := ((maskOutside S).domRestrict U).finrank_range_add_finrank_ker
  change finrank ℝ ((maskOutside S).domRestrict U).range + finrank ℝ W ≤ finrank ℝ U
  omega

/-- Nonzero vectors in a line have exactly the same coordinate support. -/
theorem support_eq_of_rank_le_one {n : ℕ} (U : Submodule ℝ (Fin n → ℝ))
    (hdim : finrank ℝ U ≤ 1) {u v : Fin n → ℝ}
    (hu : u ∈ U) (hv : v ∈ U) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    vectorSupport u = vectorSupport v := by
  have hpos : 0 < finrank ℝ U := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have hdim1 : finrank ℝ U = 1 := by omega
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim1 hu hu0
  have hvspan : v ∈ Submodule.span ℝ ({u} : Set (Fin n → ℝ)) := by rwa [← hspan]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvspan
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact hv0 ha.symm
  rw [← ha]
  ext i
  simp [vectorSupport, Pi.smul_apply, smul_eq_mul, mul_ne_zero, ha0]

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus

/-- Every actual quadrilateral has a nonzero homogeneous relation with
exactly its four vertex labels as support. -/
theorem exists_actual_quadrilateral_full_support_row {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (R : Face P 2) (hR : Nat.card (VerticesOn P R.val.carrier) = 4) :
    ∃ v : Fin n → ℝ,
      v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val) ∧
        v ≠ 0 ∧ vectorSupport v = actualFaceLabels P e R.val := by
  have hsmall : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hdim := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e R.val)
  rw [actualFaceLabels_rank, R.property, actualFaceLabels_card, hR] at hdim
  have hne : globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨v, hv, hv0⟩ := (globalRelationSpace (vertexCoordinates P e)
    (actualFaceLabels P e R.val)).ne_bot_iff.mp hne
  refine ⟨v, hv, hv0, ?_⟩
  have hcard : (actualFaceLabels P e R.val).card = 4 :=
    (actualFaceLabels_card P e R.val).trans hR
  have hfull := four_relation_full_support (vertexCoordinates P e)
    (vertexCoordinates_small_independent P e hsmall) hcard hv hv0
  have hout := ((mem_globalRelationSpace_iff _ _ _).mp hv).1
  ext i
  rw [mem_vectorSupport]
  constructor
  · intro hi
    by_contra hiR
    exact hi (hout i hiR)
  · exact hfull i

/-- This slightly stronger form needs only three quadrilateral companions.
The paper's four-companion application follows by restricting the index set. -/
theorem actual_pentagon_three_quadrilateral_rank {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (H : FaceBelow P F.val.carrier 2)
    (hH : Nat.card (VerticesOn P H.val.val.carrier) = 5)
    (Q : Fin 3 → FaceBelow P F.val.carrier 2) (hQ : Function.Injective Q)
    (hQfour : ∀ i, Nat.card (VerticesOn P (Q i).val.val.carrier) = 4) :
    4 ≤ actualPolygonRelationRank P e F := by
  by_contra hlarge
  have hdim : actualPolygonRelationRank P e F ≤ 3 := by omega
  let p := vertexCoordinates P e
  let S := actualFaceLabels P e H.val.val
  let U := polygonRelationSpan p (polygonLabelsBelow P e F)
  let f := (maskOutside S).domRestrict U
  have hS : S ∈ polygonLabelsBelow P e F :=
    Finset.mem_image.mpr ⟨H, Finset.mem_univ _, rfl⟩
  have hW : finrank ℝ (globalRelationSpace p S) = 2 := by
    have h := globalRelationSpace_finrank p S
    have hr : subsetRank p S = 3 := by
      simpa only [p, S, H.val.property] using actualFaceLabels_rank P e H.val.val
    have hc : S.card = 5 := (actualFaceLabels_card P e H.val.val).trans hH
    rw [hr, hc] at h
    omega
  have hfRank : finrank ℝ f.range ≤ 1 := by
    have h := outside_polygon_rank_budget p (polygonLabelsBelow P e F) S hS
    rw [hW] at h
    change finrank ℝ f.range + 2 ≤ actualPolygonRelationRank P e F at h
    omega
  have hex (i : Fin 3) := exists_actual_quadrilateral_full_support_row P hP e
    (Q i).val (hQfour i)
  choose C hC hCne hCsupport using hex
  have hmem (i : Fin 3) : C i ∈ U := by
    apply globalRelationSpace_le_polygonRelationSpan p
      (Finset.mem_image.mpr ⟨Q i, Finset.mem_univ _, rfl⟩)
    exact hC i
  have houtcard (i : Fin 3) : 2 ≤ (vectorSupport (maskOutside S (C i))).card := by
    rw [maskOutside_support, hCsupport i]
    have hneq : (Q i).val ≠ H.val := by
      intro h
      have hi := hQfour i
      rw [h] at hi
      omega
    have hinter := actual_two_face_labels_inter_card_le_two P e (Q i).val H.val hneq
    have hc := Finset.card_inter_add_card_sdiff (actualFaceLabels P e (Q i).val.val) S
    rw [actualFaceLabels_card, hQfour i] at hc
    change (actualFaceLabels P e (Q i).val.val ∩ S).card ≤ 2 at hinter
    omega
  have houtne (i : Fin 3) : maskOutside S (C i) ≠ 0 := by
    intro h
    have hc := houtcard i
    rw [h] at hc
    simp [vectorSupport] at hc
  have hrange (i : Fin 3) : maskOutside S (C i) ∈ f.range :=
    ⟨⟨C i, hmem i⟩, rfl⟩
  let T := vectorSupport (maskOutside S (C 0))
  have hT : ∀ i, T ⊆ actualFaceLabels P e (Q i).val.val := by
    intro i
    have hs := support_eq_of_rank_le_one f.range hfRank (hrange 0) (hrange i)
      (houtne 0) (houtne i)
    change T = _ at hs
    rw [hs, maskOutside_support, hCsupport i]
    exact Finset.sdiff_subset
  have hbound := actual_three_polygons_common_labels_card_le_one P e F Q hQ T hT
  have hTcard : 2 ≤ T.card := houtcard 0
  omega

/-- Direct Appendix C.1 interface for at least four quadrilateral faces. -/
theorem actual_pentagon_four_quadrilateral_rank {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (H : FaceBelow P F.val.carrier 2)
    (hH : Nat.card (VerticesOn P H.val.val.carrier) = 5)
    (hquad : 4 ≤ (facetQuadrilateralFaces P F).card) :
    4 ≤ actualPolygonRelationRank P e F := by
  obtain ⟨Q, hQ⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (show Fintype.card (Fin 3) ≤ (facetQuadrilateralFaces P F).card by
      rw [Fintype.card_fin]
      omega)
  exact actual_pentagon_three_quadrilateral_rank P hP e F H hH Q Q.injective
    (fun i => (Finset.mem_filter.mp (hQ ⟨i, rfl⟩)).2)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/EightFacetSurplusCases.lean -/



@[expose] public section

/-!
# Eight-vertex facet surplus: all cases except the six-quadrilateral corner

The large-polygon cases are derived from actual face intersections and
relation ranks. The purely quadrilateral case is also settled whenever
polygon excess is at most five. The only remaining case is an eight-vertex
facet with six quadrilaterals, which is isolated explicitly for the local
corner-relation argument.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceNonedges Papers.PolytopeFaceRestriction

def facetPentagonalFaces {d : ℕ} (P : ConvexPolytope d) (F : Face P 3) :
    Finset (FaceBelow P F.val.carrier 2) :=
  Finset.univ.filter fun R => Nat.card (VerticesOn P R.val.val.carrier) = 5

/-- Inclusion-exclusion and the actual pair-intersection bound. -/
theorem actual_three_polygon_vertex_count_bound {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (R S T : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) (hRT : R ≠ T) (hST : S ≠ T) :
    Nat.card (VerticesOn P R.val.val.carrier) + Nat.card (VerticesOn P S.val.val.carrier) +
      Nat.card (VerticesOn P T.val.val.carrier) ≤ facetVertexCount P F + 6 := by
  let A := actualFaceLabels P e R.val.val
  let B := actualFaceLabels P e S.val.val
  let C := actualFaceLabels P e T.val.val
  have hAB := actual_two_face_labels_inter_card_le_two P e R.val S.val
    (fun h => hRS (Subtype.ext h))
  have hAC := actual_two_face_labels_inter_card_le_two P e R.val T.val
    (fun h => hRT (Subtype.ext h))
  have hBC := actual_two_face_labels_inter_card_le_two P e S.val T.val
    (fun h => hST (Subtype.ext h))
  change (A ∩ B).card ≤ 2 at hAB
  change (A ∩ C).card ≤ 2 at hAC
  change (B ∩ C).card ≤ 2 at hBC
  have hsub : (A ∪ B) ∪ C ⊆ actualFaceLabels P e F.val :=
    Finset.union_subset (Finset.union_subset (actualFaceLabels_mono P e R.property)
      (actualFaceLabels_mono P e S.property)) (actualFaceLabels_mono P e T.property)
  have hbig := Finset.card_le_card hsub
  have hfirst := Finset.card_union_add_card_inter A B
  have hsecond := Finset.card_union_add_card_inter (A ∪ B) C
  have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hlast := Finset.card_union_le (A ∩ C) (B ∩ C)
  rw [← hdistrib] at hlast
  have hA : A.card = Nat.card (VerticesOn P R.val.val.carrier) := actualFaceLabels_card P e _
  have hB : B.card = Nat.card (VerticesOn P S.val.val.carrier) := actualFaceLabels_card P e _
  have hC : C.card = Nat.card (VerticesOn P T.val.val.carrier) := actualFaceLabels_card P e _
  rw [actualFaceLabels_card] at hbig
  change _ ≤ facetVertexCount P F at hbig
  omega

/-- There are at most two pentagons in an eight-vertex facet. -/
theorem eight_facet_pentagon_count_le_two {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hF : facetVertexCount P F = 8) : (facetPentagonalFaces P F).card ≤ 2 := by
  by_contra hlarge
  obtain ⟨R, hR⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (show Fintype.card (Fin 3) ≤ (facetPentagonalFaces P F).card by
      rw [Fintype.card_fin]
      omega)
  have hcard (i : Fin 3) : Nat.card (VerticesOn P (R i).val.val.carrier) = 5 :=
    (Finset.mem_filter.mp (hR ⟨i, rfl⟩)).2
  have h := actual_three_polygon_vertex_count_bound P e F (R 0) (R 1) (R 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (R.injective h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (R.injective h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (R.injective h))
  rw [hcard, hcard, hcard, hF] at h
  omega

/-- Exact excess and diagonal counts when all polygons have at most five vertices. -/
theorem facet_counts_of_polygons_le_five {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3)
    (hmax : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5) :
    facetPolygonExcess P F = (facetQuadrilateralFaces P F).card +
        2 * (facetPentagonalFaces P F).card ∧
      (facetDiagonalCount P F : ℤ) = 2 * facetPolygonExcess P F +
        (facetPentagonalFaces P F).card := by
  have hcard (R : FaceBelow P F.val.carrier 2) :
      Nat.card (VerticesOn P R.val.val.carrier) = 3 ∨
      Nat.card (VerticesOn P R.val.val.carrier) = 4 ∨
      Nat.card (VerticesOn P R.val.val.carrier) = 5 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    have hhi := hmax R
    omega
  have hexcess (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3 =
        (if Nat.card (VerticesOn P R.val.val.carrier) = 4 then 1 else 0) +
        2 * (if Nat.card (VerticesOn P R.val.val.carrier) = 5 then 1 else 0) := by
    rcases hcard R with h | h | h <;> rw [h] <;> norm_num
  have hdiag (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) =
        2 * ((Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3) +
        if Nat.card (VerticesOn P R.val.val.carrier) = 5 then 1 else 0 := by
    have hc := polygon_nonedge_count P R.val
    rcases hcard R with h | h | h <;>
      rw [h] at hc ⊢ <;> norm_num [Nat.choose] at hc ⊢ <;> omega
  constructor
  · rw [facetPolygonExcess_eq_sum_faceBelow]
    simp_rw [hexcess]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [facetQuadrilateralFaces, facetPentagonalFaces]
  · rw [facetDiagonalCount_eq_sum_polygon_diagonals, facetPolygonExcess_eq_sum_faceBelow]
    simp_rw [hdiag]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [facetPentagonalFaces]

/-- Exact diagonal count for one hexagon and otherwise small polygons. -/
theorem facet_diagonal_count_one_hexagon {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (H : FaceBelow P F.val.carrier 2)
    (hH : Nat.card (VerticesOn P H.val.val.carrier) = 6)
    (hother : ∀ R : FaceBelow P F.val.carrier 2, R ≠ H →
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    (facetDiagonalCount P F : ℤ) = 9 + 2 * (facetQuadrilateralFaces P F).card := by
  have hpoint (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) =
        (if R = H then 9 else 0) +
        2 * (if Nat.card (VerticesOn P R.val.val.carrier) = 4 then 1 else 0) := by
    have hc := polygon_nonedge_count P R.val
    by_cases h : R = H
    · subst R
      rw [hH] at hc ⊢
      norm_num [Nat.choose] at hc ⊢
      omega
    · have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
      have hhi := hother R h
      have hcard : Nat.card (VerticesOn P R.val.val.carrier) = 3 ∨
          Nat.card (VerticesOn P R.val.val.carrier) = 4 := by omega
      rw [if_neg h]
      rcases hcard with hcard | hcard <;>
        rw [hcard] at hc ⊢ <;> norm_num [Nat.choose] at hc ⊢ <;> omega
  rw [facetDiagonalCount_eq_sum_polygon_diagonals]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [facetQuadrilateralFaces]

/-- Every eight-vertex facet that has a polygon with at least five vertices
satisfies the surplus bound three. All large-polygon cases are included. -/
theorem eight_facet_large_polygon_surplus_ge_three {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8)
    (hlarge : ∃ R : FaceBelow P F.val.carrier 2,
      5 ≤ Nat.card (VerticesOn P R.val.val.carrier)) :
    3 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  have hmax (R : FaceBelow P F.val.carrier 2) :
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 7 := by
    have h := polygon_card_lt_containing_facet P R.val F R.property
    rw [hF] at h
    omega
  have hpair (R S : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) :
      Nat.card (VerticesOn P R.val.val.carrier) +
        Nat.card (VerticesOn P S.val.val.carrier) ≤ 10 := by
    simpa only [hF] using actual_two_polygon_vertex_count_bound P e F R S hRS
  by_cases hseven : ∃ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) = 7
  · obtain ⟨R, hR⟩ := hseven
    have htri (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
        Nat.card (VerticesOn P S.val.val.carrier) = 3 := by
      have h := hpair S R hSR
      have hlo := face_vertices_card_ge_dim_add_one P 2 S.val
      rw [hR] at h
      omega
    have hd := facet_diagonal_count_unique_polygon P F R htri
    have hdiag := polygon_nonedge_count P R.val
    rw [hR] at hdiag
    norm_num only [Nat.choose] at hdiag
    have hge := actual_polygon_card_le_relation_rank_add_three P e F R
    rw [hR] at hge
    have hrQ : (4 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 4 ≤ actualPolygonRelationRank P e F by omega)
    have hd14 : facetDiagonalCount P F = 14 := by omega
    unfold rankSurplus
    rw [hF, hd14]
    norm_num only [Nat.cast_ofNat]
    linarith
  push_neg at hseven
  by_cases hsix : ∃ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) = 6
  · obtain ⟨R, hR⟩ := hsix
    have hother (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
        Nat.card (VerticesOn P S.val.val.carrier) ≤ 4 := by
      have h := hpair S R hSR
      rw [hR] at h
      omega
    have hq := eight_facet_hexagon_quadrilateral_count_le_two P e F hF R hR
    have hd := facet_diagonal_count_one_hexagon P F R hR hother
    by_cases hquad : (facetQuadrilateralFaces P F).Nonempty
    · obtain ⟨S, hS⟩ := hquad
      have hSfour := (Finset.mem_filter.mp hS).2
      have hRS : R ≠ S := by intro h; subst S; omega
      have hr := actual_distinct_polygon_relations_rank_add P hP e F R S hRS
      rw [hR, hSfour] at hr
      have hrQ : (4 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 4 ≤ actualPolygonRelationRank P e F by omega)
      have hdQ : (facetDiagonalCount P F : ℚ) ≤ 13 := by exact_mod_cast (show (facetDiagonalCount P F : ℤ) ≤ 13 by omega)
      unfold rankSurplus
      rw [hF]
      norm_num only [Nat.cast_ofNat]
      linarith
    · have hq0 : (facetQuadrilateralFaces P F).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hquad)
      rw [hq0] at hd
      have hge := actual_polygon_card_le_relation_rank_add_three P e F R
      rw [hR] at hge
      have hrQ : (3 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 3 ≤ actualPolygonRelationRank P e F by omega)
      have hd9 : facetDiagonalCount P F = 9 := by omega
      unfold rankSurplus
      rw [hF, hd9]
      norm_num only [Nat.cast_ofNat]
      linarith
  push_neg at hsix
  have hfive (R : FaceBelow P F.val.carrier 2) :
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5 := by
    have h := hmax R
    have h6 := hsix R
    have h7 := hseven R
    omega
  obtain ⟨R, hRlarge⟩ := hlarge
  have hR : Nat.card (VerticesOn P R.val.val.carrier) = 5 := by have h := hfive R; omega
  have hp := eight_facet_pentagon_count_le_two P e F hF
  obtain ⟨hgcount, hd⟩ := facet_counts_of_polygons_le_five P F hfive
  have hg := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hg
  by_cases hsecond : ∃ S : FaceBelow P F.val.carrier 2,
      S ≠ R ∧ Nat.card (VerticesOn P S.val.val.carrier) = 5
  · obtain ⟨S, hSR, hS⟩ := hsecond
    have hr := actual_distinct_polygon_relations_rank_add P hP e F R S hSR.symm
    rw [hR, hS] at hr
    have hrQ : (4 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 4 ≤ actualPolygonRelationRank P e F by omega)
    have hdQ : (facetDiagonalCount P F : ℚ) ≤ 14 := by exact_mod_cast (show (facetDiagonalCount P F : ℤ) ≤ 14 by omega)
    unfold rankSurplus
    rw [hF]
    norm_num only [Nat.cast_ofNat]
    linarith
  push_neg at hsecond
  have hpone : (facetPentagonalFaces P F).card = 1 := by
    have heq : facetPentagonalFaces P F = {R} := by
      ext S
      simp only [facetPentagonalFaces, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hS
        by_contra hSR
        exact hsecond S hSR hS
      · intro h
        subst S
        exact hR
    rw [heq, Finset.card_singleton]
  rw [hpone] at hd hgcount
  by_cases hquad4 : 4 ≤ (facetQuadrilateralFaces P F).card
  · have hr := actual_pentagon_four_quadrilateral_rank P hP e F R hR hquad4
    have hrQ : (4 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast hr
    have hdQ : (facetDiagonalCount P F : ℚ) ≤ 13 := by exact_mod_cast (show (facetDiagonalCount P F : ℤ) ≤ 13 by omega)
    unfold rankSurplus
    rw [hF]
    norm_num only [Nat.cast_ofNat]
    linarith
  by_cases hquad : (facetQuadrilateralFaces P F).Nonempty
  · obtain ⟨S, hS⟩ := hquad
    have hSfour := (Finset.mem_filter.mp hS).2
    have hRS : R ≠ S := by intro h; subst S; omega
    have hr := actual_distinct_polygon_relations_rank_add P hP e F R S hRS
    rw [hR, hSfour] at hr
    have hrQ : (3 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 3 ≤ actualPolygonRelationRank P e F by omega)
    have hdQ : (facetDiagonalCount P F : ℚ) ≤ 11 := by exact_mod_cast (show (facetDiagonalCount P F : ℤ) ≤ 11 by omega)
    unfold rankSurplus
    rw [hF]
    norm_num only [Nat.cast_ofNat]
    linarith
  · have hq0 : (facetQuadrilateralFaces P F).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hquad)
    rw [hq0] at hgcount
    have hr := actual_polygon_card_le_relation_rank_add_three P e F R
    rw [hR] at hr
    have hrQ : (2 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast (show 2 ≤ actualPolygonRelationRank P e F by omega)
    have hd5 : facetDiagonalCount P F = 5 := by omega
    unfold rankSurplus
    rw [hF, hd5]
    norm_num only [Nat.cast_ofNat]
    linarith

/-- The small-polygon case except the six-quadrilateral corner. -/
theorem eight_facet_small_polygon_surplus_ge_four_of_excess_le_five {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hg : facetPolygonExcess P F ≤ 5) :
    4 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  have hsmall : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hd := facet_diagonal_count_twice_polygon_excess P F hpolygons
  have hq := facetQuadrilateralFaces_card P F hpolygons
  have hdefect : facetPolygonExcess P F ≤ (actualPolygonRelationRank P e F : ℤ) + 2 := by
    by_cases hzero : actualPolygonRelationRank P e F = 0
    · have hz := actualPolygonRelationRank_zero P e F hzero
      rw [hz] at hd
      omega
    by_cases hone : actualPolygonRelationRank P e F = 1
    · have ho := actualPolygonRelationRank_one P e hsmall F hone
      rw [ho] at hd
      omega
    by_cases hfour : 4 ≤ (facetQuadrilateralFaces P F).card
    · have hr := actual_rank_ge_three_of_four_quadrilateral_faces P hP e F hfour
      omega
    · omega
  have hdQ : (facetDiagonalCount P F : ℚ) = 2 * (facetPolygonExcess P F : ℚ) := by exact_mod_cast hd
  have heQ : (facetPolygonExcess P F : ℚ) ≤ (actualPolygonRelationRank P e F : ℚ) + 2 := by exact_mod_cast hdefect
  unfold rankSurplus
  rw [hF]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Exhaustive actual reduction to the sole remaining local corner case.
This is a disjunction, not a claim that the corner case has been proved. -/
theorem eight_facet_surplus_or_six_quadrilaterals {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8) :
    3 ≤ rankSurplus P F (actualPolygonRelationRank P e F) ∨
      ((∀ R : FaceBelow P F.val.carrier 2,
          Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) ∧ facetPolygonExcess P F = 6) := by
  by_cases hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4
  · by_cases hg : facetPolygonExcess P F ≤ 5
    · left
      exact (show (3 : ℚ) ≤ 4 by norm_num).trans
        (eight_facet_small_polygon_surplus_ge_four_of_excess_le_five P hP e F hF hsmall hg)
    · right
      have hmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
      rw [hF] at hmax
      exact ⟨hsmall, by omega⟩
  · left
    push_neg at hsmall
    obtain ⟨R, hR⟩ := hsmall
    exact eight_facet_large_polygon_surplus_ge_three P hP e F hF ⟨R, by omega⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/EightFacetQuadrilateralRank.lean -/





@[expose] public section

/-!
# The rank-four relation space of the eight-vertex quadrilateral case

The Euler equality in this branch forces six quadrilateral faces. Choose
two faces on an edge. Their union has six vertices and their relation
spaces are independent lines. If the complete polygon relation space had
dimension at most three, restriction to the two omitted vertices would
have dimension at most one. Full support of the quadrilateral relations
would then force every polygon through either omitted vertex to contain
both. A vertex lies in at least three polygons, whereas three distinct
polygons of a three-polytope cannot share two vertices.

No classification of the cube graph, planar embedding theorem, or chosen
coordinate chart is assumed. 
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceRestriction Papers.PolytopeEulerThree
open Papers.PolytopeEulerRadialFigure Papers.PolytopeBalinski

local instance EightFacetQuadrilateralRankFaceFintype {d : ℕ} (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

local instance incidentFaceFintype {d : ℕ} (P : ConvexPolytope d)
    (v : E d) (k : ℕ) : Fintype (IncidentFace P v k) := Fintype.ofFinite _

/-- Rank-nullity with any known subspace killed by coordinate restriction. -/
theorem maskOutside_rank_budget {n : ℕ}
    (U W : Submodule ℝ (Fin n → ℝ)) (S : Finset (Fin n))
    (hWU : W ≤ U) (hzero : ∀ v ∈ W, maskOutside S v = 0) :
    finrank ℝ ((maskOutside S).domRestrict U).range + finrank ℝ W ≤ finrank ℝ U := by
  have hker : W.comap U.subtype ≤ ((maskOutside S).domRestrict U).ker := by
    intro v hv
    exact hzero v.val hv
  have hdim := Submodule.finrank_mono hker
  have hW : finrank ℝ (W.comap U.subtype) = finrank ℝ W :=
    (Submodule.comapSubtypeEquivOfLe hWU).finrank_eq
  rw [hW] at hdim
  have hnullity := ((maskOutside S).domRestrict U).finrank_range_add_finrank_ker
  omega

/-- Every vertex of an intrinsic three-polytope belongs to at least three
two-faces. This is the vertex/edge count of its actual polygonal figure. -/
theorem three_dimensional_vertex_polygon_count {d : ℕ}
    (Q : ConvexPolytope d) (hQ : Q.dim = 3) (v : Q.vertices) :
    3 ≤ Nat.card (IncidentFace Q v.val 2) := by
  have hpos : 1 ≤ faceDim Q.toSet := by change 1 ≤ Q.dim; omega
  let D : DatiFetta Q v.val := Classical.choice (esiste_datiFetta Q v.property hpos)
  have hD : D.politopo.dim = 2 := figure_dim_two D hQ
  have hv := vertices_card_ge_dim_add_one D.politopo
  rw [hD] at hv
  have he := polygon_vertices_eq_edges D.politopo hD
  have hi := Nat.card_congr (incidentFigureEquiv (toGaloisData D) 1)
  change Nat.card (IncidentFace Q v.val 2) = Nat.card (Face D.politopo 1) at hi
  have hc : Nat.card D.politopo.vertices = D.politopo.vertices.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

/-- The same incidence bound inside an actual three-dimensional face,
retaining the ambient vertex labels. -/
theorem actual_vertex_polygon_cofaces_ge_three {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (a : Fin n) (ha : a ∈ actualFaceLabels P e F.val) :
    3 ≤ Nat.card {R : FaceBelow P F.val.carrier 2 //
      a ∈ actualFaceLabels P e R.val.val} := by
  let Q := facePolytope P F.val.isFace
  let v : Q.vertices := ⟨(e a).val, Finset.mem_filter.mpr
    ⟨(e a).property, (mem_actualFaceLabels P e F.val a).mp ha⟩⟩
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  let f : {R : FaceBelow P F.val.carrier 2 // a ∈ actualFaceLabels P e R.val.val} ≃
      IncidentFace Q v.val 2 :=
    { toFun R := ⟨faceBelowEquiv P F.val.isFace 2 R.val,
        (mem_actualFaceLabels P e R.val.val.val a).mp R.property⟩
      invFun R := ⟨(faceBelowEquiv P F.val.isFace 2).symm R.val,
        (mem_actualFaceLabels P e _ a).mpr R.property⟩
      left_inv R := by
        apply Subtype.ext
        exact (faceBelowEquiv P F.val.isFace 2).symm_apply_apply R.val
      right_inv R := by
        apply Subtype.ext
        exact (faceBelowEquiv P F.val.isFace 2).apply_symm_apply R.val }
  rw [Nat.card_congr f]
  exact three_dimensional_vertex_polygon_count Q hQ v

/-- Euler forces twelve edges and six quadrilaterals, with no triangles,
in the remaining small-polygon branch. -/
theorem eight_facet_excess_six_quad_data {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3)
    (hF : facetVertexCount P F = 8)
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hg : facetPolygonExcess P F = 6) :
    Nat.card (FaceBelow P F.val.carrier 1) = 12 ∧
      ∀ R : FaceBelow P F.val.carrier 2,
        Nat.card (VerticesOn P R.val.val.carrier) = 4 := by
  have hE : Nat.card (FaceBelow P F.val.carrier 1) = 12 := by
    have h := facet_polygon_excess_formula P F
    rw [hF, hg] at h
    omega
  refine ⟨hE, ?_⟩
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have hV : Q.vertices.card = 8 := by
    have h := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
    change facetVertexCount P F = Nat.card Q.vertices at h
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, hF] using h.symm
  have hQE : Nat.card (Face Q 1) = 12 := by
    rw [← Nat.card_congr (faceBelowEquiv P F.val.isFace 1)]
    exact hE
  have hfaces : Nat.card (FaceBelow P F.val.carrier 2) = 6 := by
    have h := euler_three Q hQ
    rw [hV, hQE] at h
    have he := Nat.card_congr (faceBelowEquiv P F.val.isFace 2)
    change Nat.card (FaceBelow P F.val.carrier 2) = Nat.card (Face Q 2) at he
    omega
  have hquads : (facetQuadrilateralFaces P F).card = 6 := by
    have h := facetQuadrilateralFaces_card P F hsmall
    rw [hg] at h
    omega
  have hall : facetQuadrilateralFaces P F = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hfaces, hquads] using
      (Nat.le_refl 6)
  intro R
  have hm : R ∈ facetQuadrilateralFaces P F := by rw [hall]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hm).2

/-- The cube branch of Appendix C.1, with every geometric and counting
hypothesis derived from the stated actual-polytope data. -/
theorem eight_facet_six_quadrilaterals_rank_ge_four {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8)
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hg : facetPolygonExcess P F = 6) :
    4 ≤ actualPolygonRelationRank P e F := by
  obtain ⟨hedges, hquad⟩ := eight_facet_excess_six_quad_data P F hF hsmall hg
  obtain ⟨E⟩ : Nonempty (FaceBelow P F.val.carrier 1) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card (FaceBelow P F.val.carrier 1) by omega)).1
  let I := {R : FaceBelow P F.val.carrier 2 // E.val.val.carrier ⊆ R.val.val.carrier}
  have hI : Nat.card I = 2 := actual_edge_polygon_cofaces_card P F E.val E.property
  obtain ⟨j⟩ : Nonempty (Fin 2 ↪ I) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin] using hI.ge)
  let R : FaceBelow P F.val.carrier 2 := (j 0).val
  let S : FaceBelow P F.val.carrier 2 := (j 1).val
  have hRS : R ≠ S := by
    intro h
    have heq : j 0 = j 1 := Subtype.ext h
    exact (by decide : (0 : Fin 2) ≠ 1) (j.injective heq)
  have hRSval : R.val ≠ S.val := fun h => hRS (Subtype.ext h)
  let p := vertexCoordinates P e
  let A := actualFaceLabels P e R.val.val
  let B := actualFaceLabels P e S.val.val
  let K := A ∪ B
  let T := actualFaceLabels P e F.val \ K
  have hA : A.card = 4 := (actualFaceLabels_card P e R.val.val).trans (hquad R)
  have hB : B.card = 4 := (actualFaceLabels_card P e S.val.val).trans (hquad S)
  have hAB : (A ∩ B).card = 2 := by
    have hlo := Finset.card_le_card (Finset.subset_inter
      (actualFaceLabels_mono P e (j 0).property)
      (actualFaceLabels_mono P e (j 1).property))
    rw [actualFaceLabels_card, one_face_vertex_card] at hlo
    have hhi := actual_two_face_labels_inter_card_le_two P e R.val S.val hRSval
    change _ ≤ (A ∩ B).card at hlo
    change (A ∩ B).card ≤ 2 at hhi
    omega
  have hK : K.card = 6 := by
    have h := Finset.card_union_add_card_inter A B
    rw [hA, hB, hAB] at h
    change K.card + 2 = 4 + 4 at h
    omega
  have hKsub : K ⊆ actualFaceLabels P e F.val := Finset.union_subset
    (actualFaceLabels_mono P e R.property) (actualFaceLabels_mono P e S.property)
  have hT : T.card = 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hKsub
    rw [actualFaceLabels_card, hK] at h
    change T.card + 6 = facetVertexCount P F at h
    omega
  let U := polygonRelationSpan p (polygonLabelsBelow P e F)
  let W := globalRelationSpace p A ⊔ globalRelationSpace p B
  let f := (maskOutside K).domRestrict U
  have hRmem : A ∈ polygonLabelsBelow P e F :=
    Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩
  have hSmem : B ∈ polygonLabelsBelow P e F :=
    Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩
  have hWU : W ≤ U := sup_le
    (globalRelationSpace_le_polygonRelationSpan p hRmem)
    (globalRelationSpace_le_polygonRelationSpan p hSmem)
  have hWP : W ≤ globalRelationSpace p K := sup_le
    (globalRelationSpace_mono p Finset.subset_union_left)
    (globalRelationSpace_mono p Finset.subset_union_right)
  have hzero : ∀ v ∈ W, maskOutside K v = 0 :=
    fun v hv => maskOutside_global_relation_zero p K (hWP hv)
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hInf : globalRelationSpace p A ⊓ globalRelationSpace p B = ⊥ :=
    actual_distinct_polygon_relation_spaces_inf P e hPcard R.val S.val hRSval
  have hdim (Q : FaceBelow P F.val.carrier 2) :
      finrank ℝ (globalRelationSpace p (actualFaceLabels P e Q.val.val)) = 1 := by
    have h := globalRelationSpace_finrank (vertexCoordinates P e)
      (actualFaceLabels P e Q.val.val)
    rw [actualFaceLabels_rank, Q.val.property, actualFaceLabels_card, hquad Q] at h
    change finrank ℝ (globalRelationSpace p (actualFaceLabels P e Q.val.val)) + 3 = 4 at h
    omega
  have hW : finrank ℝ W = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (globalRelationSpace p A) (globalRelationSpace p B)
    rw [hInf, finrank_bot, add_zero] at h
    change finrank ℝ W = _ at h
    rw [hdim R, hdim S] at h
    exact h
  by_contra hrank
  have hU : finrank ℝ U ≤ 3 := by
    change actualPolygonRelationRank P e F ≤ 3
    omega
  have hf : finrank ℝ f.range ≤ 1 := by
    have h := maskOutside_rank_budget U W K hWU hzero
    rw [hW] at h
    change finrank ℝ f.range + 2 ≤ finrank ℝ U at h
    omega
  obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have haF := (Finset.mem_sdiff.mp ha).1
  have haK := (Finset.mem_sdiff.mp ha).2
  let J := {Q : FaceBelow P F.val.carrier 2 // a ∈ actualFaceLabels P e Q.val.val}
  have hJ : 3 ≤ Nat.card J := actual_vertex_polygon_cofaces_ge_three P e F a haF
  obtain ⟨q⟩ : Nonempty (Fin 3 ↪ J) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin] using hJ)
  let Q : Fin 3 → FaceBelow P F.val.carrier 2 := fun i => (q i).val
  have hQinj : Function.Injective Q := by
    intro i k h
    exact q.injective (Subtype.ext h)
  have hQa (i : Fin 3) : a ∈ actualFaceLabels P e (Q i).val.val := (q i).property
  choose C hC hCne hCsupport using fun i : Fin 3 =>
    exists_actual_quadrilateral_full_support_row P hP e (Q i).val (hquad (Q i))
  have hCmem (i : Fin 3) : C i ∈ U :=
    globalRelationSpace_le_polygonRelationSpan p
      (Finset.mem_image.mpr ⟨Q i, Finset.mem_univ _, rfl⟩) (hC i)
  have hCmask (i : Fin 3) : maskOutside K (C i) ≠ 0 := by
    have hCa : C i a ≠ 0 := by
      apply (mem_vectorSupport _ _).mp
      rw [hCsupport i]
      exact hQa i
    intro h
    have hh := congrFun h a
    exact hCa (by simpa [maskOutside, haK] using hh)
  have hCrange (i : Fin 3) : maskOutside K (C i) ∈ f.range :=
    ⟨⟨C i, hCmem i⟩, rfl⟩
  have hcontained (i : Fin 3) : T ⊆ actualFaceLabels P e (Q i).val.val := by
    intro b hb
    have hbF := (Finset.mem_sdiff.mp hb).1
    have hbK := (Finset.mem_sdiff.mp hb).2
    let Jb := {H : FaceBelow P F.val.carrier 2 // b ∈ actualFaceLabels P e H.val.val}
    have hJb : 3 ≤ Nat.card Jb := actual_vertex_polygon_cofaces_ge_three P e F b hbF
    obtain ⟨H⟩ : Nonempty Jb := (Nat.card_pos_iff.mp (show 0 < Nat.card Jb by omega)).1
    obtain ⟨v, hv, hv0, hsupport⟩ :=
      exists_actual_quadrilateral_full_support_row P hP e H.val.val (hquad H.val)
    have hvU : v ∈ U := globalRelationSpace_le_polygonRelationSpan p
      (Finset.mem_image.mpr ⟨H.val, Finset.mem_univ _, rfl⟩) hv
    have hvb : v b ≠ 0 := by
      apply (mem_vectorSupport _ _).mp
      rw [hsupport]
      exact H.property
    have hvbmask : maskOutside K v b ≠ 0 := by simpa [maskOutside, hbK] using hvb
    have hvmask : maskOutside K v ≠ 0 := fun h => hvbmask (congrFun h b)
    have hvrange : maskOutside K v ∈ f.range := ⟨⟨v, hvU⟩, rfl⟩
    have hs := support_eq_of_rank_le_one f.range hf (hCrange i) hvrange (hCmask i) hvmask
    have hbC : b ∈ vectorSupport (maskOutside K (C i)) := by
      rw [hs]
      exact (mem_vectorSupport _ _).mpr hvbmask
    rw [maskOutside_support, hCsupport i] at hbC
    exact (Finset.mem_sdiff.mp hbC).1
  have hbound := actual_three_polygons_common_labels_card_le_one P e F Q hQinj T hcontained
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/EightFacetSurplus.lean -/




@[expose] public section

/-!
# The complete actual eight-vertex facet surplus bound

The large-polygon cases and the Euler corner case are combined here.  The
stronger bound for facets with only triangles and quadrilaterals is retained
because it is needed in the extremal global excess case.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus

/-- Every actual eight-vertex facet whose polygons have at most four vertices
has surplus at least four. -/
theorem eight_facet_small_polygon_surplus_ge_four {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8)
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    4 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  by_cases hg : facetPolygonExcess P F ≤ 5
  · exact eight_facet_small_polygon_surplus_ge_four_of_excess_le_five
      P hP e F hF hsmall hg
  have hmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hmax
  have hg6 : facetPolygonExcess P F = 6 := by omega
  have hr := eight_facet_six_quadrilaterals_rank_ge_four P hP e F hF hsmall hg6
  have hd := facet_diagonal_count_twice_polygon_excess P F hsmall
  rw [hg6] at hd
  have hd12 : facetDiagonalCount P F = 12 := by omega
  have hrQ : (4 : ℚ) ≤ actualPolygonRelationRank P e F := by exact_mod_cast hr
  unfold rankSurplus
  rw [hF, hd12]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Appendix C.1: every actual eight-vertex facet has surplus at least three,
without a combinatorial-type or realization-chart hypothesis. -/
theorem eight_facet_surplus_ge_three {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 8) :
    3 ≤ rankSurplus P F (actualPolygonRelationRank P e F) := by
  rcases eight_facet_surplus_or_six_quadrilaterals P hP e F hF with h | ⟨hsmall, _⟩
  · exact h
  · exact (show (3 : ℚ) ≤ 4 by norm_num).trans
      (eight_facet_small_polygon_surplus_ge_four P hP e F hF hsmall)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/LargeFacetGlobalCounts.lean -/





@[expose] public section

/-!
# Actual global consequences of large facet surplus

All counts below are actual face counts and the constructed sparse relation
matrix count. The selected-facet lower bound on excess keeps the full
nonsimplicial count, and the surplus sums use the actual nonnegativity theorem.
No template classification or numeric budget is supplied as an assumption.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeMasterBudget Papers.PolytopeRelationBudget

/-- Each selected large facet contributes its excess beyond the one unit
already counted by being nonsimplicial. -/
theorem facetExcess_ge_nonsimplicial_add_selected {d : ℕ}
    (P : ConvexPolytope d) (S : Finset (Face P 3))
    (hS : S ⊆ nonsimplicialFacets P) :
    ((nonsimplicialFacets P).card : ℤ) +
      (∑ F ∈ S, ((facetVertexCount P F : ℤ) - 5)) ≤ facetExcess P := by
  let extra := fun F : Face P 3 =>
    if F ∈ nonsimplicialFacets P then (facetVertexCount P F : ℤ) - 5 else 0
  have hnonneg (F : Face P 3) : 0 ≤ extra F := by
    by_cases hF : F ∈ nonsimplicialFacets P
    · have hbig := (mem_nonsimplicialFacets P F).mp hF
      simp only [extra, if_pos hF]
      omega
    · simp only [extra, if_neg hF, le_refl]
  have hpoint (F : Face P 3) : (facetVertexCount P F : ℤ) - 4 =
      (if F ∈ nonsimplicialFacets P then 1 else 0) + extra F := by
    have hlo := face_vertices_card_ge_dim_add_one P 3 F
    by_cases hF : F ∈ nonsimplicialFacets P
    · simp only [extra, if_pos hF]
      ring
    · have hsmall := mt (mem_nonsimplicialFacets P F).mpr hF
      simp only [extra, if_neg hF, add_zero]
      change 4 ≤ facetVertexCount P F at hlo
      omega
  have hsum : facetExcess P = ((nonsimplicialFacets P).card : ℤ) +
      ∑ F : Face P 3, extra F := by
    change (∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4)) = _
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hle : (∑ F ∈ S, extra F) ≤ ∑ F : Face P 3, extra F :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun F _ _ => hnonneg F)
  have heq : (∑ F ∈ S, extra F) = ∑ F ∈ S, ((facetVertexCount P F : ℤ) - 5) := by
    apply Finset.sum_congr rfl
    intro F hF
    simp only [extra, if_pos (hS hF)]
  rw [heq] at hle
  linarith

theorem facetExcess_ge_nonsimplicial_add_single {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (hF : 5 ≤ facetVertexCount P F) :
    ((nonsimplicialFacets P).card : ℤ) + (facetVertexCount P F : ℤ) - 5 ≤ facetExcess P := by
  have h := facetExcess_ge_nonsimplicial_add_selected P {F} (by
    intro G hG
    have hGF : G = F := Finset.mem_singleton.mp hG
    subst G
    exact (mem_nonsimplicialFacets P F).mpr (by omega))
  simpa only [Finset.sum_singleton, add_sub_assoc] using h

theorem facetExcess_ge_nonsimplicial_add_pair {d : ℕ}
    (P : ConvexPolytope d) (F G : Face P 3) (hFG : F ≠ G)
    (hF : 5 ≤ facetVertexCount P F) (hG : 5 ≤ facetVertexCount P G) :
    ((nonsimplicialFacets P).card : ℤ) + (facetVertexCount P F : ℤ) +
      (facetVertexCount P G : ℤ) - 10 ≤ facetExcess P := by
  have h := facetExcess_ge_nonsimplicial_add_selected P {F, G} (by
    intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with hHF | hHG
    · subst H
      exact (mem_nonsimplicialFacets P F).mpr (by omega)
    · subst H
      exact (mem_nonsimplicialFacets P G).mpr (by omega))
  rw [Finset.sum_pair hFG] at h
  linarith

/-- Under the residual nonsimplicial bound, there are at least ten actual facets. -/
theorem actual_facet_count_ge_ten_of_nonsimplicial_count {d : ℕ}
    (P : ConvexPolytope d) (hN : 10 ≤ (nonsimplicialFacets P).card) :
    10 ≤ Nat.card (Face P 3) := by
  have h := Finset.card_le_card (Finset.subset_univ (nonsimplicialFacets P))
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hN.trans h

/-- The master inequality specialized to ten vertices, retaining the entire
sum of actual local surpluses. -/
theorem actual_ten_vertex_sparse_master_bound {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) :
    (Fintype.card (SparseSharedRowIndex P e) : ℚ) +
      (∑ F : Face P 3, rankSurplus P F (actualPolygonRelationRank P e F)) ≤
      35 - Nat.card (Face P 3) - (facetExcess P : ℚ) := by
  have h := (actual_polygon_relation_budget P hP e).2.2
  have hc : (sharedRelationCount P (actualPolygonRelationRank P e) : ℚ) =
      (Fintype.card (SparseSharedRowIndex P e) : ℚ) := by
    exact_mod_cast (sparseSharedRowIndex_card P e).symm
  rw [hc, hn] at h
  norm_num only [show Nat.choose 10 2 = 45 by decide, Nat.cast_ofNat] at h
  norm_num at h ⊢
  exact h

theorem actual_surplus_le_sum {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) :
    rankSurplus P F (actualPolygonRelationRank P e F) ≤
      ∑ G : Face P 3, rankSurplus P G (actualPolygonRelationRank P e G) := by
  exact Finset.single_le_sum
    (fun G _ => (actual_polygon_relation_budget P hP e).2.1 G) (Finset.mem_univ F)

/-- An eight-vertex facet forces at most eight selected rows.  At the smallest
possible total excess all other facets have at most five vertices, so every
polygon of the large facet has at most four vertices and its stronger surplus
bound applies. -/
theorem actual_eight_vertex_facet_at_most_eight_rows {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F : Face P 3) (hF : facetVertexCount P F = 8) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 8 := by
  have hm := actual_facet_count_ge_ten_of_nonsimplicial_count P hN
  have hmQ : (10 : ℚ) ≤ Nat.card (Face P 3) := by exact_mod_cast hm
  have hE := facetExcess_ge_nonsimplicial_add_single P F (by omega)
  rw [hF] at hE
  have hElow : (13 : ℚ) ≤ (facetExcess P : ℚ) := by
    exact_mod_cast (show (13 : ℤ) ≤ facetExcess P by omega)
  have hsum := actual_surplus_le_sum P hP e F
  have hbound := actual_ten_vertex_sparse_master_bound P hP e hn
  by_cases hEbig : (14 : ℤ) ≤ facetExcess P
  · have hEbigQ : (14 : ℚ) ≤ (facetExcess P : ℚ) := by exact_mod_cast hEbig
    have heta := eight_facet_surplus_ge_three P hP e F hF
    have hrows : (Fintype.card (SparseSharedRowIndex P e) : ℚ) ≤ 8 := by linarith
    exact_mod_cast hrows
  have hother : ∀ G : Face P 3, G ≠ F → facetVertexCount P G ≤ 5 := by
    intro G hGF
    by_contra hG
    have hpair := facetExcess_ge_nonsimplicial_add_pair P F G hGF.symm
      (by omega) (by omega)
    rw [hF] at hpair
    omega
  have hsmall := polygon_card_le_four_of_one_large_facet P hP F hother
  have heta := eight_facet_small_polygon_surplus_ge_four P hP e F hF (fun R => hsmall R.val)
  have hrows : (Fintype.card (SparseSharedRowIndex P e) : ℚ) ≤ 8 := by linarith
  exact_mod_cast hrows

/-- Two seven-vertex facets already force at most eight selected rows. -/
theorem actual_two_seven_vertex_facets_at_most_eight_rows {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F G : Face P 3) (hFG : F ≠ G)
    (hF : facetVertexCount P F = 7) (hG : facetVertexCount P G = 7) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 8 := by
  have hm := actual_facet_count_ge_ten_of_nonsimplicial_count P hN
  have hE := facetExcess_ge_nonsimplicial_add_pair P F G hFG (by omega) (by omega)
  rw [hF, hG] at hE
  have hElow : (14 : ℚ) ≤ (facetExcess P : ℚ) := by
    exact_mod_cast (show (14 : ℤ) ≤ facetExcess P by omega)
  have hmQ : (10 : ℚ) ≤ Nat.card (Face P 3) := by exact_mod_cast hm
  have hetaF := seven_facet_surplus_ge_three_halves P hP e F hF
  have hetaG := seven_facet_surplus_ge_three_halves P hP e G hG
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({F, G} : Finset (Face P 3)))
    (fun H _ _ => (actual_polygon_relation_budget P hP e).2.1 H)
  rw [Finset.sum_pair hFG] at hsum
  have hbound := actual_ten_vertex_sparse_master_bound P hP e hn
  have hrows : (Fintype.card (SparseSharedRowIndex P e) : ℚ) ≤ 8 := by linarith
  exact_mod_cast hrows

/-- One seven-vertex facet and three distinct six-vertex facets force at
most eight rows. The half-unit bound is rounded only after using integrality
of the constructed row count. -/
theorem actual_seven_and_three_six_facets_at_most_eight_rows {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (G : Fin 3 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ i, facetVertexCount P (G i) = 6) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 8 := by
  let S := (Finset.univ : Finset (Fin 3)).image G
  have hFS : F ∉ S := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have h := hGsix i
    rw [hi, hF] at h
    omega
  have hselected : insert F S ⊆ nonsimplicialFacets P := by
    intro H hH
    rcases Finset.mem_insert.mp hH with hHF | hHS
    · subst H
      exact (mem_nonsimplicialFacets P F).mpr (by omega)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hHS
      exact (mem_nonsimplicialFacets P (G i)).mpr (by rw [hGsix]; omega)
  have hsum : (∑ H ∈ insert F S, ((facetVertexCount P H : ℤ) - 5)) = 5 := by
    rw [Finset.sum_insert hFS, hF]
    change (7 : ℤ) - 5 + (∑ H ∈ Finset.univ.image G, ((facetVertexCount P H : ℤ) - 5)) = 5
    rw [Finset.sum_image]
    · simp [hGsix]
    · intro i _ j _ hij
      exact hG hij
  have hE := facetExcess_ge_nonsimplicial_add_selected P (insert F S) hselected
  rw [hsum] at hE
  have hElow : (15 : ℚ) ≤ (facetExcess P : ℚ) := by
    exact_mod_cast (show (15 : ℤ) ≤ facetExcess P by omega)
  have hm := actual_facet_count_ge_ten_of_nonsimplicial_count P hN
  have hmQ : (10 : ℚ) ≤ Nat.card (Face P 3) := by exact_mod_cast hm
  have heta := seven_facet_surplus_ge_three_halves P hP e F hF
  have htotal := actual_surplus_le_sum P hP e F
  have hbound := actual_ten_vertex_sparse_master_bound P hP e hn
  by_contra hlarge
  have hcQ : (9 : ℚ) ≤ Fintype.card (SparseSharedRowIndex P e) := by
    exact_mod_cast (show 9 ≤ Fintype.card (SparseSharedRowIndex P e) by omega)
  linarith

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/NineVertexFacetBound.lean -/




@[expose] public section

/-!
# A nine-vertex facet leaves at most eight nonsimplicial facets

For a ten-vertex polytope, every facet other than a nine-vertex facet contains
the unique outside vertex. Its intersection with the large facet determines
it completely. Nonsimplicial facets therefore inject into the nontriangular
polygons of the large facet. The polygon excess of a nine-vertex
three-polytope is at most seven.

This avoids any assumption about pyramid density or a classification of the
nine-vertex facet. 
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceRestriction Papers.IncidenceCoreGeometry Papers.PolytopeNonedgeAllocation

/-- Three labels of distinct actual extreme vertices force affine dimension
at least two in every set containing them. -/
theorem three_actual_labels_dimension {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (T : Finset (Fin n)) (hT : 3 ≤ T.card) (A : Set (E d))
    (hA : ∀ i ∈ T, (e i).val ∈ A) : 2 ≤ faceDim A := by
  let S := T.image (fun i => (e i).val)
  have hinj : Function.Injective (fun i : Fin n => (e i).val) :=
    Subtype.val_injective.comp e.injective
  apply three_vertices_dimension_of_subset P S
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (e i).property
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hA i hi
  · simpa only [S, Finset.card_image_of_injective _ hinj] using hT

/-- Distinct actual three-faces sharing three vertices meet in an actual
two-face. Both its carrier and its exact labelled vertex set are retained. -/
theorem actual_three_face_intersection_labels {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (F G : Face P 3) (hne : F ≠ G)
    (hthree : 3 ≤ (actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val).card) :
    ∃ R : Face P 2, R.val.carrier = F.val.carrier ∩ G.val.carrier ∧
      actualFaceLabels P e R.val =
        actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val := by
  let T := actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val
  have hT : T.Nonempty := Finset.card_pos.mp
    (lt_of_lt_of_le (by decide : 0 < 3) hthree)
  obtain ⟨i, hi⟩ := hT
  have hiI : (e i).val ∈ F.val.carrier ∩ G.val.carrier := by
    obtain ⟨hiF, hiG⟩ := Finset.mem_inter.mp hi
    exact ⟨(mem_actualFaceLabels P e F.val i).mp hiF,
      (mem_actualFaceLabels P e G.val i).mp hiG⟩
  have hI : P.IsFace (F.val.carrier ∩ G.val.carrier) :=
    ⟨F.val.isFace.1.inter G.val.isFace.1, ⟨(e i).val, hiI⟩⟩
  have hlo : 2 ≤ faceDim (F.val.carrier ∩ G.val.carrier) := by
    apply three_actual_labels_dimension P e T hthree
    intro j hj
    obtain ⟨hjF, hjG⟩ := Finset.mem_inter.mp hj
    exact ⟨(mem_actualFaceLabels P e F.val j).mp hjF,
      (mem_actualFaceLabels P e G.val j).mp hjG⟩
  have hproper : F.val.carrier ∩ G.val.carrier ⊂ F.val.carrier := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hback
    have hsub : F.val.carrier ⊆ G.val.carrier := fun x hx => (hback hx).2
    have heq := face_eq_of_subset_equal_dimension P F.val.isFace G.val.isFace hsub
      (F.property.trans G.property.symm)
    exact hne (Subtype.ext (PolytopeFace.ext heq))
  have hhi := faceDim_lt_of_ssubset P hI F.val.isFace hproper
  rw [F.property] at hhi
  let R : Face P 2 := ⟨⟨F.val.carrier ∩ G.val.carrier, hI⟩, by
    change faceDim (F.val.carrier ∩ G.val.carrier) = 2
    omega⟩
  refine ⟨R, rfl, ?_⟩
  ext j
  simp only [mem_actualFaceLabels, Finset.mem_inter]
  rfl

def facetNontriangularPolygons {d : ℕ} (P : ConvexPolytope d) (F : Face P 3) :
    Finset (FaceBelow P F.val.carrier 2) :=
  Finset.univ.filter fun R => 3 < Nat.card (VerticesOn P R.val.val.carrier)

/-- Each nontriangular polygon contributes at least one unit to the actual
polygon excess. -/
theorem facet_nontriangular_card_le_excess {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) :
    ((facetNontriangularPolygons P F).card : ℤ) ≤ facetPolygonExcess P F := by
  rw [facetPolygonExcess_eq_sum_faceBelow]
  have hpoint (R : FaceBelow P F.val.carrier 2) :
      (if R ∈ facetNontriangularPolygons P F then (1 : ℤ) else 0) ≤
        (Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    by_cases hR : R ∈ facetNontriangularPolygons P F
    · have hbig := (Finset.mem_filter.mp hR).2
      rw [if_pos hR]
      omega
    · rw [if_neg hR]
      omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun R _ => hpoint R)
  simpa using h

/-- A nine-vertex three-face has at most seven nontriangular polygons. -/
theorem nine_facet_nontriangular_card_le_seven {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (hF : facetVertexCount P F = 9) :
    (facetNontriangularPolygons P F).card ≤ 7 := by
  have hcount := facet_nontriangular_card_le_excess P F
  have hmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hmax
  omega

/-- Every nonsimplicial three-face other than the nine-vertex face is uniquely
determined by a nontriangular polygon in that face. -/
theorem nine_facet_nonsimplicial_injection {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (F : Face P 3) (hF : facetVertexCount P F = 9) :
    Nonempty ((nonsimplicialFacets P).erase F ↪ facetNontriangularPolygons P F) := by
  have hn' : n = 10 := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_coe, hn] using h
  let A := actualFaceLabels P e F.val
  have hA : A.card = 9 := (actualFaceLabels_card P e F.val).trans hF
  have houtcard : (Finset.univ \ A).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp only [Finset.card_univ, Fintype.card_fin, hn', hA] at h
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp houtcard
  have huA : u ∉ A := by
    have h : u ∈ Finset.univ \ A := by rw [hu]; exact Finset.mem_singleton_self _
    exact (Finset.mem_sdiff.mp h).2
  have hout (i : Fin n) (hi : i ∉ A) : i = u := by
    apply Finset.mem_singleton.mp
    rw [← hu]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
  let N := (nonsimplicialFacets P).erase F
  have hdata (G : N) : ∃ R : facetNontriangularPolygons P F,
      actualFaceLabels P e G.val.val = insert u (actualFaceLabels P e R.val.val.val) := by
    have hGF : G.val ≠ F := (Finset.mem_erase.mp G.property).1
    have hGlarge := (mem_nonsimplicialFacets P G.val).mp (Finset.mem_erase.mp G.property).2
    let B := actualFaceLabels P e G.val.val
    have huB : u ∈ B := by
      by_contra huB
      have hsub : B ⊆ A := by
        intro i hi
        by_contra hiA
        have hiu := hout i hiA
        exact huB (hiu ▸ hi)
      have hcarrier := (actualFaceLabels_subset_iff P e G.val.val F.val).mp hsub
      have heq := face_eq_of_subset_equal_dimension P G.val.val.isFace F.val.isFace hcarrier
        (G.val.property.trans F.property.symm)
      exact hGF (Subtype.ext (PolytopeFace.ext heq))
    have hB : B = insert u (B ∩ A) := by
      ext i
      constructor
      · intro hi
        by_cases hiA : i ∈ A
        · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hi, hiA⟩)
        · exact Finset.mem_insert.mpr (Or.inl (hout i hiA))
      · intro hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact huB
        · exact (Finset.mem_inter.mp hi).1
    have huc : u ∉ B ∩ A := fun h => huA (Finset.mem_inter.mp h).2
    have hinter : 4 ≤ (B ∩ A).card := by
      have hc := congrArg Finset.card hB
      rw [Finset.card_insert_of_notMem huc] at hc
      have hcB : B.card = facetVertexCount P G.val := actualFaceLabels_card P e G.val.val
      omega
    obtain ⟨R, hRcarrier, hRlabels⟩ := actual_three_face_intersection_labels P e G.val F hGF
      (by omega : 3 ≤ (B ∩ A).card)
    have hRF : R.val.carrier ⊆ F.val.carrier := by
      rw [hRcarrier]
      exact Set.inter_subset_right
    let RF : FaceBelow P F.val.carrier 2 := ⟨R, hRF⟩
    have hRbig : 3 < Nat.card (VerticesOn P R.val.carrier) := by
      have hc := actualFaceLabels_card P e R.val
      rw [hRlabels] at hc
      change (B ∩ A).card = Nat.card (VerticesOn P R.val.carrier) at hc
      omega
    refine ⟨⟨RF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hRbig⟩⟩, ?_⟩
    change B = insert u (actualFaceLabels P e R.val)
    rw [hRlabels]
    exact hB
  choose f hf using hdata
  refine ⟨⟨f, ?_⟩⟩
  intro G H hGH
  apply Subtype.ext
  apply Subtype.ext
  apply actualFaceLabels_injective P e
  rw [hf G, hf H, hGH]

/-- A ten-vertex polytope with a nine-vertex facet has at most eight
nonsimplicial facets. All facet and polygon counts are actual exposed-face
counts; no pyramid-realization theorem is assumed. -/
theorem actual_nine_vertex_facet_nonsimplicial_count_le_eight {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (F : Face P 3) (hF : facetVertexCount P F = 9) :
    (nonsimplicialFacets P).card ≤ 8 := by
  obtain ⟨f⟩ := nine_facet_nonsimplicial_injection P e hn F hF
  have hcard := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_coe] at hcard
  have hFmem : F ∈ nonsimplicialFacets P := (mem_nonsimplicialFacets P F).mpr (by omega)
  have herase := Finset.card_erase_add_one hFmem
  have hpoly := nine_facet_nontriangular_card_le_seven P F hF
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/TenVertexLargeFacetReduction.lean -/



@[expose] public section

/-!
# Actual residual facet-size partition before Appendix C.2

The already established local surplus bounds eliminate every facet with
eight or nine vertices, two seven-vertex facets, and a seven-vertex facet
with three six-vertex facets. The remaining exactly-two-six branch is kept
explicitly in the conclusion. This is not an assertion of the stronger
Appendix C.2 conclusion before its cross-edge argument has been proved.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus

def sixVertexFacets {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetVertexCount P F = 6

/-- An actual facet misses at least one actual vertex. -/
theorem actual_facet_vertex_count_lt_total {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) : facetVertexCount P F < P.vertices.card := by
  have hfacet : IsFacet P F.val.carrier := ⟨F.val.isFace, by rw [F.property]; exact hP.symm⟩
  have houtside : ∃ v : P.vertices, v.val ∉ F.val.carrier := by
    by_contra hnone
    push_neg at hnone
    have hPF : P.toSet ⊆ F.val.carrier := convexHull_min
      (fun x hx => hnone ⟨x, hx⟩)
      (F.val.isFace.1.convex (convex_convexHull ℝ _))
    exact hfacet.ne_toSet
      (Set.Subset.antisymm (face_subset_toSet P F.val.isFace) hPF)
  obtain ⟨v, hv⟩ := houtside
  have hi : e.symm v ∉ actualFaceLabels P e F.val := by
    intro h
    apply hv
    have h' := (mem_actualFaceLabels P e F.val (e.symm v)).mp h
    simpa only [e.apply_symm_apply] using h'
  have hc := Finset.card_le_card
    (Finset.subset_univ (insert (e.symm v) (actualFaceLabels P e F.val)))
  rw [Finset.card_insert_of_notMem hi, Finset.card_univ, Fintype.card_fin,
    actualFaceLabels_card] at hc
  have hn := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_coe] at hn
  change facetVertexCount P F + 1 ≤ n at hc
  omega

/-- In the actual residual problem, every facet has at most seven vertices. -/
theorem actual_ten_vertex_residual_facets_le_seven {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e)) :
    ∀ F : Face P 3, facetVertexCount P F ≤ 7 := by
  intro F
  have hlt := actual_facet_vertex_count_lt_total P hP e F
  rw [hn] at hlt
  by_contra hlarge
  have hcases : facetVertexCount P F = 8 ∨ facetVertexCount P F = 9 := by omega
  rcases hcases with hF | hF
  · have hrows := actual_eight_vertex_facet_at_most_eight_rows P hP e hn hN F hF
    omega
  · have hfacets := actual_nine_vertex_facet_nonsimplicial_count_le_eight P e hn F hF
    omega

/-- If the residual has a seven-vertex facet, it is unique, and at most two
other facets have six vertices. -/
theorem actual_ten_vertex_residual_unique_seven {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F : Face P 3) (hF : facetVertexCount P F = 7) :
    (∀ G : Face P 3, G ≠ F → facetVertexCount P G ≤ 6) ∧
      (sixVertexFacets P).card ≤ 2 := by
  have hmax := actual_ten_vertex_residual_facets_le_seven P hP e hn hN hc
  constructor
  · intro G hGF
    have hGmax := hmax G
    by_contra hGlarge
    have hG : facetVertexCount P G = 7 := by omega
    have hrows := actual_two_seven_vertex_facets_at_most_eight_rows
      P hP e hn hN F G hGF.symm hF hG
    omega
  · by_contra hmany
    obtain ⟨G, hG⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin 3) (show Fintype.card (Fin 3) ≤ (sixVertexFacets P).card by
        rw [Fintype.card_fin]
        omega)
    have hGsix (i : Fin 3) : facetVertexCount P (G i) = 6 :=
      (Finset.mem_filter.mp (hG ⟨i, rfl⟩)).2
    have hrows := actual_seven_and_three_six_facets_at_most_eight_rows
      P hP e hn hN F hF G G.injective hGsix
    omega

/-- The source-complete partition currently available before the remaining
exactly-two-six-facets argument. -/
theorem actual_ten_vertex_residual_large_facet_partition {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e)) :
    (∀ F : Face P 3, facetVertexCount P F ≤ 6) ∨
      ∃ F : Face P 3, facetVertexCount P F = 7 ∧
        (∀ G : Face P 3, G ≠ F → facetVertexCount P G ≤ 6) ∧
        (sixVertexFacets P).card ≤ 2 := by
  by_cases hsmall : ∀ F : Face P 3, facetVertexCount P F ≤ 6
  · exact Or.inl hsmall
  right
  push_neg at hsmall
  obtain ⟨F, hFlarge⟩ := hsmall
  have hmax := actual_ten_vertex_residual_facets_le_seven P hP e hn hN hc F
  have hF : facetVertexCount P F = 7 := by omega
  exact ⟨F, hF, actual_ten_vertex_residual_unique_seven P hP e hn hN hc F hF⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/SevenVertexFacetAdjacency.lean -/





@[expose] public section

/-!
# A seven-vertex facet has sufficiently many neighboring facets

In a ten-vertex four-polytope, a nonsimplicial facet which is not a ridge
neighbor of a seven-vertex facet must contain all three outside vertices.
Three distinct actual facets cannot share those three vertices: their
pairwise intersections would give the same ridge, which has exactly two
facet cofaces. There are therefore at most two nonsimplicial nonneighbors.
The ridge neighbors inject into the two-faces of the fixed facet.

Consequently its number of ridges is at least N-3, where N is the actual
number of nonsimplicial facets. No facet-template or adjacency certificate
is assumed. 
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus

local instance SevenVertexFacetAdjacencyFaceFintype {d : ℕ} (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

local instance SevenVertexFacetAdjacencyCofaceFintype {d : ℕ} (P : ConvexPolytope d)
    (A : Set (E d)) (k : ℕ) : Fintype (Coface P A k) := Fintype.ofFinite _

/-- Three distinct facets of an actual four-polytope share at most two
vertices. Three shared extreme vertices would determine a common ridge. -/
theorem actual_three_facets_common_labels_card_le_two {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Fin 3 → Face P 3) (hF : Function.Injective F)
    (T : Finset (Fin n)) (hT : ∀ i, T ⊆ actualFaceLabels P e (F i).val) :
    T.card ≤ 2 := by
  by_contra hlarge
  have h01 : F 0 ≠ F 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hF h)
  have h02 : F 0 ≠ F 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hF h)
  have hT01 := Finset.subset_inter (hT 0) (hT 1)
  have hT02 := Finset.subset_inter (hT 0) (hT 2)
  obtain ⟨R, hR, hRl⟩ := actual_three_face_intersection_labels P e (F 0) (F 1) h01
    (by have hc := Finset.card_le_card hT01; omega)
  obtain ⟨S, hS, hSl⟩ := actual_three_face_intersection_labels P e (F 0) (F 2) h02
    (by have hc := Finset.card_le_card hT02; omega)
  have hTR : T ⊆ actualFaceLabels P e R.val := by rwa [hRl]
  have hTS : T ⊆ actualFaceLabels P e S.val := by rwa [hSl]
  have hRS : R = S := by
    by_contra hne
    have hbound := actual_two_face_labels_inter_card_le_two P e R S hne
    have hcard := Finset.card_le_card (Finset.subset_inter hTR hTS)
    omega
  have hRF (i : Fin 3) : R.val.carrier ⊆ (F i).val.carrier := by
    fin_cases i
    · rw [hR]
      exact Set.inter_subset_left
    · rw [hR]
      exact Set.inter_subset_right
    · rw [hRS, hS]
      exact Set.inter_subset_right
  let f : Fin 3 → Coface P R.val.carrier 3 := fun i => ⟨F i, hRF i⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hF (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
    ridge_coface_card P 2 hP R] at hc
  omega

/-- A distinct facet is a ridge neighbor exactly when the intersection
contains at least three actual vertex labels. The dimension theorem in
`NineVertexFacetBound` supplies the actual common ridge. -/
def actualFacetNeighborSet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) : Finset (Face P 3) :=
  Finset.univ.filter fun G => G ≠ F ∧
    3 ≤ (actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val).card

theorem mem_actualFacetNeighborSet_iff {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F G : Face P 3) :
    G ∈ actualFacetNeighborSet P e F ↔ G ≠ F ∧
      ∃ R : Face P 2, R.val.carrier ⊆ F.val.carrier ∧ R.val.carrier ⊆ G.val.carrier := by
  simp only [actualFacetNeighborSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hcard⟩
    obtain ⟨R, hR, _⟩ := actual_three_face_intersection_labels P e F G hne.symm hcard
    refine ⟨hne, R, ?_, ?_⟩
    · rw [hR]
      exact Set.inter_subset_left
    · rw [hR]
      exact Set.inter_subset_right
  · rintro ⟨hne, R, hRF, hRG⟩
    refine ⟨hne, ?_⟩
    have hc := Finset.card_le_card (Finset.subset_inter
      (actualFaceLabels_mono P e hRF) (actualFaceLabels_mono P e hRG))
    rw [actualFaceLabels_card] at hc
    have hlo := face_vertices_card_ge_dim_add_one P 2 R
    omega

/-- Different ridge neighbors give different ridges, by the actual
two-coface diamond. In particular there are no more neighbors than ridges. -/
theorem actual_facet_neighbor_count_le_ridges {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) :
    (actualFacetNeighborSet P e F).card ≤ Nat.card (FaceBelow P F.val.carrier 2) := by
  have hex (G : actualFacetNeighborSet P e F) :
      ∃ R : Face P 2, R.val.carrier = F.val.carrier ∩ G.val.val.carrier ∧
        actualFaceLabels P e R.val =
          actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val.val := by
    have hG := (Finset.mem_filter.mp G.property).2
    exact actual_three_face_intersection_labels P e F G.val hG.1.symm hG.2
  choose R hR hRl using hex
  let f : actualFacetNeighborSet P e F → FaceBelow P F.val.carrier 2 :=
    fun G => ⟨R G, by rw [hR G]; exact Set.inter_subset_left⟩
  have hf : Function.Injective f := by
    intro G H heq
    apply Subtype.ext
    by_contra hGH
    have hGF : G.val ≠ F := (Finset.mem_filter.mp G.property).2.1
    have hHF : H.val ≠ F := (Finset.mem_filter.mp H.property).2.1
    have hRsame : R G = R H := congrArg Subtype.val heq
    let K : Fin 3 → Face P 3 := ![F, G.val, H.val]
    have hK : Function.Injective K := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [K, eq_comm]
    have hsubset (i : Fin 3) :
        actualFaceLabels P e (R G).val ⊆ actualFaceLabels P e (K i).val := by
      apply actualFaceLabels_mono P e
      fin_cases i
      · change (R G).val.carrier ⊆ F.val.carrier
        rw [hR G]
        exact Set.inter_subset_left
      · change (R G).val.carrier ⊆ G.val.val.carrier
        rw [hR G]
        exact Set.inter_subset_right
      · change (R G).val.carrier ⊆ H.val.val.carrier
        rw [hRsame, hR H]
        exact Set.inter_subset_right
    have hbound := actual_three_facets_common_labels_card_le_two P hP e K hK
      (actualFaceLabels P e (R G).val) hsubset
    rw [actualFaceLabels_card] at hbound
    have hlo := face_vertices_card_ge_dim_add_one P 2 (R G)
    omega
  have h := Fintype.card_le_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

def actualNonsimplicialNonneighbors {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) : Finset (Face P 3) :=
  (nonsimplicialFacets P).filter fun G => G ≠ F ∧ G ∉ actualFacetNeighborSet P e F

theorem seven_vertex_facet_outside_card {n : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices) (hn : P.vertices.card = 10)
    (F : Face P 3) (hF : facetVertexCount P F = 7) :
    ((Finset.univ : Finset (Fin n)) \ actualFaceLabels P e F.val).card = 3 := by
  have hn' : n = 10 := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_coe, hn] using h
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (actualFaceLabels P e F.val))
  rw [actualFaceLabels_card, Finset.card_univ, Fintype.card_fin] at h
  change (Finset.univ \ actualFaceLabels P e F.val).card + facetVertexCount P F = n at h
  omega

/-- A nonsimplicial nonneighbor must use all three outside vertices. -/
theorem seven_vertex_facet_outside_subset_nonneighbor {n : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices) (hn : P.vertices.card = 10)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (G : Face P 3) (hG : G ∈ actualNonsimplicialNonneighbors P e F) :
    (Finset.univ : Finset (Fin n)) \ actualFaceLabels P e F.val ⊆
      actualFaceLabels P e G.val := by
  have hdata := Finset.mem_filter.mp hG
  have hGbig := (mem_nonsimplicialFacets P G).mp hdata.1
  have hsmall : (actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val).card ≤ 2 := by
    by_contra h
    apply hdata.2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdata.2.1, by omega⟩
  let T := (Finset.univ : Finset (Fin n)) \ actualFaceLabels P e F.val
  let U := actualFaceLabels P e G.val \ actualFaceLabels P e F.val
  have hT : T.card = 3 := seven_vertex_facet_outside_card P e hn F hF
  have hUT : U ⊆ T := Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
  have hsum := Finset.card_inter_add_card_sdiff
    (actualFaceLabels P e G.val) (actualFaceLabels P e F.val)
  rw [Finset.inter_comm, actualFaceLabels_card] at hsum
  change _ + U.card = facetVertexCount P G at hsum
  have hU : T.card ≤ U.card := by omega
  have hEq : U = T := Finset.eq_of_subset_of_card_le hUT hU
  change T ⊆ actualFaceLabels P e G.val
  rw [← hEq]
  exact Finset.sdiff_subset

theorem seven_vertex_facet_nonsimplicial_nonneighbors_le_two {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (F : Face P 3) (hF : facetVertexCount P F = 7) :
    (actualNonsimplicialNonneighbors P e F).card ≤ 2 := by
  by_contra hlarge
  obtain ⟨G, hG⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := actualNonsimplicialNonneighbors P e F) (by
      rw [Fintype.card_fin]
      omega)
  let T := (Finset.univ : Finset (Fin n)) \ actualFaceLabels P e F.val
  have hT : T.card = 3 := seven_vertex_facet_outside_card P e hn F hF
  have hsub (i : Fin 3) : T ⊆ actualFaceLabels P e (G i).val :=
    seven_vertex_facet_outside_subset_nonneighbor P e hn F hF (G i) (hG ⟨i, rfl⟩)
  have hbound := actual_three_facets_common_labels_card_le_two P hP e G G.injective T hsub
  omega

/-- The fixed facet, its ridge neighbors, and at most two nonneighbors
account for every nonsimplicial facet. -/
theorem seven_vertex_facet_nonsimplicial_count_le_ridges_add_three {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (F : Face P 3) (hF : facetVertexCount P F = 7) :
    (nonsimplicialFacets P).card ≤ Nat.card (FaceBelow P F.val.carrier 2) + 3 := by
  let A := actualFacetNeighborSet P e F
  let B := actualNonsimplicialNonneighbors P e F
  have hcover : nonsimplicialFacets P ⊆ insert F (A ∪ B) := by
    intro G hG
    by_cases hGF : G = F
    · exact Finset.mem_insert.mpr (Or.inl hGF)
    · apply Finset.mem_insert_of_mem
      by_cases hGA : G ∈ A
      · exact Finset.mem_union_left _ hGA
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hG, hGF, hGA⟩)
  have hcard := Finset.card_le_card hcover
  have hinsert := Finset.card_insert_le F (A ∪ B)
  have hunion := Finset.card_union_le A B
  have hA := actual_facet_neighbor_count_le_ridges P hP e F
  have hB := seven_vertex_facet_nonsimplicial_nonneighbors_le_two P hP e hn F hF
  change A.card ≤ _ at hA
  change B.card ≤ 2 at hB
  omega

theorem seven_vertex_facet_ridge_count_ge_nonsimplicial_sub_three {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (F : Face P 3) (hF : facetVertexCount P F = 7) :
    (nonsimplicialFacets P).card - 3 ≤ Nat.card (FaceBelow P F.val.carrier 2) := by
  have h := seven_vertex_facet_nonsimplicial_count_le_ridges_add_three P hP e hn F hF
  omega

theorem seven_vertex_facet_has_at_least_seven_ridges {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F : Face P 3) (hF : facetVertexCount P F = 7) :
    7 ≤ Nat.card (FaceBelow P F.val.carrier 2) := by
  have h := seven_vertex_facet_nonsimplicial_count_le_ridges_add_three P hP e hn F hF
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/SevenFacetRelationExcess.lean -/




@[expose] public section

/-!
# The finite signature of the seven-vertex excess-one case

With at least seven polygon faces, a seven-vertex facet has polygon excess
at most three. If all polygons are triangles or quadrilaterals, local
relation excess one therefore forces exactly three quadrilaterals and
relation rank two. The rank-two support argument shows that these three
quadrilaterals use exactly six vertices. This is the finite signature that
singles out the capped-prism template; the normalized catalogue check is
kept separate from this actual-geometric statement.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators

/-- Three four-supported rows in a plane, with proper pair intersections,
use exactly six columns. -/
theorem three_four_support_rows_rank_two_used_columns {n : ℕ}
    (C : Fin 3 → Fin n → ℝ)
    (hfour : ∀ i, (vectorSupport (C i)).card = 4)
    (hinter : ∀ i j, i ≠ j →
      (vectorSupport (C i) ∩ vectorSupport (C j)).card ≤ 2)
    (hdim : finrank ℝ (Submodule.span ℝ (Set.range C)) ≤ 2) :
    (activeColumns C).card = 6 := by
  have hnonzero (i : Fin 3) : C i ≠ 0 := by
    intro h
    have hc := hfour i
    rw [h] at hc
    simp [vectorSupport] at hc
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      LinearIndependent ℝ (![C i, C j] : Fin 2 → Fin n → ℝ) := by
    rw [linearIndependent_fin2]
    constructor
    · simpa using hnonzero j
    · intro a heq
      have hex : ∃ k, k ∈ vectorSupport (C i) ∧ k ∉ vectorSupport (C j) := by
        by_contra h
        push_neg at h
        have hb := hinter i j hij
        rw [Finset.inter_eq_left.mpr h, hfour i] at hb
        omega
      obtain ⟨k, hki, hkj⟩ := hex
      have hi : C i k ≠ 0 := (mem_vectorSupport _ _).mp hki
      have hj : C j k = 0 := by simpa using hkj
      have hh := congrFun heq k
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
        smul_eq_mul, hj, mul_zero] at hh
      exact hi hh.symm
  have hspan (i j : Fin 3) (hij : i ≠ j) :
      Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) =
        Submodule.span ℝ (Set.range C) := by
    have hle : Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) ≤
        Submodule.span ℝ (Set.range C) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.subset_span ⟨j, rfl⟩
    have htwo : finrank ℝ
        (Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ))) = 2 := by
      simpa using finrank_span_eq_card (hpair i j hij)
    have hlow := Submodule.finrank_mono hle
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hcolumn (k : Fin n) (hk : k ∈ activeColumns C) :
      2 ≤ (columnSupport C k).card := by
    by_contra hsmall
    let Z := (Finset.univ : Finset (Fin 3)) \ columnSupport C k
    have hc : Z.card + (columnSupport C k).card = 3 := by
      simpa only [Z, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (columnSupport C k))
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < Z.card by omega)
    have hi0 : C i k = 0 := by
      have h := (Finset.mem_sdiff.mp hi).2
      simpa [columnSupport] using h
    have hj0 : C j k = 0 := by
      have h := (Finset.mem_sdiff.mp hj).2
      simpa [columnSupport] using h
    have hker : Submodule.span ℝ (Set.range (![C i, C j] : Fin 2 → Fin n → ℝ)) ≤
        (LinearMap.proj k : (Fin n → ℝ) →ₗ[ℝ] ℝ).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact hi0
      · exact hj0
    rw [hspan i j hij] at hker
    obtain ⟨a, ha⟩ := (mem_activeColumns C k).mp hk
    exact ha (hker (Submodule.subset_span ⟨a, rfl⟩))
  have hentries : 2 * (activeColumns C).card ≤ 12 := by
    have hcount : 2 * (activeColumns C).card ≤ totalNonzeros C := by
      rw [totalNonzeros_eq_sum_columns]
      calc
        2 * (activeColumns C).card = ∑ _k ∈ activeColumns C, 2 := by simp [mul_comm]
        _ ≤ ∑ k ∈ activeColumns C, (columnSupport C k).card := Finset.sum_le_sum hcolumn
        _ ≤ ∑ k, (columnSupport C k).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
    have hn : totalNonzeros C = 12 := by simp [totalNonzeros, hfour]
    simpa only [hn] using hcount
  have hused : 6 ≤ (activeColumns C).card := by
    have hsub : vectorSupport (C 0) ∪ vectorSupport (C 1) ⊆ activeColumns C := by
      intro k hk
      apply (mem_activeColumns C k).mpr
      rcases Finset.mem_union.mp hk with h | h
      · exact ⟨0, (mem_vectorSupport _ _).mp h⟩
      · exact ⟨1, (mem_vectorSupport _ _).mp h⟩
    have hc := Finset.card_union_add_card_inter (vectorSupport (C 0)) (vectorSupport (C 1))
    rw [hfour, hfour] at hc
    have hi := hinter 0 1 (by decide)
    have hle := Finset.card_le_card hsub
    omega
  omega

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceRestriction Papers.PolytopeEulerThree

/-- Euler expresses polygon excess directly in terms of vertex and polygon
counts of the actual facet. -/
theorem facet_polygon_excess_face_formula {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) :
    facetPolygonExcess P F =
      2 * (facetVertexCount P F : ℤ) - Nat.card (FaceBelow P F.val.carrier 2) - 4 := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have hv : Q.vertices.card = facetVertexCount P F := by
    have h := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
    change facetVertexCount P F = Nat.card Q.vertices at h
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h.symm
  have he := Nat.card_congr (faceBelowEquiv P F.val.isFace 1)
  have hf := Nat.card_congr (faceBelowEquiv P F.val.isFace 2)
  have hEuler := euler_three Q hQ
  rw [hv, ← he, ← hf] at hEuler
  have hformula := facet_polygon_excess_formula P F
  omega

/-- With the actual adjacency lower bound on polygon faces, local excess one
forces exactly three quadrilaterals and relation rank two. -/
theorem seven_facet_excess_one_three_quads_rank_two {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2))
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hexcess : facetPolygonExcess P F - (actualPolygonRelationRank P e F : ℤ) = 1) :
    (facetQuadrilateralFaces P F).card = 3 ∧ actualPolygonRelationRank P e F = 2 := by
  have hmax := facet_polygon_excess_face_formula P F
  rw [hF] at hmax
  have hg : facetPolygonExcess P F ≤ 3 := by omega
  have hquad := facetQuadrilateralFaces_card P F hsmall
  have hdiag := facet_diagonal_count_twice_polygon_excess P F hsmall
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hz : actualPolygonRelationRank P e F ≠ 0 := by
    intro h
    have hd := actualPolygonRelationRank_zero P e F h
    rw [hd] at hdiag
    omega
  have ho : actualPolygonRelationRank P e F ≠ 1 := by
    intro h
    have hd := actualPolygonRelationRank_one P e hPcard F h
    rw [hd] at hdiag
    omega
  omega

def facetQuadrilateralLabels {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) : Finset (Fin n) :=
  (facetQuadrilateralFaces P F).biUnion fun R => actualFaceLabels P e R.val.val

/-- The actual equality branch has the exact finite capped-prism signature:
three quadrilateral faces with a six-vertex union. The catalogue identification
itself is a separate finite lemma. -/
theorem seven_facet_excess_one_quad_signature {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2))
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hexcess : facetPolygonExcess P F - (actualPolygonRelationRank P e F : ℤ) = 1) :
    (facetQuadrilateralFaces P F).card = 3 ∧
      (facetQuadrilateralLabels P e F).card = 6 := by
  obtain ⟨hqcard, hrank⟩ := seven_facet_excess_one_three_quads_rank_two
    P hP e F hF hfaces hsmall hexcess
  obtain ⟨q, hq⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (show Fintype.card (Fin 3) ≤ (facetQuadrilateralFaces P F).card by
      simp only [Fintype.card_fin, hqcard, le_refl])
  have hqfour (i : Fin 3) : Nat.card (VerticesOn P (q i).val.val.carrier) = 4 :=
    (Finset.mem_filter.mp (hq ⟨i, rfl⟩)).2
  have himage : Finset.univ.image q = facetQuadrilateralFaces P F := by
    apply Finset.eq_of_subset_of_card_le
    · intro R hR
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hR
      exact hq ⟨i, rfl⟩
    · rw [Finset.card_image_of_injective _ q.injective, Finset.card_univ,
        Fintype.card_fin, hqcard]
  choose C hC hCne hCsupport using fun i : Fin 3 =>
    exists_actual_quadrilateral_full_support_row P hP e (q i).val (hqfour i)
  have hCfour (i : Fin 3) : (vectorSupport (C i)).card = 4 := by
    rw [hCsupport, actualFaceLabels_card, hqfour]
  have hCinter (i j : Fin 3) (hij : i ≠ j) :
      (vectorSupport (C i) ∩ vectorSupport (C j)).card ≤ 2 := by
    rw [hCsupport, hCsupport]
    apply actual_two_face_labels_inter_card_le_two P e
    intro h
    exact hij (q.injective (Subtype.ext h))
  have hCspan : Submodule.span ℝ (Set.range C) ≤
      polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
      (Finset.mem_image.mpr ⟨q i, Finset.mem_univ _, rfl⟩) (hC i)
  have hCdim : finrank ℝ (Submodule.span ℝ (Set.range C)) ≤ 2 := by
    have h := Submodule.finrank_mono hCspan
    change _ ≤ actualPolygonRelationRank P e F at h
    rwa [hrank] at h
  have hused := three_four_support_rows_rank_two_used_columns C hCfour hCinter hCdim
  have hlabels : activeColumns C = facetQuadrilateralLabels P e F := by
    ext i
    simp only [activeColumns, Finset.mem_filter, Finset.mem_univ, true_and,
      facetQuadrilateralLabels, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨q j, hq ⟨j, rfl⟩, ?_⟩
      rw [← hCsupport j]
      exact (mem_vectorSupport _ _).mpr hj
    · rintro ⟨R, hR, hi⟩
      rw [← himage] at hR
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hR
      refine ⟨j, ?_⟩
      apply (mem_vectorSupport _ _).mp
      rwa [hCsupport j]
  exact ⟨hqcard, hlabels ▸ hused⟩

/-- In the ten-vertex residual, the polygon-face hypothesis of the preceding
signature theorem follows from actual facet adjacency. -/
theorem actual_seven_facet_excess_one_quad_signature {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hsmall : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hexcess : facetPolygonExcess P F - (actualPolygonRelationRank P e F : ℤ) = 1) :
    (facetQuadrilateralFaces P F).card = 3 ∧
      (facetQuadrilateralLabels P e F).card = 6 :=
  seven_facet_excess_one_quad_signature P hP e F hF
    (seven_vertex_facet_has_at_least_seven_ridges P hP e hn hN F hF) hsmall hexcess

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/SevenTwoSixFacetBudget.lean -/




@[expose] public section

/-!
# The exact residual budget with one seven- and two six-vertex facets

The actual selected-facet excess and surplus sums force ten facets, total
facet excess fourteen, ten nonsimplicial facets, nine selected relation
rows, and total local surplus at most two. These conclusions are derived
from actual faces and row counts; no finite boundary budget is assumed.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeMasterBudget Papers.PolytopeRelationBudget

theorem actual_seven_and_two_six_excess_lower_bound {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) (hF : facetVertexCount P F = 7)
    (G : Fin 2 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ i, facetVertexCount P (G i) = 6) :
    ((nonsimplicialFacets P).card : ℤ) + 4 ≤ facetExcess P := by
  let S := (Finset.univ : Finset (Fin 2)).image G
  have hFS : F ∉ S := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have h := hGsix i
    rw [hi, hF] at h
    omega
  have hselected : insert F S ⊆ nonsimplicialFacets P := by
    intro H hH
    rcases Finset.mem_insert.mp hH with hHF | hHS
    · subst H
      exact (mem_nonsimplicialFacets P F).mpr (by omega)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hHS
      exact (mem_nonsimplicialFacets P (G i)).mpr (by rw [hGsix]; omega)
  have hsum : (∑ H ∈ insert F S, ((facetVertexCount P H : ℤ) - 5)) = 4 := by
    rw [Finset.sum_insert hFS, hF]
    change (7 : ℤ) - 5 +
      (∑ H ∈ Finset.univ.image G, ((facetVertexCount P H : ℤ) - 5)) = 4
    rw [Finset.sum_image]
    · simp [hGsix]
    · intro i _ j _ hij
      exact hG hij
  have h := facetExcess_ge_nonsimplicial_add_selected P (insert F S) hselected
  rwa [hsum] at h

/-- The unique numeric corner that remains before the Appendix C.2
pentagon/prism and cross-edge arguments. -/
theorem actual_seven_and_two_six_residual_budget {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (G : Fin 2 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ i, facetVertexCount P (G i) = 6) :
    Nat.card (Face P 3) = 10 ∧ facetExcess P = 14 ∧
      (nonsimplicialFacets P).card = 10 ∧
      Fintype.card (SparseSharedRowIndex P e) = 9 ∧
      (∑ H : Face P 3, rankSurplus P H (actualPolygonRelationRank P e H)) ≤ 2 := by
  have hm := actual_facet_count_ge_ten_of_nonsimplicial_count P hN
  have hE := actual_seven_and_two_six_excess_lower_bound P F hF G hG hGsix
  have hE14 : (14 : ℤ) ≤ facetExcess P := by omega
  have hmQ : (10 : ℚ) ≤ Nat.card (Face P 3) := by exact_mod_cast hm
  have hcQ : (9 : ℚ) ≤ Fintype.card (SparseSharedRowIndex P e) := by exact_mod_cast hc
  have heta := seven_facet_surplus_ge_three_halves P hP e F hF
  have htotal := actual_surplus_le_sum P hP e F
  have hmaster := actual_ten_vertex_sparse_master_bound P hP e hn
  have hsumZ : (Nat.card (Face P 3) : ℤ) + facetExcess P ≤ 24 := by
    by_contra h
    have h25 : (25 : ℚ) ≤ (Nat.card (Face P 3) : ℚ) + (facetExcess P : ℚ) := by
      exact_mod_cast (show (25 : ℤ) ≤ (Nat.card (Face P 3) : ℤ) + facetExcess P by omega)
    linarith
  have hm10 : Nat.card (Face P 3) = 10 := by omega
  have hEeq : facetExcess P = 14 := by omega
  have hNeq : (nonsimplicialFacets P).card = 10 := by omega
  rw [hm10, hEeq] at hmaster
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hmaster
  have hceq : Fintype.card (SparseSharedRowIndex P e) = 9 := by
    by_contra hne
    have h10 : (10 : ℚ) ≤ Fintype.card (SparseSharedRowIndex P e) := by
      exact_mod_cast (show 10 ≤ Fintype.card (SparseSharedRowIndex P e) by omega)
    linarith
  refine ⟨hm10, hEeq, hNeq, hceq, ?_⟩
  linarith

/-- In that corner every actual facet is nonsimplicial. -/
theorem actual_seven_and_two_six_all_facets_nonsimplicial {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (G : Fin 2 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ i, facetVertexCount P (G i) = 6) :
    ∀ H : Face P 3, 5 ≤ facetVertexCount P H := by
  obtain ⟨hm, _, hNc, _, _⟩ := actual_seven_and_two_six_residual_budget
    P hP e hn hN hc F hF G hG hGsix
  have hcard : (Finset.univ : Finset (Face P 3)).card ≤ (nonsimplicialFacets P).card := by
    simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, hm, hNc, le_refl]
  have heq : nonsimplicialFacets P = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hcard
  intro H
  have hmem : H ∈ nonsimplicialFacets P := by rw [heq]; exact Finset.mem_univ _
  have h := (mem_nonsimplicialFacets P H).mp hmem
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart12
