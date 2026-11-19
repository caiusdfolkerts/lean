module
public import Papers.IntrinsicActualPolytopes
public import Papers.ThreePolytopeRationalDensity
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.IntervalCases
public import Papers.ZeroColumnRestoration
public import Papers.SelectedNormalReconstruction
public import Papers.NineVertexFacetShapes
public import Papers.SmallRelationMatrixCriteria
public import Papers.SimpleDeletionPaper

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/LowDimensionalActualDensity.lean -/






@[expose] public section

/-!
# Rational density in intrinsic dimension at most three

For dimensions zero, one, and two, every facet has independent homogeneous
vertices.  Its full affine relation space is therefore zero, so the already
proved relation reconstruction applies to the empty relation matrix.  This
includes polygons with any finite number of vertices.

The three-dimensional theorem is transported through the exact intrinsic
model.  The final ambient-five wrapper requires only the corresponding
full four-dimensional vertex theorem, making the logical order explicit.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence

theorem homogeneous_two_vertices_independent {d : ℕ} (P : ConvexPolytope d)
    (v : Fin 2 → P.vertices) (hv : Function.Injective v) :
    LinearIndependent ℝ (fun i => homogeneousVertex (v i).val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hs : a 0 + a 1 = 0 := by
    have h := congrFun ha 0
    simpa [Fin.sum_univ_succ, homogeneousVertex] using h
  have hvec : a 0 • (v 0).val + a 1 • (v 1).val = 0 := by
    ext j
    have h := congrFun ha j.succ
    simpa [Fin.sum_univ_succ, homogeneousVertex] using h
  have ha1 : a 1 = -a 0 := by linarith
  have hdiff : a 0 • ((v 0).val - (v 1).val) = 0 := by
    simpa only [ha1, neg_smul, sub_eq_add_neg, smul_add, smul_neg] using hvec
  have hne : (v 0).val - (v 1).val ≠ 0 := by
    intro h
    have heq := hv (Subtype.ext (sub_eq_zero.mp h))
    exact (by decide : (0 : Fin 2) ≠ 1) heq
  have h0 : a 0 = 0 := (smul_eq_zero.mp hdiff).resolve_right hne
  have h1 : a 1 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

theorem homogeneous_maximal_family_independent_of_dim_le_two {d : ℕ}
    (P : ConvexPolytope d) (hd : d ≤ 2)
    (v : Fin (d+1) → P.vertices) (hv : Function.Injective v) :
    LinearIndependent ℝ (fun i => homogeneousVertex (v i).val) := by
  interval_cases d
  · apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    fin_cases i
    have h := congrFun ha 0
    simpa [Fin.sum_univ_succ, homogeneousVertex] using h
  · exact homogeneous_two_vertices_independent P v hv
  · exact homogeneous_three_vertices_linearIndependent P v hv

theorem facet_card_le_of_maximal_independence {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ)
    (hLI : ∀ b : Fin (d+1) → Fin n, Function.Injective b → LinearIndependent ℝ (p ∘ b))
    (T : Finset (Fin n)) (hT : FacetMask p T) : T.card ≤ d := by
  by_contra hcard
  have hsize : d+1 ≤ T.card := by omega
  obtain ⟨bT⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (d+1)) (β := T) (by simpa using hsize)
  let b : Fin (d+1) → Fin n := fun i => (bT i).val
  have hb : Function.Injective b := Subtype.val_injective.comp bT.injective
  have hdet := (nonzero_minor_iff_independent p b).mpr (hLI b hb)
  have hrank : (Matrix.of (fun i j => p (b i) j)).rank = d+1 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have hmask : (maskRows p T).submatrix b id = Matrix.of (fun i j => p (b i) j) := by
    ext i j
    simp [maskRows, Matrix.submatrix_apply, b, (bT i).property]
  have hbound := Matrix.rank_submatrix_le (maskRows p T) b id
  rw [hmask, hrank, maskRows_rank] at hbound
  have hdim := hT.2.2
  omega

theorem empty_relation_matrix_spans_facets {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ)
    (hLI : ∀ b : Fin (d+1) → Fin n, Function.Injective b → LinearIndependent ℝ (p ∘ b))
    (T : Finset (Fin n)) (hT : FacetMask p T) :
    SpansFacetRelations (0 : Matrix (Fin 0) (Fin n) ℝ) p T := by
  have hcard := facet_card_le_of_maximal_independence p hLI T hT
  have hdim := facetRelationSpace_finrank p T
  have hrank := hT.2.2
  have hzero : finrank ℝ (facetRelationSpace p T) = 0 := by omega
  have hbot := Submodule.finrank_eq_zero.mp hzero
  unfold SpansFacetRelations
  rw [hbot]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Fin.elim0 i.val
  · exact bot_le

theorem full_dim_le_two_rationallyApproximable {d : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : d ≤ 2) :
    Papers.Polytopes.RationallyApproximable P := by
  let n := Fintype.card P.vertices
  let e : Fin n ≃ P.vertices := (Fintype.equivFin P.vertices).symm
  let p := ordinaryVertexCoordinates P e
  let C : Matrix (Fin 0) (Fin n) ℝ := 0
  have hp : Spans (homogeneousPoints p) := by
    simpa only [p, ordinaryVertexCoordinates_homogeneous] using vertexCoordinates_spans P e hP
  have hLI : ∀ b : Fin (d+1) → Fin n, Function.Injective b →
      LinearIndependent ℝ (vertexCoordinates P e ∘ b) := by
    intro b hb
    exact homogeneous_maximal_family_independent_of_dim_le_two P hd
      (e ∘ b) (e.injective.comp hb)
  have hrelations : ∀ T, FacetMask (homogeneousPoints p) T →
      SpansFacetRelations C (homogeneousPoints p) T := by
    intro T hT
    have hT' : FacetMask (vertexCoordinates P e) T := by
      simpa only [p, ordinaryVertexCoordinates_homogeneous] using hT
    simpa only [C, p, ordinaryVertexCoordinates_homogeneous] using
      empty_relation_matrix_spans_facets (vertexCoordinates P e) hLI T hT'
  have hclosure := rational_ordinary_polytope_density_seven_relation_rows
    (c := 0) (by decide) C p hp (by simp [C]) hrelations
  apply rationallyApproximable_of_coordinate_density P e
  apply closure_mono (s := {q | RationalCoordinates q ∧
    Spans (homogeneousPoints q) ∧ LabelledPolytopeEquivalent p q}) ?_ hclosure
  intro q hq
  exact ⟨hq.1, hq.2.2⟩

theorem full_dim_le_three_rationallyApproximable {d : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : d ≤ 3) :
    Papers.Polytopes.RationallyApproximable P := by
  by_cases h : d = 3
  · subst d
    exact Papers.ThreePolytopeRationalDensity.three_polytope_rationally_approximable P hP
  · exact full_dim_le_two_rationallyApproximable P hP (by omega)

/-- All actual polytopes of intrinsic dimension at most three are
rationally approximable in their given ambient space, with no bound on
their number of vertices. -/
theorem ambient_dimension_le_three_rationallyApproximable {d : ℕ}
    (P : ConvexPolytope d) (hd : P.dim ≤ 3) :
    Papers.Polytopes.RationallyApproximable P := by
  obtain ⟨r, _, Q, hQ, _, hr, htransport⟩ := exists_intrinsic_actual_model P
  apply htransport
  apply full_dim_le_three_rationallyApproximable Q hQ
  simpa only [hr] using hd

/-- In particular, a vertex theorem for full four-polytopes gives the
same rational-density conclusion for dimension-at-most-four cores in E5
(and in every other finite ambient dimension). -/
theorem ambient_dimension_le_four_of_full_four {d N : ℕ}
    (P : ConvexPolytope d) (hd : P.dim ≤ 4) (hn : P.vertices.card ≤ N)
    (hfour : ∀ Q : ConvexPolytope 4, Q.IsFullDim → Q.vertices.card ≤ N →
      Papers.Polytopes.RationallyApproximable Q) :
    Papers.Polytopes.RationallyApproximable P := by
  obtain ⟨r, _, Q, hQ, hcard, hr, htransport⟩ := exists_intrinsic_actual_model P
  apply htransport
  have hr4 : r ≤ 4 := by simpa only [hr] using hd
  by_cases h : r = 4
  · rw [← h] at hfour
    exact hfour Q hQ (by simpa only [hcard] using hn)
  · exact full_dim_le_three_rationallyApproximable Q hQ (by omega)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ActualCoreRestoration.lean -/



@[expose] public section

/-!
# Actual retained cores and restoration of all other vertices

A retained core is the ordinary convex hull of a nonempty subset of the
original extreme vertices. Its rational approximation is transported through
the complete face-order isomorphism. Every retained part of an old facet is
an exposed core face, so its dimension, and therefore homogeneous rank,
is preserved. The other vertices are chosen freely and rationally nearby.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence
open Papers.PolytopeIncidenceConfiguration Papers.HomogeneousSpanDimension
open Papers.FaceVertexCardinality

def retainedVertexCore {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (I : Finset (Fin n)) (hI : I.Nonempty) :
    ConvexPolytope d :=
  vertexSubsetPolytope P (I.image fun i => (e i).val) (hI.image _) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (e i).property)

def retainedVertexEquiv {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (I : Finset (Fin n)) (hI : I.Nonempty) :
    I ≃ VertexType (retainedVertexCore P e I hI) :=
  Equiv.ofBijective
    (fun i => ⟨(e i.val).val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩)
    ⟨fun i j h => Subtype.ext (e.injective (Subtype.ext
      (congrArg (fun v : VertexType (retainedVertexCore P e I hI) => v.val) h))), by
      intro v
      obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp v.property
      exact ⟨⟨i, hi⟩, Subtype.ext hiv⟩⟩

theorem retainedVertexCore_body_subset {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (I : Finset (Fin n)) (hI : I.Nonempty) :
    (retainedVertexCore P e I hI).toSet ⊆ P.toSet := by
  apply convexHull_mono
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact (e i).property

theorem retainedVertexCore_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (I : Finset (Fin n)) (hI : I.Nonempty) :
    (retainedVertexCore P e I hI).vertices.card = I.card := by
  have h := Fintype.card_congr (retainedVertexEquiv P e I hI)
  simpa only [VertexType, Fintype.card_coe] using h.symm

theorem homogeneousVertex_subsetRank_of_hull {d n : ℕ}
    (u : Fin n → E d) (S : Finset (Fin n)) (A : Set (E d))
    (hA : A.Nonempty) (hhull : convexHull ℝ (u '' (↑S : Set (Fin n))) = A) :
    subsetRank (fun i => homogeneousVertex (u i)) S = faceDim A + 1 := by
  let U := Submodule.span ℝ
    ((fun i => homogeneousVertex (u i)) '' (↑S : Set (Fin n)))
  have hm : U.map (coordinateHomogeneousEquiv d).toLinearMap =
      liftSpan (u '' (↑S : Set (Fin n))) := by
    rw [Submodule.map_span]
    apply congrArg (Submodule.span ℝ)
    ext z
    constructor
    · rintro ⟨a, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨u i, ⟨i, hi, rfl⟩, (coordinateHomogeneousEquiv_vertex (u i)).symm⟩
    · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨homogeneousVertex (u i), ⟨i, hi, rfl⟩,
        coordinateHomogeneousEquiv_vertex (u i)⟩
  calc
    _ = finrank ℝ U := rfl
    _ = finrank ℝ (U.map (coordinateHomogeneousEquiv d).toLinearMap) :=
      ((coordinateHomogeneousEquiv d).finrank_map_eq U).symm
    _ = finrank ℝ (liftSpan A) := by rw [hm, ← liftSpan_convexHull, hhull]
    _ = faceDim A + 1 := finrank_liftSpan hA

/-- The image of precisely the labels of a core face is the complete
vertex set of its transported face. This uses the induced vertex map. -/
theorem core_face_labelled_hull {d n : ℕ} (K Q : ConvexPolytope d)
    (I : Finset (Fin n)) (b : I ≃ VertexType K)
    (φ : FaceType K ≃o FaceType Q) (A : FaceType K)
    (S : Finset (Fin n))
    (hS : ∀ i, i ∈ S ↔ ∃ hi : i ∈ I, (b ⟨i, hi⟩).val ∈ A.val)
    (u : Fin n → E d)
    (hu : ∀ (i : Fin n) (hi : i ∈ I), u i = (imageVertex φ (b ⟨i, hi⟩)).val) :
    convexHull ℝ (u '' (↑S : Set (Fin n))) = (φ A).val := by
  have heq : u '' (↑S : Set (Fin n)) =
      (↑(Q.vertices.filter (· ∈ (φ A).val)) : Set (E d)) := by
    ext x
    constructor
    · rintro ⟨i, hiS, rfl⟩
      obtain ⟨hi, hiA⟩ := (hS i).mp hiS
      rw [hu i hi]
      exact Finset.mem_filter.mpr
        ⟨(imageVertex φ (b ⟨i, hi⟩)).property,
          (imageVertex_mem_iff φ (b ⟨i, hi⟩) A).mpr hiA⟩
    · intro hx
      obtain ⟨hxQ, hxA⟩ := Finset.mem_filter.mp hx
      obtain ⟨v, hv⟩ := (vertexEquivOfFaceOrder φ).surjective ⟨x, hxQ⟩
      obtain ⟨i, hi⟩ := b.surjective v
      have himage : (imageVertex φ (b i)).val = x := by
        rw [hi]
        exact congrArg Subtype.val hv
      have hiA : (b i).val ∈ A.val := by
        apply (imageVertex_mem_iff φ (b i) A).mp
        rw [himage]
        exact hxA
      refine ⟨i.val, (hS i.val).mpr ⟨i.property, hiA⟩, ?_⟩
      exact (hu i.val i.property).trans himage
  rw [heq]
  exact (face_eq_hull_vertices Q (φ A).property).symm

theorem core_face_subsetRank_preserved {d n : ℕ} (K Q : ConvexPolytope d)
    (I : Finset (Fin n)) (b : I ≃ VertexType K)
    (φ : FaceType K ≃o FaceType Q) (A : FaceType K)
    (S : Finset (Fin n))
    (hS : ∀ i, i ∈ S ↔ ∃ hi : i ∈ I, (b ⟨i, hi⟩).val ∈ A.val)
    (u v : Fin n → E d)
    (hu : ∀ (i : Fin n) (hi : i ∈ I), u i = (b ⟨i, hi⟩).val)
    (hv : ∀ (i : Fin n) (hi : i ∈ I), v i = (imageVertex φ (b ⟨i, hi⟩)).val) :
    subsetRank (fun i => homogeneousVertex (v i)) S =
      subsetRank (fun i => homogeneousVertex (u i)) S := by
  have hold := core_face_labelled_hull K K I b (OrderIso.refl _) A S hS u (by
    intro i hi
    rw [imageVertex_refl]
    exact hu i hi)
  have hnew := core_face_labelled_hull K Q I b φ A S hS v hv
  rw [homogeneousVertex_subsetRank_of_hull v S (φ A).val (φ A).property.2 hnew,
    homogeneousVertex_subsetRank_of_hull u S A.val A.property.2 hold,
    faceOrderIso_dimension φ A]

def freelyRestoredPoints {d n : ℕ} (K : ConvexPolytope d)
    (I : Finset (Fin n)) (b : I ≃ VertexType K)
    (z : (VertexType K → E d) × ((Fin n × Fin d) → ℝ)) : Fin n → E d :=
  fun i => if hi : i ∈ I then z.1 (b ⟨i, hi⟩)
    else (euclideanCoordinateEquiv d).symm (fun j => z.2 (i, j))

theorem freelyRestoredPoints_continuous {d n : ℕ} (K : ConvexPolytope d)
    (I : Finset (Fin n)) (b : I ≃ VertexType K) :
    Continuous (freelyRestoredPoints K I b) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simp only [freelyRestoredPoints, dif_pos hi]
    exact (continuous_apply (b ⟨i, hi⟩)).comp continuous_fst
  · simp only [freelyRestoredPoints, dif_neg hi]
    exact (euclideanCoordinateEquiv d).symm.continuous.comp
      (continuous_pi fun j => (continuous_apply (i, j)).comp continuous_snd)

theorem actual_retained_core_rank_density {n : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices)
    (I : Finset (Fin n)) (hI : I.Nonempty)
    (hcore : RationallyApproximable (retainedVertexCore P e I hI)) :
    vertexCoordinates P e ∈ closure {q : Fin n → Fin 5 → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ S ∈ facetMasks (vertexCoordinates P e),
        subsetRank q (S ∩ I) = subsetRank (vertexCoordinates P e) (S ∩ I)} := by
  let K := retainedVertexCore P e I hI
  let b := retainedVertexEquiv P e I hI
  let t : (Fin n × Fin 4) → ℝ := fun a => (e a.1).val a.2
  let F := fun z : (VertexType K → E 4) × ((Fin n × Fin 4) → ℝ) =>
    fun i => homogeneousVertex (freelyRestoredPoints K I b z i)
  have hF : Continuous F := continuous_pi fun i => continuous_homogeneousVertex.comp
    ((continuous_apply i).comp (freelyRestoredPoints_continuous K I b))
  have hbase : F (Subtype.val, t) = vertexCoordinates P e := by
    ext i j
    by_cases hi : i ∈ I
    · simp only [F, freelyRestoredPoints, dif_pos hi]
      rfl
    · simp only [F, freelyRestoredPoints, dif_neg hi]
      cases j using Fin.cases <;> rfl
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have hpre : F ⁻¹' U ∈ 𝓝 (Subtype.val, t) := by
    apply hF.continuousAt.preimage_mem_nhds
    simpa only [hbase] using hU
  obtain ⟨Q, φ, t', hQr, hnear⟩ := hcore.exists_parameters_in_neighborhood t (F ⁻¹' U) hpre
  let z := ((fun v => (imageVertex φ v).val), (fun a => (t' a : ℝ)))
  let v := freelyRestoredPoints K I b z
  have hv (i : Fin n) (hi : i ∈ I) :
      v i = (imageVertex φ (b ⟨i, hi⟩)).val := by
    simp only [v, freelyRestoredPoints, dif_pos hi, z]
  refine ⟨F z, hnear, ?_⟩
  refine ⟨?_, (fun _ => rfl), ?_⟩
  · intro i j
    cases j using Fin.cases with
    | zero => exact ⟨1, by simp only [F, homogeneousVertex, Fin.cases_zero, Rat.cast_one]⟩
    | succ j =>
      by_cases hi : i ∈ I
      · change ∃ a : ℚ, (a : ℝ) = v i j
        rw [hv i hi]
        exact hQr _ (imageVertex φ (b ⟨i, hi⟩)).property j
      · exact ⟨t' (i, j), by simp only [F, freelyRestoredPoints, dif_neg hi, z]; rfl⟩
  · intro S hS
    by_cases hSI : (S ∩ I).Nonempty
    · obtain ⟨G, hG⟩ := facetMask_actual_three_face P e S
        ((mem_facetMasks _ S).mp hS)
      let Aset := G.val.carrier ∩ K.toSet
      have hAne : Aset.Nonempty := by
        obtain ⟨i, hi⟩ := hSI
        obtain ⟨hiS, hiI⟩ := Finset.mem_inter.mp hi
        refine ⟨(e i).val, ?_, ?_⟩
        · exact (mem_actualFaceLabels P e G.val i).mp (hG.symm ▸ hiS)
        · exact vertex_mem_body K (b ⟨i, hiI⟩).property
      have hA : K.IsFace Aset := face_inter_subpolytope P K
        (retainedVertexCore_body_subset P e I hI) G.val.isFace hAne
      let A : FaceType K := ⟨Aset, hA⟩
      have hlabels (i : Fin n) : i ∈ S ∩ I ↔
          ∃ hi : i ∈ I, (b ⟨i, hi⟩).val ∈ A.val := by
        constructor
        · intro hi
          obtain ⟨hiS, hiI⟩ := Finset.mem_inter.mp hi
          refine ⟨hiI, ?_, vertex_mem_body K (b ⟨i, hiI⟩).property⟩
          exact (mem_actualFaceLabels P e G.val i).mp (hG.symm ▸ hiS)
        · rintro ⟨hiI, hiG, hiK⟩
          refine Finset.mem_inter.mpr ⟨?_, hiI⟩
          rw [← hG]
          exact (mem_actualFaceLabels P e G.val i).mpr hiG
      exact core_face_subsetRank_preserved K Q I b φ A (S ∩ I) hlabels
        (fun i => (e i).val) v (fun _ _ => rfl) hv
    · have hempty : S ∩ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSI
      rw [hempty, subsetRank_empty, subsetRank_empty]

/-- The complete actual-polytope apex restoration principle. Its input is
rational approximation of the ordinary retained core, and the selected
matrix is required to span every full facet relation space. -/
theorem actual_zero_column_restoration {c n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (C : Matrix (Fin c) (Fin n) ℝ) (I : Finset (Fin n)) (hI : I.Nonempty)
    (hzero : ∀ i j, j ∉ I → C i j = 0)
    (hrelations : ∀ S ∈ facetMasks (vertexCoordinates P e),
      supportedRowSpan C S = globalRelationSpace (vertexCoordinates P e) S)
    (hcore : RationallyApproximable (retainedVertexCore P e I hI)) :
    RationallyApproximable P := by
  have hh := rational_polytope_density_from_zero_column_core_rank_density
    C (vertexCoordinates P e) (vertexCoordinates_spans P e hP) (fun _ => rfl)
    I hzero hrelations (actual_retained_core_rank_density P e I hI hcore)
  have ho := ordinary_density_of_homogeneous_density (ordinaryVertexCoordinates P e)
    (by simpa only [ordinaryVertexCoordinates_homogeneous] using hh)
  apply rationallyApproximable_of_coordinate_density P e
  apply closure_mono ?_ ho
  intro q hq
  exact ⟨hq.1, hq.2.2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/NormalCoreRankDensity.lean -/




@[expose] public section

/-!
# The rank information supplied by a genuine normal core

The core is an ordinary convex polytope in a hyperplane separated from the
origin. A face-order preserving approximation preserves the affine dimension
of each specified face. Homogenization turns this into an upper bound on its
linear rank; the usual open lower bound gives equality. The approximating
vertices need not remain in the original, possibly irrational hyperplane.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence

theorem subsetRank_linearMap_le {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (T : Finset (Fin n))
    (L : (Fin r → ℝ) →ₗ[ℝ] (Fin s → ℝ)) :
    subsetRank (fun i => L (p i)) T ≤ subsetRank p T := by
  have heq : Submodule.span ℝ ((fun i => L (p i)) '' (↑T : Set (Fin n))) =
      (Submodule.span ℝ (p '' (↑T : Set (Fin n)))).map L := by
    rw [Submodule.map_span, Set.image_image]
  change finrank ℝ (Submodule.span ℝ ((fun i => L (p i)) '' (↑T : Set (Fin n)))) ≤ _
  rw [heq]
  exact Submodule.finrank_map_le L _

def homogeneousTail (r : ℕ) : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun x j := x j.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homogeneousOnHyperplane {r : ℕ} (c : Fin r → ℝ) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun x := Fin.cases (c ⬝ᵥ x) x
  map_add' x y := by
    ext j
    cases j using Fin.cases
    · exact dotProduct_add c x y
    · rfl
  map_smul' t x := by
    ext j
    cases j using Fin.cases
    · simp only [Fin.cases_zero, Pi.smul_apply, smul_eq_mul, dotProduct_smul, RingHom.id_apply]
    · rfl

theorem subsetRank_le_homogeneous {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (T : Finset (Fin n)) :
    subsetRank p T ≤ subsetRank (homogeneousPoints p) T := by
  have h := subsetRank_linearMap_le (homogeneousPoints p) T (homogeneousTail r)
  have heq : (fun i => homogeneousTail r (homogeneousPoints p i)) = p := rfl
  simpa only [heq] using h

theorem subsetRank_homogeneous_of_hyperplane {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (c : Fin r → ℝ)
    (hc : ∀ i, c ⬝ᵥ p i = 1) (T : Finset (Fin n)) :
    subsetRank (homogeneousPoints p) T = subsetRank p T := by
  apply Nat.le_antisymm _ (subsetRank_le_homogeneous p T)
  have h := subsetRank_linearMap_le p T (homogeneousOnHyperplane c)
  have heq : (fun i => homogeneousOnHyperplane c (p i)) = homogeneousPoints p := by
    ext i j
    cases j using Fin.cases
    · exact hc i
    · rfl
  simpa only [heq] using h

private def univVertexEquiv {m r : ℕ} (K : ConvexPolytope r)
    (e : Fin m ≃ K.vertices) :
    (Finset.univ : Finset (Fin m)) ≃ VertexType K where
  toFun i := e i.val
  invFun v := ⟨e.symm v, Finset.mem_univ _⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv v := e.apply_symm_apply v

theorem transported_core_face_homogeneous_rank {m r : ℕ}
    (K Q : ConvexPolytope r) (e : Fin m ≃ K.vertices)
    (φ : FaceType K ≃o FaceType Q)
    (T : Finset (Fin m)) (F : FaceType K)
    (hT : ∀ j, j ∈ T ↔ (e j).val ∈ F.val) :
    subsetRank (fun j => homogeneousVertex (imageVertex φ (e j)).val) T =
      subsetRank (vertexCoordinates K e) T := by
  exact core_face_subsetRank_preserved K Q Finset.univ (univVertexEquiv K e)
    φ F T (by
      intro j
      constructor
      · intro hj
        exact ⟨Finset.mem_univ j, (hT j).mp hj⟩
      · rintro ⟨_, hj⟩
        exact (hT j).mpr hj)
    (fun j => (e j).val) (fun j => (imageVertex φ (e j)).val)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Rational approximation of the actual core supplies exactly the incident
subset-rank density required by the vertex reconstruction theorem. -/
theorem incident_rank_density_of_actual_core {m n r : ℕ}
    (K : ConvexPolytope r) (e : Fin m ≃ K.vertices)
    (c : Fin r → ℝ)
    (hc : ∀ j, c ⬝ᵥ ordinaryVertexCoordinates K e j = 1)
    (S : Fin m → Finset (Fin n))
    (hfaces : ∀ i, (incidentSelectedNormals S i).Nonempty →
      ∃ F : FaceType K, ∀ j, j ∈ incidentSelectedNormals S i ↔ (e j).val ∈ F.val)
    (hK : RationallyApproximable K) :
    ordinaryVertexCoordinates K e ∈ closure
      (incidentRankRealizations (ordinaryVertexCoordinates K e) S) := by
  let A := ordinaryVertexCoordinates K e
  let H := fun z : (VertexType K → E r) × (Unit → ℝ) =>
    fun j => euclideanCoordinateEquiv r (z.1 (e j))
  have hH : Continuous H := continuous_pi fun j =>
    (euclideanCoordinateEquiv r).continuous.comp
      ((continuous_apply (e j)).comp continuous_fst)
  have hHbase : H (Subtype.val, (0 : Unit → ℝ)) = A := rfl
  have hlower : ∀ᶠ B in 𝓝 A, ∀ i,
      subsetRank A (incidentSelectedNormals S i) ≤
        subsetRank B (incidentSelectedNormals S i) :=
    eventually_all.mpr fun i => eventually_subsetRank_ge A (incidentSelectedNormals S i)
  apply mem_closure_iff_nhds.mpr
  intro U hU
  let V := U ∩ {B | ∀ i,
    subsetRank A (incidentSelectedNormals S i) ≤
      subsetRank B (incidentSelectedNormals S i)}
  have hV : V ∈ 𝓝 A := inter_mem hU hlower
  have hpre : H ⁻¹' V ∈ 𝓝 (Subtype.val, (0 : Unit → ℝ)) :=
    hH.continuousAt.preimage_mem_nhds hV
  obtain ⟨Q, φ, t, hQr, hnear⟩ :=
    hK.exists_parameters_in_neighborhood (0 : Unit → ℝ) (H ⁻¹' V) hpre
  let B : Fin m → Fin r → ℝ :=
    fun j => euclideanCoordinateEquiv r (imageVertex φ (e j)).val
  have hBnear : B ∈ V := hnear
  refine ⟨B, hBnear.1, ?_, ?_⟩
  · intro j a
    exact hQr _ (imageVertex φ (e j)).property a
  · intro i
    let T := incidentSelectedNormals S i
    by_cases hT : T.Nonempty
    · obtain ⟨F, hF⟩ := hfaces i hT
      have hhom := transported_core_face_homogeneous_rank K Q e φ T F hF
      have hhom' : subsetRank (homogeneousPoints B) T =
          subsetRank (homogeneousPoints A) T := hhom
      apply Nat.le_antisymm _ (hBnear.2 i)
      calc
        subsetRank B T ≤ subsetRank (homogeneousPoints B) T :=
          subsetRank_le_homogeneous B T
        _ = subsetRank (homogeneousPoints A) T := hhom'
        _ = subsetRank A T := subsetRank_homogeneous_of_hyperplane A c hc T
    · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      change subsetRank B T = subsetRank A T
      rw [he, subsetRank_empty, subsetRank_empty]

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FiniteNormalCore.lean -/



@[expose] public section

/-!
# The ordinary convex hull of normalized selected facet normals

Every generator is exposed by the sum of the original vertices on its facet.
The construction therefore contains exactly the supplied normals as extreme
vertices. Original vertex incidences become genuine exposed faces of the
core. No oriented-matroid or abstract face-lattice realization is substituted
for this actual convex hull.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence

theorem FacetMask.eq_of_subset {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S T : Finset (Fin n)}
    (hS : FacetMask p S) (hT : FacetMask p T) (hST : S ⊆ T) : S = T := by
  let U := Submodule.span ℝ (p '' (↑S : Set (Fin n)))
  let V := Submodule.span ℝ (p '' (↑T : Set (Fin n)))
  have hUV : U ≤ V := Submodule.span_mono (Set.image_mono hST)
  have hdim : finrank ℝ U = finrank ℝ V := by
    have h₁ := hS.2.2
    have h₂ := hT.2.2
    change finrank ℝ U + 1 = r at h₁
    change finrank ℝ V + 1 = r at h₂
    omega
  have heq : U = V := Submodule.eq_of_le_of_finrank_eq hUV hdim
  obtain ⟨a, ha⟩ := hS.2.1
  have hUker : U ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact ha.1 i hi
  apply Finset.Subset.antisymm hST
  intro i hi
  have hm : p i ∈ U := heq ▸ Submodule.subset_span ⟨i, hi, rfl⟩
  have hz : a ⬝ᵥ p i = 0 := hUker hm
  by_contra hn
  exact (ne_of_gt (ha.2 i hn)) hz

def sumVertexCoordinates {n r : ℕ} (p : Fin n → Fin r → ℝ) : Fin r → ℝ :=
  ∑ i, p i

theorem StrictSupport.dot_sum_pos {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)} {a : Fin r → ℝ}
    (h : StrictSupport p S a) (hproper : S ≠ Finset.univ) :
    0 < a ⬝ᵥ sumVertexCoordinates p := by
  have hex : ∃ i, i ∉ S := by
    by_contra hn
    push_neg at hn
    exact hproper (Finset.eq_univ_of_forall hn)
  obtain ⟨i, hi⟩ := hex
  rw [sumVertexCoordinates, dotProduct_sum]
  exact Finset.sum_pos' (fun j _ => h.nonneg j)
    ⟨i, Finset.mem_univ _, h.2 i hi⟩

def normalizeFacetNormal {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (a : Fin r → ℝ) : Fin r → ℝ :=
  (a ⬝ᵥ sumVertexCoordinates p)⁻¹ • a

theorem normalizeFacetNormal_strictSupport {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)} {a : Fin r → ℝ}
    (h : StrictSupport p S a) (hproper : S ≠ Finset.univ) :
    StrictSupport p S (normalizeFacetNormal p a) := by
  have hpos := h.dot_sum_pos hproper
  constructor
  · intro i hi
    rw [normalizeFacetNormal, smul_dotProduct, h.1 i hi]
    simp
  · intro i hi
    rw [normalizeFacetNormal, smul_dotProduct]
    exact mul_pos (inv_pos.mpr hpos) (h.2 i hi)

theorem normalizeFacetNormal_hyperplane {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)} {a : Fin r → ℝ}
    (h : StrictSupport p S a) (hproper : S ≠ Finset.univ) :
    sumVertexCoordinates p ⬝ᵥ normalizeFacetNormal p a = 1 := by
  rw [dotProduct_comm, normalizeFacetNormal, smul_dotProduct]
  exact inv_mul_cancel₀ (ne_of_gt (h.dot_sum_pos hproper))

theorem selected_normal_singleton_support {m n r : ℕ}
    (p : Fin n → Fin r → ℝ) (A : Fin m → Fin r → ℝ)
    (S : Fin m → Finset (Fin n))
    (hS : ∀ j, FacetMask p (S j)) (hinj : Function.Injective S)
    (hsupport : ∀ j, StrictSupport p (S j) (A j)) (j : Fin m) :
    StrictSupport A {j} (∑ i ∈ S j, p i) := by
  constructor
  · intro k hk
    have hkj : k = j := Finset.mem_singleton.mp hk
    subst k
    rw [sum_dotProduct]
    apply Finset.sum_eq_zero
    intro i hi
    rw [dotProduct_comm]
    exact (hsupport j).1 i hi
  · intro k hk
    have hkj : k ≠ j := by simpa only [Finset.mem_singleton] using hk
    have hnot : ¬ S j ⊆ S k := by
      intro hsub
      exact hkj (hinj ((hS j).eq_of_subset (hS k) hsub)).symm
    obtain ⟨i, hiS, hik⟩ := Finset.not_subset.mp hnot
    rw [sum_dotProduct]
    apply Finset.sum_pos'
    · intro t ht
      rw [dotProduct_comm]
      exact (hsupport k).nonneg t
    · refine ⟨i, hiS, ?_⟩
      rw [dotProduct_comm]
      exact (hsupport k).2 i hik

theorem singleton_supports_injective {m r : ℕ}
    (A : Fin m → Fin r → ℝ)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a) : Function.Injective A := by
  intro i j hij
  by_contra hne
  obtain ⟨a, ha⟩ := hsingle i
  have hz := ha.1 i (Finset.mem_singleton_self i)
  have hp := ha.2 j (by simpa only [Finset.mem_singleton] using Ne.symm hne)
  rw [← hij, hz] at hp
  exact (lt_irrefl 0) hp

def exposedCoordinatePolytope {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a) : ConvexPolytope r where
  vertices := Finset.univ.image fun j => (euclideanCoordinateEquiv r).symm (A j)
  vertices_nonempty := by
    refine ⟨(euclideanCoordinateEquiv r).symm (A ⟨0, hm⟩), ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a, ha⟩ := hsingle j
      have hex := strictSupport_exposed_hull ha (Finset.singleton_nonempty j)
      have hset : labelledHull A {j} = {A j} := by
        simp only [labelledHull, Finset.coe_singleton, Set.image_singleton,
          convexHull_singleton]
      rw [hset] at hex
      have h := exposed_image_equiv (euclideanCoordinateEquiv r).symm hex
      rw [coordinate_image_hull, Set.image_singleton] at h
      exact h.isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset

def exposedCoordinateVertexEquiv {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a) :
    Fin m ≃ (exposedCoordinatePolytope A hm hsingle).vertices :=
  Equiv.ofBijective
    (fun j => ⟨(euclideanCoordinateEquiv r).symm (A j),
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j h => singleton_supports_injective A hsingle
      ((euclideanCoordinateEquiv r).symm.injective (congrArg Subtype.val h)), by
      intro v
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp v.property
      exact ⟨j, Subtype.ext hj⟩⟩

@[simp] theorem exposedCoordinateVertexEquiv_coordinates {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a) :
    ordinaryVertexCoordinates (exposedCoordinatePolytope A hm hsingle)
      (exposedCoordinateVertexEquiv A hm hsingle) = A := by
  ext j k
  exact congrFun ((euclideanCoordinateEquiv r).apply_symm_apply (A j)) k

theorem exposedCoordinatePolytope_card {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a) :
    (exposedCoordinatePolytope A hm hsingle).vertices.card = m := by
  have h := Fintype.card_congr (exposedCoordinateVertexEquiv A hm hsingle)
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm

theorem exposedCoordinatePolytope_support_face {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a)
    (T : Finset (Fin m)) (hT : T.Nonempty)
    (a : Fin r → ℝ) (ha : StrictSupport A T a) :
    ∃ F : FaceType (exposedCoordinatePolytope A hm hsingle), ∀ j,
      j ∈ T ↔ ((exposedCoordinateVertexEquiv A hm hsingle) j).val ∈ F.val := by
  let K := exposedCoordinatePolytope A hm hsingle
  let e := exposedCoordinateVertexEquiv A hm hsingle
  have hbody : euclideanCoordinateEquiv r '' K.toSet = coordinateHull A := by
    have hh := coordinateHull_actual_polytope K e
    have he : ordinaryVertexCoordinates K e = A :=
      exposedCoordinateVertexEquiv_coordinates A hm hsingle
    rw [he] at hh
    exact hh
  let G : ActualCoordinateFace A := ⟨labelledHull A T,
    strictSupport_exposed_hull ha hT, by
      obtain ⟨j, hj⟩ := hT
      exact ⟨A j, subset_convexHull ℝ _ ⟨j, hj, rfl⟩⟩⟩
  let F := (coordinateFaceOrderIso K A hbody).symm G
  refine ⟨F, ?_⟩
  intro j
  have hF : (euclideanCoordinateEquiv r '' F.val) = G.val := by
    exact congrArg Subtype.val ((coordinateFaceOrderIso K A hbody).apply_symm_apply G)
  have hcoord : euclideanCoordinateEquiv r (e j).val = A j :=
    congrFun (exposedCoordinateVertexEquiv_coordinates A hm hsingle) j
  rw [← strictSupport_label_exact ha hT j, ← hcoord]
  change euclideanCoordinateEquiv r (e j).val ∈ G.val ↔ (e j).val ∈ F.val
  rw [← hF]
  constructor
  · rintro ⟨y, hy, heq⟩
    have heqy := (euclideanCoordinateEquiv r).injective heq
    exact heqy ▸ hy
  · intro hj
    exact ⟨(e j).val, hj, rfl⟩

theorem selected_normal_incidence_support {m n r : ℕ}
    (p : Fin n → Fin r → ℝ) (A : Fin m → Fin r → ℝ)
    (S : Fin m → Finset (Fin n))
    (hsupport : ∀ j, StrictSupport p (S j) (A j)) (i : Fin n) :
    StrictSupport A (incidentSelectedNormals S i) (p i) := by
  constructor
  · intro j hj
    rw [dotProduct_comm]
    exact (hsupport j).1 i ((mem_incidentSelectedNormals S i j).mp hj)
  · intro j hj
    rw [dotProduct_comm]
    exact (hsupport j).2 i (fun hi => hj ((mem_incidentSelectedNormals S i j).mpr hi))

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/SelectedFacetCoreDensity.lean -/




@[expose] public section

/-!
# Transfer from a small core of nonsimplicial facet normals

The core has one actual extreme vertex for each selected facet and affine
dimension at most the original dimension. This proves the precise core
transfer used before the nine-vertex and ten-vertex relation analysis.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.ActualThreeVertexIndependence
open Papers.PolytopeIncidenceCounting Papers.PolytopeFacetSurplus Papers.PolytopeFaceCounting

theorem exposedCoordinatePolytope_dim_bound {m r : ℕ}
    (A : Fin m → Fin r → ℝ) (hm : 0 < m)
    (hsingle : ∀ j, ∃ a, StrictSupport A {j} a)
    (c : Fin r → ℝ) (hc : ∀ j, c ⬝ᵥ A j = 1) :
    (exposedCoordinatePolytope A hm hsingle).dim + 1 ≤ r := by
  let K := exposedCoordinatePolytope A hm hsingle
  let e := exposedCoordinateVertexEquiv A hm hsingle
  have h := actualFaceLabels_rank K e ⟨K.toSet, toSet_isFace K⟩
  rw [actualFaceLabels_top] at h
  have hcoords : vertexCoordinates K e = homogeneousPoints A := by
    rw [← ordinaryVertexCoordinates_homogeneous, exposedCoordinateVertexEquiv_coordinates]
  rw [hcoords, subsetRank_homogeneous_of_hyperplane A c hc] at h
  have hr : subsetRank A Finset.univ ≤ r := by
    have hh := (Submodule.span ℝ (A '' (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)))).finrank_le
    change finrank ℝ (Submodule.span ℝ
      (A '' (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)))) ≤ r
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hh
  exact h ▸ hr

/-- Uniform selected-facet transfer. The input `hcores` is a theorem about
actual lower-dimensional convex polytopes, not a density hypothesis attached
to an arbitrary algebraic or combinatorial core. -/
theorem density_from_selected_facet_core {m n d k : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans p)
    (hfirst : ∀ i, p i 0 = 1)
    (S : Fin m → Finset (Fin n)) (hS : ∀ j, FacetMask p (S j))
    (hinj : Function.Injective S)
    (hcover : ∀ T ∈ facetMasks p, T.card ≤ d ∨ ∃ j, S j = T)
    (hmk : m ≤ k)
    (hcores : ∀ K : ConvexPolytope (d + 1), K.dim ≤ d → K.vertices.card ≤ k →
      RationallyApproximable K) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  let raw : Fin m → Fin (d + 1) → ℝ :=
    fun j => Classical.choose (hS j).2.1
  have hraw (j : Fin m) : StrictSupport p (S j) (raw j) :=
    Classical.choose_spec (hS j).2.1
  let A : Fin m → Fin (d + 1) → ℝ := fun j => normalizeFacetNormal p (raw j)
  have hsupp (j : Fin m) : StrictSupport p (S j) (A j) :=
    normalizeFacetNormal_strictSupport (hraw j) ((hS j).ne_univ hp)
  have hplane (j : Fin m) : sumVertexCoordinates p ⬝ᵥ A j = 1 :=
    normalizeFacetNormal_hyperplane (hraw j) ((hS j).ne_univ hp)
  have hne (j : Fin m) : A j ≠ 0 := by
    intro hz
    have hh := hplane j
    simp only [hz, dotProduct_zero] at hh
    exact zero_ne_one hh
  apply rational_polytope_density_from_selected_normal_rank_density p hp hfirst A S hne
    (fun j => (hsupp j).1) hcover
  by_cases hm : 0 < m
  · have hsingle (j : Fin m) : ∃ a, StrictSupport A {j} a :=
      ⟨_, selected_normal_singleton_support p A S hS hinj hsupp j⟩
    let K := exposedCoordinatePolytope A hm hsingle
    let e := exposedCoordinateVertexEquiv A hm hsingle
    have hdim : K.dim ≤ d := by
      have hh := exposedCoordinatePolytope_dim_bound A hm hsingle
        (sumVertexCoordinates p) hplane
      change K.dim + 1 ≤ d + 1 at hh
      omega
    have hcard : K.vertices.card ≤ k := by
      rw [exposedCoordinatePolytope_card]
      exact hmk
    have hdense := hcores K hdim hcard
    have hface (i : Fin n) (hi : (incidentSelectedNormals S i).Nonempty) :
        ∃ F : FaceType K, ∀ j,
          j ∈ incidentSelectedNormals S i ↔ (e j).val ∈ F.val :=
      exposedCoordinatePolytope_support_face A hm hsingle _ hi (p i)
        (selected_normal_incidence_support p A S hsupp i)
    have he : ordinaryVertexCoordinates K e = A :=
      exposedCoordinateVertexEquiv_coordinates A hm hsingle
    have hh := incident_rank_density_of_actual_core K e (sumVertexCoordinates p)
      (by rw [he]; exact hplane) S hface hdense
    rw [he] at hh
    exact hh
  · have hm0 : m = 0 := by omega
    apply subset_closure
    refine ⟨?_, fun _ => rfl⟩
    intro j
    exact False.elim (by have := j.isLt; omega)

theorem actual_three_face_facetMask {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) :
    FacetMask (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  let f : FacetType P := ⟨⟨F.val.carrier, F.val.isFace⟩,
    F.val.isFace, by rw [F.property, hP]⟩
  have hrank := actualFaceLabels_rank P e F.val
  rw [F.property] at hrank
  refine ⟨?_, ⟨_, actualFacetLabels_strictSupport P e f⟩, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, subsetRank_empty] at hrank
    omega
  · omega

/-- Actual four-polytopes reduce to a core with exactly as many vertices
as nonsimplicial facets. Simplicial facets require no extra incidence rows. -/
theorem actual_polytope_density_of_small_facet_core {k : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ k)
    (hcores : ∀ K : ConvexPolytope 5, K.dim ≤ 4 → K.vertices.card ≤ k →
      RationallyApproximable K) : RationallyApproximable P := by
  let e : Fin (Fintype.card P.vertices) ≃ P.vertices := (Fintype.equivFin _).symm
  let m := Fintype.card (nonsimplicialFacets P)
  let f : Fin m ≃ nonsimplicialFacets P := (Fintype.equivFin _).symm
  let S := fun j : Fin m => actualFaceLabels P e (f j).val.val
  have hS (j : Fin m) : FacetMask (vertexCoordinates P e) (S j) :=
    actual_three_face_facetMask P hP e (f j).val
  have hSinj : Function.Injective S := by
    intro i j hij
    apply f.injective
    apply Subtype.ext
    apply Subtype.ext
    exact actualFaceLabels_injective P e hij
  have hcover : ∀ T ∈ facetMasks (vertexCoordinates P e),
      T.card ≤ 4 ∨ ∃ j, S j = T := by
    intro T hT
    by_cases hsmall : T.card ≤ 4
    · exact Or.inl hsmall
    obtain ⟨F, hF⟩ := facetMask_actual_three_face P e T
      ((mem_facetMasks _ T).mp hT)
    have hlarge : F ∈ nonsimplicialFacets P := by
      apply (mem_nonsimplicialFacets P F).mpr
      have hc := actualFaceLabels_card P e F.val
      rw [hF] at hc
      change 4 < Nat.card (VerticesOn P F.val.carrier)
      omega
    obtain ⟨j, hj⟩ := f.surjective ⟨F, hlarge⟩
    exact Or.inr ⟨j, by simpa only [S, hj] using hF⟩
  have hmk : m ≤ k := by simpa only [m, Fintype.card_coe] using hcount
  have hh := density_from_selected_facet_core (vertexCoordinates P e)
    (vertexCoordinates_spans P e hP) (fun _ => rfl) S hS hSinj hcover hmk hcores
  have ho := ordinary_density_of_homogeneous_density (ordinaryVertexCoordinates P e)
    (by simpa only [ordinaryVertexCoordinates_homogeneous] using hh)
  apply rationallyApproximable_of_coordinate_density P e
  apply closure_mono ?_ ho
  intro q hq
  exact ⟨hq.1, hq.2.2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/NineVertexRelationReduction.lean -/




@[expose] public section

/-!
# Geometric exclusion of the exceptional relation pattern on nine vertices

After simple vertices and small selected-facet cores are removed, the
actual relation matrix has either at most seven rows, a transpose-kernel
vector on at most three rows, or an omitted four-support in every family
of nine such supports. These are the exact inputs needed by the ordinary
and golden-omission matrix-density theorems.

This is a geometric reduction, not by itself the rational-density theorem.

-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open Papers.RationalityTen.ActualNineBipyramidExclusion

theorem nine_vertex_nine_excess_relation_reduction
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 9 ≃ P.vertices)
    (hn : P.vertices.card = 9)
    (hm : Nat.card (Face P 3) = 9 ∨ Nat.card (Face P 3) = 10)
    (hN : 9 ≤ (nonsimplicialFacets P).card) (hE : facetExcess P = 9)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v)
    (hc : 8 ≤ Fintype.card (SparseSharedRowIndex P e)) :
    Fintype.card (SparseSharedRowIndex P e) = 8 ∧
      OmitsEveryNineFourSupportFamily (actualSparseSharedMatrix P e) := by
  obtain ⟨_, hfacets, _⟩ := nine_nonsimplicial_facets_nine_excess P hN hE
  have hcount := actual_sparse_shared_count_of_card_le_five P hP e hfacets
  rw [hE] at hcount
  have hnonneg := polygonExcess_nonnegative P
  have hgsmall : polygonExcess P ≤ 1 := by omega
  have hgpos : 1 ≤ polygonExcess P := by
    by_contra h
    have hg0 : polygonExcess P = 0 := by omega
    rcases hm with hm9 | hm10
    · have hmin := all_facets_nonsimplicial_of_nine_and_nine P hm9 hN
      have hall (F : Face P 3) : Nat.card (VerticesOn P F.val.carrier) = 5 := by
        have hlo := hmin F
        have hhi := hfacets F
        change Nat.card (VerticesOn P F.val.carrier) ≤ 5 at hhi
        change 5 ≤ Nat.card (VerticesOn P F.val.carrier) at hlo
        omega
      exact no_nine_five_vertex_simplicial_facets P hP hn hm9 hall hg0 hnonsimple
    · have hp := actual_nine_vertex_nine_excess_positive_polygons P hP hn hm10 hE
      omega
  have hg1 : polygonExcess P = 1 := by omega
  have h8 : Fintype.card (SparseSharedRowIndex P e) = 8 := by omega
  refine ⟨h8, ?_⟩
  intro L hL hfour
  exact actual_single_quadrilateral_omits_four_support P hP e hfacets hE hg1 L hL hfour

theorem nine_vertex_selected_relation_obstruction_excluded
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 9 ≃ P.vertices)
    (hn : P.vertices.card = 9)
    (hN : 9 ≤ (nonsimplicialFacets P).card)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 7 ∨
      (Fintype.card (SparseSharedRowIndex P e) = 8 ∧
        ((∃ v : Fin (Fintype.card (SparseSharedRowIndex P e)) → ℝ,
          v ≠ 0 ∧ (actualSparseSharedMatrix P e).transpose.mulVec v = 0 ∧
            (vectorSupport v).card ≤ 3) ∨
          OmitsEveryNineFourSupportFamily (actualSparseSharedMatrix P e))) := by
  by_cases hsmall : Fintype.card (SparseSharedRowIndex P e) ≤ 7
  · exact Or.inl hsmall
  have hc : 8 ≤ Fintype.card (SparseSharedRowIndex P e) := by omega
  have hcold : 8 ≤ Fintype.card (ActualSharedRowIndex P e) := by
    rw [← sparseSharedRowIndex_card_eq]
    exact hc
  have hcardle := Finset.card_le_card (Finset.subset_univ (nonsimplicialFacets P))
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcardle
  have hm : 9 ≤ Nat.card (Face P 3) := by omega
  have hE := nonsimplicial_facets_card_le_excess P
  have hE9 : 9 ≤ facetExcess P := by omega
  rcases actual_nine_vertex_budget_trichotomy P hP e hn hm hE9 hcold with
      ⟨hm9, hE9⟩ | ⟨hm9, hE10⟩ | ⟨hm10, hE9⟩
  · obtain ⟨h8, homit⟩ := nine_vertex_nine_excess_relation_reduction P hP e hn
      (Or.inl hm9) hN hE9 hnonsimple hc
    exact Or.inr ⟨h8, Or.inr homit⟩
  · obtain ⟨F₀, hF₀, hother⟩ := nine_facets_ten_excess_unique_six P hm9 hN hE10
    rcases nine_vertex_one_six_facet_rows_or_sparse_left_kernel P hP e hn hm9 F₀ hF₀ hother with
        hseven | ⟨h8, hkernel⟩
    · exact Or.inl hseven
    · exact Or.inr ⟨h8, Or.inl hkernel⟩
  · obtain ⟨h8, homit⟩ := nine_vertex_nine_excess_relation_reduction P hP e hn
      (Or.inr hm10) hN hE9 hnonsimple hc
    exact Or.inr ⟨h8, Or.inr homit⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/SimpleVertexNineDensity.lean -/




@[expose] public section

/-!
# The simple-vertex branch through nine vertices

The complete simple-deletion theorem transfers actual rational density
from the at-most-eight-vertex core. This uses its density equivalence,
not merely its field-of-realization conclusion.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem actual_at_most_nine_vertices_with_simple_vertex_rationallyDense
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card ≤ 9)
    (v : VertexType P) (hs : IsSimpleVertex P v) : RationallyDense P := by
  by_cases hsmall : P.vertices.card ≤ 8
  · exact actual_polytope_at_most_eight_vertices_rationallyDense P hP hsmall
  have hcard : 4 + 1 < P.vertices.card := by omega
  obtain ⟨hne, hfull, _, _, hdensity⟩ := paper_simple_vertex_deletion 4 P v hP hcard hs
  apply hdensity.mpr
  apply actual_polytope_at_most_eight_vertices_rationallyDense _ hfull
  rw [deleteVertex_vertices, Finset.card_erase_of_mem v.property]
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/NineVertexDensityAssembly.lean -/





@[expose] public section

/-!
# Assembly of the actual nine-vertex density theorem

The ambient-dimension transport closes the small selected-facet-core branch
using only the already preceding eight-vertex result. The remaining actual
nine-vertex geometry is supplied by NineVertexRelationReduction.

The algebraic premise below is deliberately explicit. It is the final
eight-element classification and golden-omission input, to be supplied by
the separately checked chart theorem. None of the theorems in this file
with that premise is presented as an unconditional principal theorem.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Matrix
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem ambient_at_most_eight_vertices_rationallyApproximable {d : ℕ}
    (P : ConvexPolytope d) (hd : P.dim ≤ 4) (hn : P.vertices.card ≤ 8) :
    RationallyApproximable P :=
  ambient_dimension_le_four_of_full_four P hd hn
    actual_polytope_at_most_eight_vertices_approximable

theorem actual_at_most_eight_nonsimplicial_facets_rationallyApproximable
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 8) : RationallyApproximable P :=
  actual_polytope_density_of_small_facet_core P hP hcount
    (fun K hdim hcard => ambient_at_most_eight_vertices_rationallyApproximable K hdim hcard)

theorem actual_at_most_nine_vertices_approximable_of_exceptional_matrix_density
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card ≤ 9) :
    RationallyApproximable P := by
  by_cases hsmall : P.vertices.card ≤ 8
  · exact actual_polytope_at_most_eight_vertices_approximable P hP hsmall
  have hnine : P.vertices.card = 9 := by omega
  by_cases hsimple : ∃ v : VertexType P, IsSimpleVertex P v
  · obtain ⟨v, hv⟩ := hsimple
    exact (actual_at_most_nine_vertices_with_simple_vertex_rationallyDense
      P hP hn v hv).approximable
  push_neg at hsimple
  by_cases hcore : (nonsimplicialFacets P).card ≤ 8
  · exact actual_at_most_eight_nonsimplicial_facets_rationallyApproximable P hP hcore
  let e : Fin 9 ≃ P.vertices := (Finset.equivFinOfCardEq hnine).symm
  have hN : 9 ≤ (nonsimplicialFacets P).card := by omega
  apply rationallyApproximable_of_actualSparseSharedMatrix_density P hP e
  rcases nine_vertex_selected_relation_obstruction_excluded P hP e hnine hN hsimple with
      hseven | ⟨height, hcase⟩
  · exact rational_matrix_zero_pattern_rank_density_seven hseven (actualSparseSharedMatrix P e)
  · exact hmatrices _ (actualSparseSharedMatrix P e) height hcase

theorem actual_at_most_nine_vertices_rationallyDense_of_exceptional_matrix_density
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card ≤ 9) :
    RationallyDense P := by
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hQn : Q.vertices.card ≤ 9 := by
    rw [← faceOrderIso_vertex_card φ]
    exact hn
  exact actual_at_most_nine_vertices_approximable_of_exceptional_matrix_density
    hmatrices Q hQ hQn

theorem ambient_at_most_nine_vertices_of_exceptional_matrix_density {d : ℕ}
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope d) (hd : P.dim ≤ 4) (hn : P.vertices.card ≤ 9) :
    RationallyApproximable P :=
  ambient_dimension_le_four_of_full_four P hd hn
    (actual_at_most_nine_vertices_approximable_of_exceptional_matrix_density hmatrices)

theorem actual_at_most_nine_nonsimplicial_facets_of_exceptional_matrix_density
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 9) : RationallyApproximable P :=
  actual_polytope_density_of_small_facet_core P hP hcount
    (fun K hdim hcard =>
      ambient_at_most_nine_vertices_of_exceptional_matrix_density hmatrices K hdim hcard)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/EightRelationRowsAssembly.lean -/



@[expose] public section

/-!
# Eight shared relation rows in arbitrary four-polytopes

This is the geometric assembly of Appendix A.4. No bound on the number of
vertices is imposed. The finite rank-four classification is kept as an
explicit input until its separate proof is imported: it supplies density
or the four-entry lower bound on each active relation-matrix column.

The zero-polygon-excess branch uses an eight-vertex normal core. In the
positive-excess branch, the sparse relation rows leave at most nine active
columns, and actual retained-core approximation restores all other vertices.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget
open Papers.RationalityTen.SimplicialFiveFacetGeometry

theorem actual_sparse_shared_count_of_polygonExcess_zero {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (hg : polygonExcess P = 0) :
    (Fintype.card (SparseSharedRowIndex P e) : ℤ) = facetExcess P := by
  have hlocal (F : Face P 3) : actualPolygonRelationRank P e F = 0 := by
    apply (actualPolygonRelationRank_eq_zero_iff P e F).mpr
    exact facePolytope_polygonExcess_zero P hg F.val.isFace
  rw [sparseSharedRowIndex_card]
  simp only [sharedRelationCount, hg, hlocal, Nat.cast_zero,
    Finset.sum_const_zero, zero_add, sub_zero]

theorem actual_eight_sparse_rows_zero_polygon_excess {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hg : polygonExcess P = 0) : RationallyApproximable P := by
  apply actual_at_most_eight_nonsimplicial_facets_rationallyApproximable P hP
  have hcount := actual_sparse_shared_count_of_polygonExcess_zero P e hg
  have hselected := nonsimplicial_facets_card_le_excess P
  omega

/-- An empty active set causes no exceptional corner case: retain any one
actual vertex. Otherwise retain exactly the active columns. -/
theorem exists_nonempty_small_active_container {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (hne : Nonempty (Fin n))
    (hcard : (activeColumns C).card ≤ 9) :
    ∃ I : Finset (Fin n), I.Nonempty ∧ I.card ≤ 9 ∧ activeColumns C ⊆ I := by
  by_cases hactive : (activeColumns C).Nonempty
  · exact ⟨activeColumns C, hactive, hcard, Finset.Subset.refl _⟩
  · obtain ⟨i⟩ := hne
    have hz : activeColumns C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
    refine ⟨{i}, Finset.singleton_nonempty i, by simp, ?_⟩
    rw [hz]
    exact Finset.empty_subset _

theorem actual_density_of_at_most_nine_active_columns {c n : ℕ}
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (C : Matrix (Fin c) (Fin n) ℝ)
    (hrelations : ∀ S ∈ facetMasks (vertexCoordinates P e),
      supportedRowSpan C S = globalRelationSpace (vertexCoordinates P e) S)
    (hcard : (activeColumns C).card ≤ 9) : RationallyApproximable P := by
  have hne : Nonempty (Fin n) := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨e.symm ⟨v, hv⟩⟩
  obtain ⟨I, hI, hIcard, hactive⟩ := exists_nonempty_small_active_container C hne hcard
  have hzero (i : Fin c) (j : Fin n) (hj : j ∉ I) : C i j = 0 := by
    by_contra hentry
    apply hj
    exact hactive ((mem_activeColumns C j).mpr ⟨i, hentry⟩)
  let K := retainedVertexCore P e I hI
  have hKdim : K.dim ≤ 4 := by
    have hh : K.dim ≤ P.dim :=
      Submodule.finrank_mono (vectorSpan_mono ℝ (retainedVertexCore_body_subset P e I hI))
    exact hh.trans hP.le
  have hKcard : K.vertices.card ≤ 9 := by
    rw [retainedVertexCore_card]
    exact hIcard
  have hcore := ambient_at_most_nine_vertices_of_exceptional_matrix_density
    hmatrices K hKdim hKcard
  exact actual_zero_column_restoration P hP e C I hI hzero hrelations hcore

/-- Appendix A.4, with its separately developed finite classification
dependencies displayed explicitly. There is no vertex-count restriction. -/
theorem actual_polytope_eight_sparse_relations_of_classification {n : ℕ}
    (hnine : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8) : RationallyApproximable P := by
  by_cases hg : polygonExcess P = 0
  · exact actual_eight_sparse_rows_zero_polygon_excess P hP e hc hg
  have hgpos : 0 < polygonExcess P := by
    have hnonneg := polygonExcess_nonnegative P
    omega
  rcases hclassification _ _ (actualSparseSharedMatrix P e) hc with hdense | hfour
  · exact rationallyApproximable_of_actualSparseSharedMatrix_density P hP e hdense
  · apply actual_density_of_at_most_nine_active_columns hnine P hP e
      (actualSparseSharedMatrix P e)
    · intro S hS
      obtain ⟨F, hF⟩ := facetMask_actual_three_face P e S ((mem_facetMasks _ S).mp hS)
      rw [← hF]
      exact actualSparseSharedMatrix_span_facet P e F
    · exact actualSparseSharedMatrix_at_most_nine_active_columns P e hc hgpos hfour

theorem actual_polytope_eight_shared_relations_of_classification {n : ℕ}
    (hnine : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (ActualSharedRowIndex P e) ≤ 8) : RationallyApproximable P := by
  apply actual_polytope_eight_sparse_relations_of_classification hnine hclassification P hP e
  simpa only [sparseSharedRowIndex_card_eq] using hc

theorem actual_high_facet_count_density_of_classification {n : ℕ}
    (hnine : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hE : 10 ≤ facetExcess P)
    (hm : 17 ≤ Nat.card (Face P 3)) : RationallyApproximable P :=
  actual_polytope_eight_sparse_relations_of_classification hnine hclassification P hP e
    (actualSparseSharedRowIndex_le_eight_of_high_facet_count P hP e hn hE hm)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8
