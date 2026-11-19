module
public import Papers.ActualGaleRanks
public import Papers.FiniteProjectionBoundary
public import GaleSevenObstruction

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: GaleBoundaryRankWitness.lean -/





@[expose] public section

/-!
# Actual facial witnesses for full complementary rank

Two finite witnesses suffice for Appendix B.8. A whole facet together with
an outside vertex has homogeneous rank five. Alternatively, three vertices
of an actual triangular two-face, a fourth vertex of a containing facet,
and a vertex outside that facet have rank five. The supporting hyperplanes
justify both rank increases; generic-position assumptions are unnecessary.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.GaleBoundaryRankWitness

open Set Finset Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open ActualGale FiniteProjection

inductive RankFiveCertificate (B : Boundary 9) (T : Finset (Fin 10)) : Prop
  | facetOutside (F : B.facets) (v : Fin 10) (hout : v ∉ F.val)
      (hsub : insert v F.val ⊆ T)
  | triangleFacet (R : B.polygons) (hR : R.val.card = 3)
      (u : Fin 10) (hu : u ∉ R.val) (F : B.facets)
      (hRF : R.val ⊆ F.val) (huF : u ∈ F.val)
      (v : Fin 10) (hv : v ∉ F.val)
      (hsub : insert v (insert u R.val) ⊆ T)

theorem actual_facet_dimension (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (F : FacetType P) : faceDim F.val.val = 3 := by
  have h := F.property.2
  rw [hP] at h
  omega

theorem actual_facet_labels_rank (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : Fin 10 ≃ VertexType P) (F : FacetType P) :
    subsetRank (vertexCoordinates P lab) (FiniteProjection.faceLabels P lab F.val) = 4 := by
  rw [FiniteProjection.faceLabels, actualFaceLabels_rank]
  have h := actual_facet_dimension P hP F
  simpa only [h] using (show faceDim F.val.val + 1 = 4 by omega)

theorem RankFiveCertificate.sound {B : Boundary 9} {T : Finset (Fin 10)}
    (C : RankFiveCertificate B T) (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : Fin 10 ≃ VertexType P) (hB : RealizesBoundary P lab B) :
    subsetRank (vertexCoordinates P lab) T = 5 := by
  apply Nat.le_antisymm (rank_le_ambient _ T)
  cases C with
  | facetOutside F v hout hsub =>
    let FF : PolytopeFace P := ⟨(hB.facetFor F).val.val, (hB.facetFor F).val.property⟩
    have hlabels : actualFaceLabels P lab FF = F.val := hB.facetFor_labels F
    have hrank : subsetRank (vertexCoordinates P lab) (insert v F.val) = 5 := by
      rw [← hlabels]
      rw [actual_face_rank_insert P lab FF v (by simpa only [hlabels] using hout)]
      have hd := actual_facet_dimension P hP (hB.facetFor F)
      change faceDim (hB.facetFor F).val.val + 2 = 5
      omega
    have hle := rank_mono (vertexCoordinates P lab) hsub
    rw [hrank] at hle
    exact hle
  | triangleFacet R hR u hu F hRF huF v hv hsub =>
    let RR := hB.polygonFor R
    let FF : PolytopeFace P := ⟨(hB.facetFor F).val.val, (hB.facetFor F).val.property⟩
    have hRlabels : actualFaceLabels P lab RR.val = R.val := hB.polygonFor_labels R
    have hFlabels : actualFaceLabels P lab FF = F.val := hB.facetFor_labels F
    have hrankR : subsetRank (vertexCoordinates P lab) R.val = 3 := by
      rw [← hRlabels, actualFaceLabels_rank, RR.property]
    have hu_not : vertexCoordinates P lab u ∉ labelSpan (vertexCoordinates P lab) R.val :=
      outside_actual_face_notMem P lab RR.val R.val
        (by rw [hRlabels]) u (by simpa only [hRlabels] using hu)
    have hrank4 : subsetRank (vertexCoordinates P lab) (insert u R.val) = 4 := by
      rw [rank_insert_of_notMem _ _ _ hu_not, hrankR]
    have hsubF : insert u R.val ⊆ actualFaceLabels P lab FF := by
      rw [hFlabels]
      exact Finset.insert_subset huF hRF
    have hv_not : vertexCoordinates P lab v ∉
        labelSpan (vertexCoordinates P lab) (insert u R.val) :=
      outside_actual_face_notMem P lab FF _ hsubF v
        (by simpa only [hFlabels] using hv)
    have hrank5 : subsetRank (vertexCoordinates P lab) (insert v (insert u R.val)) = 5 := by
      rw [rank_insert_of_notMem _ _ _ hv_not, hrank4]
    have hle := rank_mono (vertexCoordinates P lab) hsub
    rw [hrank5] at hle
    exact hle

/-- The rank of the image of any independent indexed family is its index
cardinality. The statement remains correct without separately assuming
that the label map is injective. -/
theorem rank_image_of_independent {n r k : ℕ} (p : Fin n → Fin r → ℝ)
    (b : Fin k → Fin n) (h : LinearIndependent ℝ (p ∘ b)) :
    subsetRank p (Finset.univ.image b) = k := by
  unfold subsetRank
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  simpa only [Fintype.card_fin] using finrank_span_eq_card h

end Papers.RationalityTen.ChirotopeDensity.GaleBoundaryRankWitness

end
end
end BundlePart0

section BundlePart1
/- Source: GaleBoundaryObstruction.lean -/





@[expose] public section

/-!
# Soundness of finite facial certificates for the Gale obstruction

The certificate contains only actual face masks and finite containment
checks. The Gale configuration is constructed from the kernel of the
homogeneous vertex matrix. Complementary-rank duality proves all four-set
and triple independence facts and all seven hyperplane incidences.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.GaleBoundaryObstruction

open Set Finset Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open ActualGale FiniteProjection GaleBoundaryRankWitness
open Papers.RationalityTen.GaleSevenFrame

def labelsOf {k : ℕ} (σ : Equiv.Perm (Fin 10)) (b : Fin k → Fin 10) :
    Finset (Fin 10) := Finset.univ.image (σ ∘ b)

theorem labelsOf_card {k : ℕ} (σ : Equiv.Perm (Fin 10)) (b : Fin k → Fin 10)
    (hb : Function.Injective b) : (labelsOf σ b).card = k := by
  rw [labelsOf, Finset.card_image_of_injective _ (σ.injective.comp hb), Finset.card_univ,
    Fintype.card_fin]

structure Certificate (B : Boundary 9) where
  labels : Equiv.Perm (Fin 10)
  quadrilateral : B.polygons
  quadrilateral_card : quadrilateral.val.card = 4
  quadrilateral_labels : ∀ i : Fin 10, labels i ∈ quadrilateral.val ↔ 6 ≤ i.val
  four_rank : ∀ i : Fin 4, RankFiveCertificate B (labelsOf labels (fourSets i))ᶜ
  triple_rank : ∀ i : Fin 3, RankFiveCertificate B (labelsOf labels (tripleSets i))ᶜ
  hyperplane_facet : ∀ i : Fin 7, (labelsOf labels (hyperplanes i))ᶜ ∈ B.facets

theorem Certificate.four_independent {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) (G : Coordinates P lab) (i : Fin 4) :
    LinearIndependent ℝ ((G.vectors ∘ C.labels) ∘ fourSets i) := by
  have hprimal := (C.four_rank i).sound P hP lab hB
  have hrank := G.rank_eq_of_primal_complement_rank (labelsOf C.labels (fourSets i)) hprimal
  rw [labelsOf_card C.labels _ (fourSets_injective i)] at hrank
  exact independent_of_rank G.vectors (C.labels ∘ fourSets i) hrank

theorem Certificate.three_independent {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) (G : Coordinates P lab) (i : Fin 3) :
    LinearIndependent ℝ ((G.vectors ∘ C.labels) ∘ tripleSets i) := by
  have hprimal := (C.triple_rank i).sound P hP lab hB
  have hrank := G.rank_eq_of_primal_complement_rank (labelsOf C.labels (tripleSets i)) hprimal
  rw [labelsOf_card C.labels _ (tripleSets_injective i)] at hrank
  exact independent_of_rank G.vectors (C.labels ∘ tripleSets i) hrank

theorem Certificate.hyperplane_dependent {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) (G : Coordinates P lab) (i : Fin 7) :
    ¬ LinearIndependent ℝ ((G.vectors ∘ C.labels) ∘ hyperplanes i) := by
  let S := labelsOf C.labels (hyperplanes i)
  let F : B.facets := ⟨Sᶜ, C.hyperplane_facet i⟩
  have hprimal : subsetRank (vertexCoordinates P lab) Sᶜ = 4 := by
    change subsetRank (vertexCoordinates P lab) F.val = 4
    rw [← hB.facetFor_labels F]
    exact actual_facet_labels_rank P hP lab (hB.facetFor F)
  have hcard : S.card = 5 := labelsOf_card C.labels _ (hyperplanes_injective i)
  have hcompcard : Sᶜ.card = 5 := by
    have hc := Finset.card_compl S
    rw [hcard, Fintype.card_fin] at hc
    exact hc
  have hrank := G.complementary_rank Sᶜ
  rw [hprimal, hcompcard, compl_compl] at hrank
  intro hli
  have hfull := rank_image_of_independent G.vectors (C.labels ∘ hyperplanes i) hli
  change subsetRank G.vectors S = 5 at hfull
  omega

/-- The certificate's distinguished hyperplane is exactly the span used
by the common obstruction, rather than merely a containing subspace. -/
theorem Certificate.plane_eq {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) (G : Coordinates P lab) :
    plane (G.vectors ∘ C.labels) = labelSpan G.vectors C.quadrilateral.valᶜ := by
  have hle : plane (G.vectors ∘ C.labels) ≤ labelSpan G.vectors C.quadrilateral.valᶜ := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨C.labels (fourSets 1 i), ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_compl, C.quadrilateral_labels]
    fin_cases i <;> decide
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hleft : finrank ℝ (plane (G.vectors ∘ C.labels)) = 4 := by
    change finrank ℝ (Submodule.span ℝ
      (Set.range ((G.vectors ∘ C.labels) ∘ fourSets 1))) = 4
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card (C.four_independent P hP lab hB G 1)
  have hQ := G.quadrilateral_rank (hB.polygonFor C.quadrilateral)
    (by rw [hB.polygonFor_labels]; exact C.quadrilateral_card)
  rw [hB.polygonFor_labels] at hQ
  exact hleft.trans hQ.symm

theorem Certificate.conditions {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) (G : Coordinates P lab) :
    Conditions (G.vectors ∘ C.labels) := by
  have hplane := C.plane_eq P hP lab hB G
  refine ⟨?_, ?_, ?_, C.four_independent P hP lab hB G,
    C.three_independent P hP lab hB G, C.hyperplane_dependent P hP lab hB G⟩
  · rw [hplane]
    apply Submodule.subset_span
    refine ⟨C.labels 0, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_compl, C.quadrilateral_labels]
    decide
  · rw [hplane]
    apply Submodule.subset_span
    refine ⟨C.labels 5, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_compl, C.quadrilateral_labels]
    decide
  · intro i
    let j : Fin 10 := ⟨6 + i.val, by omega⟩
    have hj : C.labels j ∈ C.quadrilateral.val :=
      (C.quadrilateral_labels j).mpr (by dsimp [j]; omega)
    have ho := G.outside_quadrilateral_hyperplane (hB.polygonFor C.quadrilateral)
      (by rw [hB.polygonFor_labels]; exact C.quadrilateral_card)
      (C.labels j) (by rw [hB.polygonFor_labels]; exact hj)
    rw [hB.polygonFor_labels, ← hplane] at ho
    exact ho

/-- A checked finite certificate excludes every actual realization of its
complete boundary, with no extra algebraic or genericity assumption. -/
theorem Certificate.not_realizable {B : Boundary 9} (C : Certificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (lab : Fin 10 ≃ VertexType P)
    (hB : RealizesBoundary P lab B) : False := by
  obtain ⟨G⟩ := coordinates_exist P lab hP
  exact seven_hyperplane_obstruction (G.vectors ∘ C.labels) (C.conditions P hP lab hB G)

end Papers.RationalityTen.ChirotopeDensity.GaleBoundaryObstruction

end
end
end BundlePart1

section BundlePart2
/- Source: GaleType31.lean -/




@[expose] public section

/-!
## Appendix B.8: type 31

The boundary and every rank witness below are literal finite data.
`not_realizable` excludes every full-dimensional real four-polytope
with these complete facet and polygon families.
-/

namespace Papers.RationalityTen.ChirotopeDensity.GaleType31

open FiniteProjection GaleBoundaryRankWitness GaleBoundaryObstruction
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

def boundary : Boundary 9 where
  facets := {{1, 4, 5, 7}, {2, 4, 5, 6, 7}, {2, 3, 4, 8}, {1, 2, 4, 5, 8}, {0, 3, 6, 8}, {2, 3, 5, 6, 8}, {0, 3, 7, 8}, {1, 3, 4, 7, 8}, {2, 3, 4, 9}, {0, 2, 3, 6, 9}, {0, 3, 4, 7, 9}, {2, 4, 6, 7, 9}, {1, 5, 6, 7, 9}, {1, 5, 8, 9}, {0, 5, 6, 8, 9}, {0, 1, 7, 8, 9}}
  polygons := {{2, 3, 4}, {1, 4, 5}, {2, 4, 5}, {0, 3, 6}, {2, 3, 6}, {2, 5, 6}, {0, 3, 7}, {1, 4, 7}, {3, 4, 7}, {1, 5, 7}, {4, 5, 7}, {2, 4, 6, 7}, {5, 6, 7}, {0, 3, 8}, {2, 3, 8}, {1, 4, 8}, {2, 4, 8}, {3, 4, 8}, {1, 5, 8}, {2, 5, 8}, {0, 6, 8}, {3, 6, 8}, {5, 6, 8}, {0, 7, 8}, {1, 7, 8}, {3, 7, 8}, {0, 3, 9}, {2, 3, 9}, {2, 4, 9}, {3, 4, 9}, {1, 5, 9}, {0, 6, 9}, {2, 6, 9}, {5, 6, 9}, {0, 7, 9}, {1, 7, 9}, {4, 7, 9}, {6, 7, 9}, {0, 8, 9}, {1, 8, 9}, {5, 8, 9}}

def letterLabels : Equiv.Perm (Fin 10) where
  toFun := ![0, 1, 5, 8, 3, 9, 7, 4, 6, 2]
  invFun := ![0, 1, 9, 4, 7, 2, 8, 6, 3, 5]
  left_inv := by decide
  right_inv := by decide

def certificate : Certificate boundary where
  labels := letterLabels
  quadrilateral := ⟨{2, 4, 6, 7}, by decide⟩
  quadrilateral_card := by decide
  quadrilateral_labels := by decide
  four_rank := by
    intro i
    fin_cases i
    · exact .triangleFacet ⟨{2, 3, 6}, by decide⟩ (by decide) 9 (by decide)
        ⟨{0, 2, 3, 6, 9}, by decide⟩ (by decide) (by decide) 4 (by decide) (by decide)
    · exact .triangleFacet ⟨{0, 6, 9}, by decide⟩ (by decide) 2 (by decide)
        ⟨{0, 2, 3, 6, 9}, by decide⟩ (by decide) (by decide) 4 (by decide) (by decide)
    · exact .triangleFacet ⟨{2, 3, 6}, by decide⟩ (by decide) 8 (by decide)
        ⟨{2, 3, 5, 6, 8}, by decide⟩ (by decide) (by decide) 4 (by decide) (by decide)
    · exact .triangleFacet ⟨{1, 4, 5}, by decide⟩ (by decide) 2 (by decide)
        ⟨{1, 2, 4, 5, 8}, by decide⟩ (by decide) (by decide) 6 (by decide) (by decide)
  triple_rank := by
    intro i
    fin_cases i
    · exact .facetOutside ⟨{0, 2, 3, 6, 9}, by decide⟩ 5 (by decide) (by decide)
    · exact .facetOutside ⟨{1, 3, 4, 7, 8}, by decide⟩ 0 (by decide) (by decide)
    · exact .facetOutside ⟨{0, 1, 7, 8, 9}, by decide⟩ 5 (by decide) (by decide)
  hyperplane_facet := by decide

theorem not_realizable (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : Fin 10 ≃ VertexType P) (hB : RealizesBoundary P lab boundary) : False :=
  certificate.not_realizable P hP lab hB

end Papers.RationalityTen.ChirotopeDensity.GaleType31

end
end BundlePart2

section BundlePart3
/- Source: GaleType32.lean -/




@[expose] public section

/-!
## Appendix B.8: type 32

The boundary and every rank witness below are literal finite data.
`not_realizable` excludes every full-dimensional real four-polytope
with these complete facet and polygon families.
-/

namespace Papers.RationalityTen.ChirotopeDensity.GaleType32

open FiniteProjection GaleBoundaryRankWitness GaleBoundaryObstruction
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

def boundary : Boundary 9 where
  facets := {{2, 3, 6, 7}, {1, 3, 5, 6, 7}, {0, 4, 5, 8}, {1, 2, 3, 6, 8}, {2, 4, 6, 8}, {1, 4, 5, 6, 8}, {0, 4, 7, 8}, {2, 3, 4, 7, 8}, {2, 4, 6, 9}, {0, 4, 5, 6, 9}, {0, 2, 4, 7, 9}, {1, 3, 5, 7, 9}, {2, 5, 6, 7, 9}, {1, 3, 8, 9}, {0, 1, 5, 8, 9}, {0, 3, 7, 8, 9}}
  polygons := {{0, 4, 5}, {1, 3, 6}, {2, 3, 6}, {2, 4, 6}, {1, 5, 6}, {4, 5, 6}, {2, 3, 7}, {0, 4, 7}, {2, 4, 7}, {1, 3, 5, 7}, {2, 6, 7}, {3, 6, 7}, {5, 6, 7}, {1, 3, 8}, {2, 3, 8}, {0, 4, 8}, {2, 4, 8}, {0, 5, 8}, {1, 5, 8}, {4, 5, 8}, {1, 6, 8}, {2, 6, 8}, {4, 6, 8}, {0, 7, 8}, {3, 7, 8}, {4, 7, 8}, {1, 3, 9}, {0, 4, 9}, {2, 4, 9}, {0, 5, 9}, {1, 5, 9}, {2, 6, 9}, {4, 6, 9}, {5, 6, 9}, {0, 7, 9}, {2, 7, 9}, {3, 7, 9}, {5, 7, 9}, {0, 8, 9}, {1, 8, 9}, {3, 8, 9}}

def letterLabels : Equiv.Perm (Fin 10) where
  toFun := ![0, 2, 6, 4, 8, 9, 7, 3, 5, 1]
  invFun := ![0, 9, 1, 7, 3, 8, 2, 6, 4, 5]
  left_inv := by decide
  right_inv := by decide

def certificate : Certificate boundary where
  labels := letterLabels
  quadrilateral := ⟨{1, 3, 5, 7}, by decide⟩
  quadrilateral_card := by decide
  quadrilateral_labels := by decide
  four_rank := by
    intro i
    fin_cases i
    · exact .triangleFacet ⟨{1, 5, 8}, by decide⟩ (by decide) 9 (by decide)
        ⟨{0, 1, 5, 8, 9}, by decide⟩ (by decide) (by decide) 3 (by decide) (by decide)
    · exact .triangleFacet ⟨{0, 5, 9}, by decide⟩ (by decide) 1 (by decide)
        ⟨{0, 1, 5, 8, 9}, by decide⟩ (by decide) (by decide) 3 (by decide) (by decide)
    · exact .triangleFacet ⟨{1, 5, 8}, by decide⟩ (by decide) 4 (by decide)
        ⟨{1, 4, 5, 6, 8}, by decide⟩ (by decide) (by decide) 3 (by decide) (by decide)
    · exact .triangleFacet ⟨{1, 3, 6}, by decide⟩ (by decide) 2 (by decide)
        ⟨{1, 2, 3, 6, 8}, by decide⟩ (by decide) (by decide) 5 (by decide) (by decide)
  triple_rank := by
    intro i
    fin_cases i
    · exact .facetOutside ⟨{0, 4, 5, 6, 9}, by decide⟩ 1 (by decide) (by decide)
    · exact .facetOutside ⟨{0, 2, 4, 7, 9}, by decide⟩ 3 (by decide) (by decide)
    · exact .facetOutside ⟨{0, 2, 4, 7, 9}, by decide⟩ 5 (by decide) (by decide)
  hyperplane_facet := by decide

theorem not_realizable (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : Fin 10 ≃ VertexType P) (hB : RealizesBoundary P lab boundary) : False :=
  certificate.not_realizable P hP lab hB

end Papers.RationalityTen.ChirotopeDensity.GaleType32

end
end BundlePart3
