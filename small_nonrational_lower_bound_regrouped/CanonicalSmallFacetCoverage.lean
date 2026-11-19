module
public import SmallFacetUniverseCanonicalS4T0
public import SmallFacetUniverseCanonicalS5T0
public import SmallFacetUniverseCanonicalS5T1
public import RootedKindedActualEncoding
public import RootedSmallCache

@[expose] public section

/-!
# Actual coverage of the complete rooted small-facet universe

The three canonical placement theorems cover every tetrahedron, triangular
bipyramid and square pyramid compatible with the distinguished bipyramid.
Their conclusions preserve the literal kind as well as every vertex, edge
and polygon face. Consequently the actual facet assignment supplies exact
quotas without an additional table of kind-identification assumptions.
-/

noncomputable section
namespace Papers.RationalityTen.CanonicalSmallFacetCoverage

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualSmallFacetClassification ActualFacetCatalogueTransport
open MatroidChecked.FacetBoundaryEncoding CellFacetInvariants
open LiteralMaskGeometry RawFacetEmbeddingSemantics
open RootedCanonical.SmallFacetUniverse

private theorem face_vertex_card {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) :
    (facePolytope P F.val.isFace).vertices.card = facetVertexCount P F := by
  simpa only [facetVertexCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm

private theorem face_dimension {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) : (facePolytope P F.val.isFace).dim = 3 := by
  change faceDim (facePolytope P F.val.isFace).toSet = 3
  rw [facePolytope_toSet]
  exact F.property

/-- The canonical local bipyramid has missing edge `{2,4}`, whereas the
rooted ten-label universe has missing edge `{3,4}`. -/
def rootEmbedding : Fin 5 ↪ Fin 10 where
  toFun := ![0, 1, 3, 2, 4]
  inj' := by decide +kernel

theorem root_exact :
    mapCell rootEmbedding (cellOfBoundary (FiniteCycleCandidates.N5.templates 0)) =
      decodeCell (FacetUniverses.Small.cells FacetUniverses.Small.root) := by
  apply cell_ext <;> decide +kernel

private theorem five_excess : ∀ i : Fin 2,
    cellExcess (cellOfBoundary (FiniteCycleCandidates.N5.templates i)) =
      if i = 0 then 0 else 1 := by
  decide +kernel

theorem bipyramid_template {d : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (F : Face P 3)
    (hF : facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0) :
    ∃ loc : (facePolytope P F.val.isFace).vertices ≃ Fin 5,
      polygonBoundary (facePolytope P F.val.isFace) loc =
        FiniteCycleCandidates.N5.templates 0 := by
  obtain ⟨loc, i, hi⟩ := five_vertex_classification (facePolytope P F.val.isFace)
    (face_dimension P F) ((face_vertex_card P F).trans hF.1)
  have hcell := actualCell_of_template P lab F loc
    (FiniteCycleCandidates.N5.templates i) hi
  have hg := congrArg cellExcess hcell
  rw [actualCell_excess, mapCell_excess, hF.2, five_excess] at hg
  have hi0 : i = 0 := by split_ifs at hg <;> simp_all
  exact ⟨loc, hi0 ▸ hi⟩

/-- The finite candidate kind is the actual intrinsic small-facet kind. -/
theorem covers_other_facet {d : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (G : Face P 3)
    (hG : facetVertexCount P G ≤ 5)
    (hcompat : (actualCell P lab G).Compatible
      (decodeCell (FacetUniverses.Small.cells FacetUniverses.Small.root))) :
    ∃ i, (FacetUniverses.Small.cells i).kind =
        RootedSmallFacetCoverage.smallKind (actualCell P lab G) ∧
      decodeCell (FacetUniverses.Small.cells i) = actualCell P lab G := by
  have hmin : 4 ≤ facetVertexCount P G :=
    Nat.succ_le_iff.mpr
      (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 G)
  have hcases : facetVertexCount P G = 4 ∨ facetVertexCount P G = 5 := by omega
  rcases hcases with h4 | h5
  · obtain ⟨loc, i, hi⟩ := four_vertex_classification (facePolytope P G.val.isFace)
      (face_dimension P G) ((face_vertex_card P G).trans h4)
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    have hcell := actualCell_of_template P lab G loc
      (FiniteCycleCandidates.N4.templates 0) hi
    obtain ⟨j, hk, hj⟩ := S4T0.covers_exact
      (ActualFaceTransport.labelEmbedding P lab G loc) (by
        simpa only [S4T0.localCell, S4T0.root, FacetUniverses.Small.root, ← hcell]
          using hcompat)
    refine ⟨j, ?_, hj.trans hcell.symm⟩
    simpa [RootedSmallFacetCoverage.smallKind, actualCell_vertex_card, h4,
      S4T0.template] using hk
  · obtain ⟨loc, i, hi⟩ := five_vertex_classification (facePolytope P G.val.isFace)
      (face_dimension P G) ((face_vertex_card P G).trans h5)
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · have hcell := actualCell_of_template P lab G loc
        (FiniteCycleCandidates.N5.templates 0) hi
      have hg := congrArg cellExcess hcell
      rw [actualCell_excess, mapCell_excess, five_excess] at hg
      have hg0 : facetPolygonExcess P G = 0 := by simpa only [ite_true] using hg
      obtain ⟨j, hk, hj⟩ := S5T0.covers_exact
        (ActualFaceTransport.labelEmbedding P lab G loc) (by
          simpa only [S5T0.localCell, S5T0.root, FacetUniverses.Small.root, ← hcell]
            using hcompat)
      refine ⟨j, ?_, hj.trans hcell.symm⟩
      simpa [RootedSmallFacetCoverage.smallKind, actualCell_vertex_card,
        actualCell_excess, h5, hg0, S5T0.template] using hk
    · have hcell := actualCell_of_template P lab G loc
        (FiniteCycleCandidates.N5.templates 1) hi
      have hg := congrArg cellExcess hcell
      rw [actualCell_excess, mapCell_excess, five_excess] at hg
      have hg1 : facetPolygonExcess P G = 1 := by
        simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hg
      obtain ⟨j, hk, hj⟩ := S5T1.covers_exact
        (ActualFaceTransport.labelEmbedding P lab G loc) (by
          simpa only [S5T1.localCell, S5T1.root, FacetUniverses.Small.root, ← hcell]
            using hcompat)
      refine ⟨j, ?_, hj.trans hcell.symm⟩
      simpa [RootedSmallFacetCoverage.smallKind, actualCell_vertex_card,
        actualCell_excess, h5, hg1, S5T1.template] using hk

/-- The exact kind-preserving coverage gives a complete genuine boundary,
with the distinguished actual bipyramid forced to candidate zero. -/
theorem rooted_encoding {d : Nat} (P : ConvexPolytope d)
    (lab₀ : P.vertices ≃ Fin 10)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (F : Face P 3)
    (hF : facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0) :
    ∃ lab : P.vertices ≃ Fin 10,
      ∃ E : Encoding P lab (fun i => decodeCell (FacetUniverses.Small.cells i)),
        E.index F = FacetUniverses.Small.root ∧
        ∀ G, (FacetUniverses.Small.cells (E.index G)).kind =
          SmallFacetTargetBudgets.partitionKind (nonsimplicialFacets P)
            (SmallFacetTargetBudgets.squareFacets P) F G := by
  obtain ⟨loc, hloc⟩ := bipyramid_template P lab₀ F hF
  obtain ⟨lab, hlab⟩ := ActualGrowthTarget.normalize_facet_template_to_embedding
    P lab₀ F loc _ hloc rootEmbedding
  rw [root_exact] at hlab
  let tag := SmallFacetTargetBudgets.partitionKind (nonsimplicialFacets P)
    (SmallFacetTargetBudgets.squareFacets P) F
  have hrootKind : (FacetUniverses.Small.cells FacetUniverses.Small.root).kind = tag F := by
    change 0 = if F = F then 0 else _
    simp only [ite_true]
  refine ⟨lab, ?_⟩
  apply RootedKindedActualEncoding.encoding_with_kinds P lab FacetUniverses.Small.cells
    F FacetUniverses.Small.root tag hlab.symm hrootKind
  intro G
  by_cases hGF : G = F
  · subst G
    exact ⟨FacetUniverses.Small.root, hrootKind, hlab.symm⟩
  obtain ⟨i, hk, hi⟩ := covers_other_facet P lab G (hfacets G) (by
    rw [← hlab]
    exact actualCell_compatible P lab G F hGF)
  refine ⟨i, hk.trans ?_, hi⟩
  simp only [RootedSmallFacetCoverage.smallKind, actualCell_vertex_card,
    actualCell_excess, tag, SmallFacetTargetBudgets.partitionKind, if_neg hGF,
    mem_nonsimplicialFacets, SmallFacetTargetBudgets.squareFacets,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem cells_wellFormed (i : Fin FacetUniverses.Small.cellCount) :
    WellFormed (FacetUniverses.Small.cells i) :=
  wellFormed_of_check _ (RootedSmallCache.well_formed i)

/-- An arbitrary actual residual with small facets supplies the exact rooted
growth target, exact counts for every kind, and inclusion of the root. -/
theorem actual_small_facet_growth_target (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ∃ lab : P.vertices ≃ Fin 10,
      ∃ E : Encoding P lab (fun i => decodeCell (FacetUniverses.Small.cells i)),
        GrowthRenaming.Target
          (fun a => SparseGrowthDAG.has (FacetUniverses.Small.ridgeList a))
          FacetUniverses.Small.literalCompatible FacetUniverses.Small.kind
          (SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
            (nonsimplicialFacets P).card (quadrilateralFaces P).card) E.family.toList ∧
        (∀ k, (E.family.filter fun a => (FacetUniverses.Small.cells a).kind = k).card =
          SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
            (nonsimplicialFacets P).card (quadrilateralFaces P).card k) ∧
        GrowthDAG.Included (SparseGrowthDAG.family [FacetUniverses.Small.root])
          (SparseGrowthDAG.family E.family.toList) := by
  obtain ⟨F, hF⟩ := SmallFacetTargetBudgets.actual_bipyramid_root P hP e hn hN hc hfacets
  obtain ⟨lab, E, hroot, hkinds⟩ := rooted_encoding P e.symm hfacets F hF
  obtain ⟨htarget, hcounts⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    FacetUniverses.Small.cells E hP cells_wellFormed
    (SmallFacetTargetBudgets.partitionKind (nonsimplicialFacets P)
      (SmallFacetTargetBudgets.squareFacets P) F) hkinds
    (SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
      (nonsimplicialFacets P).card (quadrilateralFaces P).card)
    (SmallFacetTargetBudgets.actual_rooted_quota_counts P hP hfacets F hF)
  exact ⟨lab, E, htarget, hcounts,
    ActualGrowthTarget.actual_root_included E F _ hroot⟩

end Papers.RationalityTen.CanonicalSmallFacetCoverage
