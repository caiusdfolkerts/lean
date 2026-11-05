module
public import TenGraphTriangleSemantics
public import ActualComplementGraph
public import MatroidChecked.BoundaryTriangleCount
public import ActualSmallFacetClassification
public import CellFacetInvariants

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: ActualGraphTriangleCount.lean -/






@[expose] public section

/-!
# The actual graph's raw triangle count

The complement mask below is defined from the complete actual edge set.
The triangle codec therefore gives equality of counts. The second theorem
transports the geometric lower bound to exactly the raw counter used by
the finite graph certificates.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGraphTriangleCount

open Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open MatroidChecked.FacetBoundaryEncoding MatroidChecked.BoundaryTriangleCount
open LiteralMaskGeometry ActualFacetInducedGraph ActualComplementGraph
open TenGraphEdges TenGraphTriangleSemantics

def complementMask (edges : Finset ℕ) : ℕ :=
  GrowthBitsets.ofList (complementEdges edges).toList

theorem complementMask_false_iff (edges : Finset ℕ) (e : Fin 45) :
    (complementMask edges).testBit e.val = false ↔ edgeMask e ∈ edges := by
  have htrue : (complementMask edges).testBit e.val = true ↔ edgeMask e ∉ edges := by
    rw [complementMask, ← GrowthBitsets.bitAt_eq_testBit, GrowthBitsets.bitAt_ofList,
      Finset.mem_toList, mem_complementEdges]
  rw [Bool.eq_false_iff, ne_eq, htrue, not_not]

theorem raw_edge_mem_image_iff (edges : Finset ℕ)
    (hbound : ∀ m ∈ edges, m < 1024) (e : Fin 45) :
    maskSet (edgeMask e) ∈ edges.image maskSet ↔ edgeMask e ∈ edges := by
  constructor
  · intro h
    obtain ⟨m, hm, hme⟩ := Finset.mem_image.mp h
    exact maskSet_injective (hbound m hm) (edgeMask_lt e) hme ▸ hm
  · exact Finset.mem_image_of_mem _

/-- Exact equality with the ordinary graph triangles of any faithfully
encoded actual boundary; no restriction on its facet templates is used. -/
theorem actual_triangle_count {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) :
    TenGraphTriangles.count (complementMask (literalGraphEdges cells E.family)) =
      (graphTriangles (E.family.biUnion fun i => (decodeCell (cells i)).edges)).card := by
  have hbits (e : Fin 45) :
      (complementMask (literalGraphEdges cells E.family)).testBit e.val = false ↔
        maskSet (edgeMask e) ∈ (literalGraphEdges cells E.family).image maskSet := by
    rw [complementMask_false_iff, raw_edge_mem_image_iff _
      (fun m hm => literalGraphEdges_bound cells E.family hwell hm)]
  have h := count_eq_triangle_card ((literalGraphEdges cells E.family).image maskSet)
    (complementMask (literalGraphEdges cells E.family)) hbits
  rw [literalGraphEdges_image] at h
  exact h

/-- The geometric triangular-ridge and bipyramid-equator lower bound in
the finite checker's exact120-triangle encoding. The local shape facts
are separate literal-template facts, while pairing comes from `E`. -/
theorem actual_triangle_lower_bound {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hdim : P.dim = 4)
    (B : Finset (Fin c)) (hBS : B ⊆ E.family)
    (htriangle : ∀ i ∈ E.family, ∀ R ∈ (decodeCell (cells i)).ridges,
      R.card = 3 → R.powersetCard 2 ⊆ (decodeCell (cells i)).edges)
    (hshape : ∀ i ∈ E.family,
      ((decodeCell (cells i)).ridges.filter fun R => R.card = 3).card =
        4 + if i ∈ B then 2 else 0)
    (base : Fin c → Finset (Fin 10))
    (hrules : ∀ i ∈ B, BaseRules (decodeCell (cells i)) (base i)) :
    2 * E.family.card + 2 * B.card ≤
      TenGraphTriangles.count (complementMask (literalGraphEdges cells E.family)) := by
  rw [actual_triangle_count cells hwell E]
  exact actual_graph_triangle_lower_bound E hdim B hBS htriangle hshape base hrules

end Papers.RationalityTen.ActualGraphTriangleCount

end
end
end BundlePart0

section BundlePart1
/- Source: SmallFacetTriangleShapes.lean -/






@[expose] public section

/-!
# Triangle shapes of every actual small facet

The four- and five-vertex classifications supply the local shape facts
used by the triangle lower bound. They are transported along arbitrary
injective vertex labelings, including the nonfacial equator of a triangular
bipyramid. No property of a producer-selected finite record is assumed.
-/

noncomputable section
namespace Papers.RationalityTen.SmallFacetTriangleShapes

open Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open MatroidChecked.FacetBoundaryEncoding MatroidChecked.BoundaryTriangleCount
open ActualFacetCatalogueTransport ActualSmallFacetClassification CellFacetInvariants
open LiteralMaskGeometry ActualFacetInducedGraph ActualGraphTriangleCount

variable {m n : ℕ}

def BipyramidPredicate (C : Cell n) : Prop :=
  4 < C.vertices.card ∧ cellExcess C ≠ 1

instance (C : Cell n) : Decidable (BipyramidPredicate C) := by
  unfold BipyramidPredicate
  infer_instance

structure TriangleShape (C : Cell n) : Prop where
  edges : ∀ R ∈ C.ridges, R.card = 3 → R.powersetCard 2 ⊆ C.edges
  count : cellRidgeSizeCount C 3 = 4 + if BipyramidPredicate C then 2 else 0
  base : BipyramidPredicate C → ∃ T, BaseRules C T

theorem powersetCard_image (f : Fin m ↪ Fin n) (S : Finset (Fin m)) (k : ℕ) :
    (S.image f).powersetCard k = (S.powersetCard k).image (fun T => T.image f) := by
  calc
    (S.image f).powersetCard k = (S.map f).powersetCard k := by
      rw [Finset.map_eq_image]
    _ = (S.powersetCard k).map (Finset.mapEmbedding f).toEmbedding :=
      Finset.powersetCard_map f k S
    _ = (S.powersetCard k).image (fun T => T.image f) := by
      rw [Finset.map_eq_image]
      apply Finset.image_congr
      intro T _
      exact Finset.map_eq_image f T

theorem properFaces_map_embedding (f : Fin m ↪ Fin n) (C : Cell m) :
    (mapCell f C).properFaces = C.properFaces.image (fun S => S.image f) := by
  simp only [Cell.properFaces, mapCell, Finset.image_union, Finset.image_singleton,
    Finset.image_empty, Finset.image_image, Function.comp_def]

theorem baseRules_map (f : Fin m ↪ Fin n) (C : Cell m)
    (T : Finset (Fin m)) (h : BaseRules C T) :
    BaseRules (mapCell f C) (T.image f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ f.injective]
    exact h.card
  · exact Finset.image_subset_image h.vertices
  · rw [powersetCard_image]
    exact Finset.image_subset_image h.edges
  · intro F hF hsub
    rw [properFaces_map_embedding] at hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    exact h.nonfacial G hG ((Finset.image_subset_image_iff f.injective).mp hsub)

theorem triangleShape_map (f : Fin m ↪ Fin n) (C : Cell m)
    (h : TriangleShape C) : TriangleShape (mapCell f C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R hR hcard
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
    rw [Finset.card_image_of_injective _ f.injective] at hcard
    rw [powersetCard_image]
    exact Finset.image_subset_image (h.edges S hS hcard)
  · rw [mapCell_ridge_size_count]
    simpa only [BipyramidPredicate, mapCell_vertex_card, mapCell_excess] using h.count
  · intro hB
    have hB' : BipyramidPredicate C := by
      simpa only [BipyramidPredicate, mapCell_vertex_card, mapCell_excess] using hB
    obtain ⟨T, hT⟩ := h.base hB'
    exact ⟨T.image f, baseRules_map f C T hT⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tetrahedron_shape : TriangleShape
    (cellOfBoundary (FiniteCycleCandidates.N4.templates 0)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  exact False.elim ((show ¬ BipyramidPredicate
    (cellOfBoundary (FiniteCycleCandidates.N4.templates 0)) by decide +kernel) h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bipyramid_shape : TriangleShape
    (cellOfBoundary (FiniteCycleCandidates.N5.templates 0)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro _
  refine ⟨{0, 1, 3}, ?_⟩
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem square_pyramid_shape : TriangleShape
    (cellOfBoundary (FiniteCycleCandidates.N5.templates 1)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  exact False.elim ((show ¬ BipyramidPredicate
    (cellOfBoundary (FiniteCycleCandidates.N5.templates 1)) by decide +kernel) h)

private theorem face_polytope_vertex_card {d : ℕ} (P : ConvexPolytope d)
    (F : Face P 3) : (facePolytope P F.val.isFace).vertices.card = facetVertexCount P F := by
  simpa only [facetVertexCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm

private theorem face_polytope_dim {d : ℕ} (P : ConvexPolytope d)
    (F : Face P 3) : (facePolytope P F.val.isFace).dim = 3 := by
  change faceDim (facePolytope P F.val.isFace).toSet = 3
  rw [facePolytope_toSet]
  exact F.property

/-- All local hypotheses in the triangle inequality follow from the
complete classification of actual three-dimensional facets with at most
five vertices. The ambient dimension and labeling remain unrestricted. -/
theorem actual_small_facet_shape {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (hF : facetVertexCount P F ≤ 5) :
    TriangleShape (actualCell P lab F) := by
  have hmin : 4 ≤ facetVertexCount P F :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  have hcases : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 := by omega
  rcases hcases with h4 | h5
  · obtain ⟨loc, i, hi⟩ := four_vertex_classification (facePolytope P F.val.isFace)
      (face_polytope_dim P F) ((face_polytope_vertex_card P F).trans h4)
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    rw [actualCell_of_template P lab F loc (FiniteCycleCandidates.N4.templates 0) hi]
    exact triangleShape_map _ _ tetrahedron_shape
  · obtain ⟨loc, i, hi⟩ := five_vertex_classification (facePolytope P F.val.isFace)
      (face_polytope_dim P F) ((face_polytope_vertex_card P F).trans h5)
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · rw [actualCell_of_template P lab F loc (FiniteCycleCandidates.N5.templates 0) hi]
      exact triangleShape_map _ _ bipyramid_shape
    · rw [actualCell_of_template P lab F loc (FiniteCycleCandidates.N5.templates 1) hi]
      exact triangleShape_map _ _ square_pyramid_shape

theorem kind_two_iff {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (hkind : ∀ i, UnrootedKindCheck cells i) (i : Fin c) :
    (cells i).kind = 2 ↔ BipyramidPredicate (decodeCell (cells i)) := by
  have h := hkind i
  unfold UnrootedKindCheck at h
  rw [h]
  unfold BipyramidPredicate
  by_cases hv : 4 < (decodeCell (cells i)).vertices.card <;>
    by_cases hx : cellExcess (decodeCell (cells i)) = 1 <;> simp [hv, hx]

/-- The all-small graph producer's lower bound, with every geometric and
local cell premise discharged by the actual boundary and its complete
four- and five-vertex facet classification. -/
theorem actual_all_small_triangle_lower_bound {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i)) (hkind : ∀ i, UnrootedKindCheck cells i)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hdim : P.dim = 4)
    (hsmall : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    2 * E.family.card + 2 * (E.family.filter fun i => (cells i).kind = 2).card ≤
      TenGraphTriangles.count (complementMask (literalGraphEdges cells E.family)) := by
  classical
  let B := E.family.filter fun i => (cells i).kind = 2
  have hshape (i : Fin c) (hi : i ∈ E.family) : TriangleShape (decodeCell (cells i)) := by
    obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
    rw [E.index_spec]
    exact actual_small_facet_shape P lab F (hsmall F)
  have hbase (i : Fin c) (hi : i ∈ B) : ∃ T, BaseRules (decodeCell (cells i)) T :=
    (hshape i (Finset.mem_filter.mp hi).1).base
      ((kind_two_iff cells hkind i).mp (Finset.mem_filter.mp hi).2)
  let base (i : Fin c) : Finset (Fin 10) :=
    if hi : i ∈ B then Classical.choose (hbase i hi) else ∅
  have hcount (i : Fin c) (hi : i ∈ E.family) :
      cellRidgeSizeCount (decodeCell (cells i)) 3 = 4 + if i ∈ B then 2 else 0 := by
    have hB : i ∈ B ↔ BipyramidPredicate (decodeCell (cells i)) := by
      simp only [B, Finset.mem_filter, hi, true_and, kind_two_iff cells hkind i]
    simpa only [hB] using (hshape i hi).count
  have hrules (i : Fin c) (hi : i ∈ B) :
      BaseRules (decodeCell (cells i)) (base i) := by
    dsimp only [base]
    rw [dif_pos hi]
    exact Classical.choose_spec (hbase i hi)
  exact actual_triangle_lower_bound cells hwell E hdim B (Finset.filter_subset _ _)
    (fun i hi => (hshape i hi).edges) hcount base hrules

end Papers.RationalityTen.SmallFacetTriangleShapes

end
end
end BundlePart1
