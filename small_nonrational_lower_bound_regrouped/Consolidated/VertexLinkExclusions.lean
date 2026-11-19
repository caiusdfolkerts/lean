module
public import ActualVertexLinkWeights
public import ActualFacetInducedGraph
public import VertexLinkObstructionData

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: LiteralVertexLinkWeights.lean -/





@[expose] public section

/-!
# Vertex-link weights in literal boundary records

Every edge mask is decoded injectively. Thus a cell's literal degree at
a label equals the degree inside the corresponding actual facet. The
sum below includes every selected facet, with weight zero at labels not
in that facet. It is an exact equality for every encoded convex boundary.
-/

noncomputable section
namespace Papers.RationalityTen.LiteralVertexLinkWeights

open Set Finset
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open MatroidChecked.FacetBoundaryEncoding
open LiteralMaskGeometry ActualFacetInducedGraph ActualVertexLinkWeights

def localDegree (C : ConcreteGrowth.Cell) (v : Fin 10) : ℕ :=
  (C.edges.toFinset.filter fun e => e.testBit v.val = true).card

/-- The integer Euler contribution is nonnegative for actual incident
facets. The natural subtraction here is justified by the actual proof. -/
def vertexWeight (C : ConcreteGrowth.Cell) (v : Fin 10) : ℕ :=
  if C.vertices.testBit v.val = true then localDegree C v - 2 else 0

theorem localDegree_semantics (C : ConcreteGrowth.Cell) (hC : WellFormed C)
    (v : Fin 10) :
    localDegree C v = ((decodeCell C).edges.filter fun e => v ∈ e).card := by
  change _ = ((C.edges.toFinset.image maskSet).filter fun e => v ∈ e).card
  rw [Finset.filter_image]
  have hinj : Set.InjOn maskSet (C.edges.toFinset.filter fun e => v ∈ maskSet e) := by
    intro a ha b hb hab
    exact maskSet_injective
      (hC.edges_bound a (List.mem_toFinset.mp (Finset.mem_filter.mp ha).1))
      (hC.edges_bound b (List.mem_toFinset.mp (Finset.mem_filter.mp hb).1)) hab
  rw [Finset.card_image_of_injOn hinj]
  simp only [localDegree, mem_maskSet]

theorem actualCell_localDegree {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (v : Fin n) :
    ((actualCell P lab F).edges.filter fun e => v ∈ e).card =
      Nat.card (EdgesAtVertexBelow P (lab.symm v).val F.val.carrier) := by
  change ((((Finset.univ : Finset (Face P 1)).filter
    (fun e => e.val.carrier ⊆ F.val.carrier)).image (faceLabels P lab)).filter
      (fun e => v ∈ e)).card = _
  rw [Finset.filter_image, Finset.card_image_of_injective _ (faceLabels_injective P lab),
    Nat.card_congr (edgesAtVertexBelowEquiv P (lab.symm v).val F.val.carrier),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.filter_filter, mem_faceLabels_iff]

theorem encoded_localDegree {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (F : Face P 3) (v : Fin 10) :
    localDegree (cells (E.index F)) v =
      Nat.card (EdgesAtVertexBelow P (lab.symm v).val F.val.carrier) := by
  rw [localDegree_semantics _ (hwell _), E.index_spec]
  exact actualCell_localDegree P lab F v

theorem encoded_vertex_membership {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (F : Face P 3) (v : Fin 10) :
    (cells (E.index F)).vertices.testBit v.val = true ↔
      (lab.symm v).val ∈ F.val.carrier := by
  rw [← mem_maskSet]
  change v ∈ (decodeCell (cells (E.index F))).vertices ↔ _
  rw [E.index_spec]
  exact mem_faceLabels_iff P lab F v

theorem encoded_weight_sum {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (v : Fin 10) :
    (∑ i ∈ E.family, vertexWeight (cells i) v) =
      ∑ F : IncidentFace P (lab.symm v).val 3,
        (Nat.card (EdgesAtVertexBelow P (lab.symm v).val F.val.val.carrier) - 2) := by
  calc
    _ = ∑ F : Face P 3, vertexWeight (cells (E.index F)) v := by
      rw [Encoding.family, Finset.sum_image]
      intro a _ b _ hab
      exact E.index_injective hab
    _ = ∑ F ∈ (Finset.univ : Finset (Face P 3)).filter
        (fun F => (lab.symm v).val ∈ F.val.carrier),
        (Nat.card (EdgesAtVertexBelow P (lab.symm v).val F.val.carrier) - 2) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro F _
      simp only [vertexWeight, encoded_vertex_membership cells E F v,
        encoded_localDegree cells hwell E F v]
    _ = _ := Finset.sum_subtype _ (by intro F; simp only
        [Finset.mem_filter, Finset.mem_univ, true_and]) _

/-- Every actual encoded four-polytope satisfies the exact vertex-link
Euler equation, expressed entirely by finite masks and natural counts. -/
theorem literal_vertex_link_weight_identity {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (v : Fin 10) :
    (∑ i ∈ E.family, vertexWeight (cells i) v) + 4 =
      2 * ((literalGraphEdges cells E.family).filter
        fun e => e.testBit v.val = true).card := by
  rw [encoded_weight_sum cells hwell E v,
    literalGraphEdges_incidence_card cells hwell E hP v]
  exact vertex_link_weight_identity_nat P hP (lab.symm v)

theorem literal_vertex_weight_sum {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (v : Fin 10) :
    (∑ i ∈ E.family, vertexWeight (cells i) v) =
      2 * ((literalGraphEdges cells E.family).filter
        fun e => e.testBit v.val = true).card - 4 := by
  have h := literal_vertex_link_weight_identity cells hwell E hP v
  omega

end Papers.RationalityTen.LiteralVertexLinkWeights

end
end
end BundlePart0

section BundlePart1
/- Source: VertexLinkObstruction.lean -/





@[expose] public section

/-!
# Excluding the four terminal families with an invalid vertex link

A terminal list is compared with the complete selected family of a genuine
facet encoding. Its raw cells determine both sides of the vertex-link Euler
identity. Thus a finite inequality of those two counts excludes every actual
four-dimensional realization of that complete family.
-/

noncomputable section
namespace Papers.RationalityTen.VertexLinkObstruction

open Set Finset
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open MatroidChecked.FacetBoundaryEncoding
open LiteralMaskGeometry ActualFacetInducedGraph LiteralVertexLinkWeights

namespace Data

open VertexLinkObstructionData

theorem distinct_toFinset (values : List Nat) :
    (distinct values).toFinset = values.toFinset := by
  ext a
  simp only [List.mem_toFinset, mem_distinct]

theorem distinct_filter_length (values : List Nat) (vertex : Nat) :
    ((distinct values).filter fun edge => edge.testBit vertex).length =
      (values.toFinset.filter fun edge => edge.testBit vertex = true).card := by
  rw [← List.toFinset_card_of_nodup ((distinct_nodup values).filter _),
    List.toFinset_filter, distinct_toFinset]

theorem degree_eq (cell : ConcreteGrowth.Cell) (vertex : Fin 10) :
    degree cell vertex.val = localDegree cell vertex := by
  exact distinct_filter_length cell.edges vertex.val

theorem weight_eq (cell : ConcreteGrowth.Cell) (vertex : Fin 10) :
    weight cell vertex.val = vertexWeight cell vertex := by
  simp only [weight, vertexWeight, degree_eq]

theorem weightSum_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (hnodup : selected.Nodup) (vertex : Fin 10) :
    weightSum (selected.map cells) vertex.val =
      ∑ i ∈ selected.toFinset, vertexWeight (cells i) vertex := by
  rw [List.sum_toFinset _ hnodup]
  simp only [weightSum, List.map_map, Function.comp_def, weight_eq]

theorem edges_flatMap_toFinset {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) :
    ((selected.map cells).flatMap ConcreteGrowth.Cell.edges).toFinset =
      literalGraphEdges cells selected.toFinset := by
  ext edge
  simp [literalGraphEdges]

theorem graphDegree_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (vertex : Fin 10) :
    graphDegree (selected.map cells) vertex.val =
      ((literalGraphEdges cells selected.toFinset).filter
        fun edge => edge.testBit vertex.val = true).card := by
  rw [graphDegree, distinct_filter_length, edges_flatMap_toFinset]

end Data

/-- A checked raw Euler violation cannot be the complete selected family
of an actual four-polytope. The selected list may have any order; the
literal-cell equality preserves precisely the order used by its certificate. -/
theorem checked_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (vertex : Fin 10) (hcheck : VertexLinkObstructionData.check raw vertex.val = true) :
    False := by
  have hbad : VertexLinkObstructionData.weightSum raw vertex.val + 4 ≠
      2 * VertexLinkObstructionData.graphDegree raw vertex.val := of_decide_eq_true hcheck
  apply hbad
  rw [← hraw, Data.weightSum_map cells selected hnodup vertex,
    Data.graphDegree_map cells selected vertex, ← hfamily]
  exact literal_vertex_link_weight_identity cells hwell E hP vertex

theorem G0477T0_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (hraw : selected.map cells = VertexLinkObstructionData.G0477T0) : False :=
  checked_not_selected_family cells hwell E hP selected hnodup hfamily _ hraw 0
    VertexLinkObstructionData.G0477T0_checked

theorem G0811T0_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (hraw : selected.map cells = VertexLinkObstructionData.G0811T0) : False :=
  checked_not_selected_family cells hwell E hP selected hnodup hfamily _ hraw 0
    VertexLinkObstructionData.G0811T0_checked

theorem G1439T0_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (hraw : selected.map cells = VertexLinkObstructionData.G1439T0) : False :=
  checked_not_selected_family cells hwell E hP selected hnodup hfamily _ hraw 0
    VertexLinkObstructionData.G1439T0_checked

theorem G1627T0_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (hraw : selected.map cells = VertexLinkObstructionData.G1627T0) : False :=
  checked_not_selected_family cells hwell E hP selected hnodup hfamily _ hraw 0
    VertexLinkObstructionData.G1627T0_checked

end Papers.RationalityTen.VertexLinkObstruction

end
end
end BundlePart1
