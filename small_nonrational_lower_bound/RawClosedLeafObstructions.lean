module

public import RawClosedLeafData
public import VertexLinkObstruction
public import ActualGraphGrowthTarget

@[expose] public section

/-!
# Closed-leaf contradictions for actual facet encodings

The complete ordered raw record is compared with the selected family. Exact
kind counts, minimum vertex incidence, and the global Euler equation then
exclude the corresponding checked finite leaves. None of these conditions is
inferred from the search producer's label for a leaf.
-/

noncomputable section
namespace Papers.RationalityTen.RawClosedLeafObstructions

open Set Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeEulerFour
open MatroidChecked.FacetBoundaryEncoding
open LiteralMaskGeometry ActualFacetInducedGraph ActualGraphGrowthTarget
open GraphGrowthConstraints

theorem kindCount_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (kind : Nat) :
    RawClosedLeafData.kindCount (selected.map cells) kind =
      GrowthPruning.kindCount (fun i => (cells i).kind) selected kind := by
  simp only [RawClosedLeafData.kindCount, GrowthPruning.kindCount,
    List.filter_map, List.length_map, Function.comp_def]

theorem incidenceCount_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (vertex : Nat) :
    RawClosedLeafData.incidenceCount (selected.map cells) vertex =
      (selected.filter fun i => (cells i).vertices.testBit vertex).length := by
  simp only [RawClosedLeafData.incidenceCount, List.filter_map,
    List.length_map, Function.comp_def]

/-- Applicable to a legacy growth target as soon as its actual numerical
row supplies the exact count of the indicated kind. -/
theorem quota_not_exact {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (raw : List ConcreteGrowth.Cell)
    (hraw : selected.map cells = raw) (kind quota : Nat)
    (hexact : GrowthPruning.kindCount (fun i => (cells i).kind) selected kind = quota)
    (hcheck : RawClosedLeafData.quotaFailure raw kind quota = true) : False := by
  have hbad : RawClosedLeafData.kindCount raw kind ≠ quota := of_decide_eq_true hcheck
  apply hbad
  rw [← hraw, kindCount_map]
  exact hexact

/-- The incidence test uses an actual lower bound, independently of the
search's current budget or compatibility cache. -/
theorem incidence_below_minimum {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) (raw : List ConcreteGrowth.Cell)
    (hraw : selected.map cells = raw) (vertex minimum : Nat)
    (hlower : minimum ≤
      (selected.filter fun i => (cells i).vertices.testBit vertex).length)
    (hcheck : RawClosedLeafData.incidenceFailure raw vertex minimum = true) : False := by
  have hbad : RawClosedLeafData.incidenceCount raw vertex < minimum :=
    of_decide_eq_true hcheck
  rw [← hraw, incidenceCount_map] at hbad
  exact Nat.not_lt_of_ge hlower hbad

/-- An actual numerical case row can supply its kind count directly,
without constructing the additional graph-search data. -/
theorem quota_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (kind quota : Nat)
    (hexact : (E.family.filter fun i => (cells i).kind = kind).card = quota)
    (hcheck : RawClosedLeafData.quotaFailure raw kind quota = true) : False := by
  apply quota_not_exact cells selected raw hraw kind quota _ hcheck
  rw [GrowthPruning.kindCount,
    ← List.toFinset_card_of_nodup (hnodup.filter _), List.toFinset_filter, ← hfamily]
  simpa only [decide_eq_true_eq] using hexact

/-- Intrinsic nonsimplicity supplies the five-facet lower bound for an
actual complete selected family. -/
theorem incidence_below_five_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices,
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (vertex : Fin 10)
    (hcheck : RawClosedLeafData.incidenceFailure raw vertex.val 5 = true) : False := by
  apply incidence_below_minimum cells selected raw hraw vertex.val 5 _ hcheck
  rw [← List.toFinset_card_of_nodup (hnodup.filter _),
    List.toFinset_filter, ← hfamily]
  simpa only [Encoding.vertexIncidence, decodeCell, mem_maskSet] using
    E.vertex_incidence_ge_five hP hnonsimple vertex

theorem target_quota_not_exact {c k : Nat} (D : Problem c 1024 45 10 k)
    (cells : Fin c → ConcreteGrowth.Cell) (H : LiteralData D cells)
    (selected : List (Fin c)) (hselected : Target D selected)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (kind : Fin k)
    (hcheck : RawClosedLeafData.quotaFailure raw kind.val (D.quota kind.val) = true) :
    False := by
  apply quota_not_exact cells selected raw hraw kind.val (D.quota kind.val) _ hcheck
  simpa only [GrowthPruning.kindCount, H.kind] using hselected.exactQuota kind

theorem target_incidence_below_minimum {c k : Nat} (D : Problem c 1024 45 10 k)
    (cells : Fin c → ConcreteGrowth.Cell) (H : LiteralData D cells)
    (selected : List (Fin c)) (hselected : Target D selected)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (vertex : Fin 10)
    (hcheck : RawClosedLeafData.incidenceFailure raw vertex.val D.minimumIncidence = true) :
    False := by
  apply incidence_below_minimum cells selected raw hraw vertex.val D.minimumIncidence _ hcheck
  simpa only [vertexCount, H.vertices] using hselected.incidence vertex

theorem distinct_length (values : List Nat) :
    (VertexLinkObstructionData.distinct values).length = values.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (VertexLinkObstructionData.distinct_nodup values),
    VertexLinkObstruction.Data.distinct_toFinset]

def literalRidges {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) : Finset Nat :=
  selected.biUnion fun i => (cells i).ridgeMasks.toFinset

theorem literalRidges_image {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) :
    (literalRidges cells selected).image maskSet =
      selected.biUnion fun i => (decodeCell (cells i)).ridges :=
  Finset.biUnion_image

theorem literalRidges_card {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    (literalRidges cells E.family).card = Nat.card (Face P 2) := by
  have hinj : Set.InjOn maskSet (literalRidges cells E.family) := by
    intro a ha b hb hab
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
    exact maskSet_injective ((hwell i).ridges_bound a (List.mem_toFinset.mp hi))
      ((hwell j).ridges_bound b (List.mem_toFinset.mp hj)) hab
  rw [← Finset.card_image_of_injOn hinj, literalRidges_image,
    E.ridges_eq_actual hP, Finset.card_image_of_injective _ (faceLabels_injective P lab),
    Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

theorem edgeCount_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) :
    RawClosedLeafData.edgeCount (selected.map cells) =
      (literalGraphEdges cells selected.toFinset).card := by
  rw [RawClosedLeafData.edgeCount, distinct_length,
    VertexLinkObstruction.Data.edges_flatMap_toFinset]

theorem ridgeCount_map {c : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : List (Fin c)) :
    RawClosedLeafData.ridgeCount (selected.map cells) =
      (literalRidges cells selected.toFinset).card := by
  rw [RawClosedLeafData.ridgeCount, distinct_length]
  apply congrArg Finset.card
  ext ridge
  simp [literalRidges]

/-- The raw edge/ridge union and facet list have the Euler counts of the
actual polytope whenever they are exactly its encoded facet family. -/
theorem global_euler_not_selected_family {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (selected : List (Fin c)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (hcheck : RawClosedLeafData.eulerFailure raw = true) : False := by
  have hbad : 10 + RawClosedLeafData.ridgeCount raw ≠
      RawClosedLeafData.edgeCount raw + raw.length := of_decide_eq_true hcheck
  have hvertices : P.vertices.card = 10 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr lab
  have hfacets : selected.length = Nat.card (Face P 3) := by
    rw [← List.toFinset_card_of_nodup hnodup, ← hfamily, E.family_card]
  apply hbad
  rw [← hraw, edgeCount_map, ridgeCount_map, List.length_map, ← hfamily,
    literalGraphEdges_card cells hwell E hP, literalRidges_card cells hwell E hP,
    hfacets, ← hvertices]
  exact vertices_add_two_faces_eq_edges_add_facets P hP

#print axioms target_quota_not_exact
#print axioms target_incidence_below_minimum
#print axioms global_euler_not_selected_family

end Papers.RationalityTen.RawClosedLeafObstructions
