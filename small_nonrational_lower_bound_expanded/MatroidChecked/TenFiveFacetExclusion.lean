module
public import MatroidChecked.BoundaryTriangleCount
public import MatroidChecked.GoodmanTen

@[expose] public section
noncomputable section

/-! The two ten-facet small budgets are excluded uniformly by triangle
counting. All cell-shape premises are literal finite properties; all
incidence and degree bounds are derived from the actual convex polytope. -/
namespace Papers.RationalityTen.MatroidChecked.TenFiveFacetExclusion
open Set Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone
open FacetBoundaryEncoding BoundaryTriangleCount
open scoped Classical BigOperators

theorem sum_vertex_incidence {n c : ℕ} (cells : Fin c → Cell n) (S : Finset (Fin c)) :
    (∑ v : Fin n, (S.filter fun i => v ∈ (cells i).vertices).card) =
      ∑ i ∈ S, (cells i).vertices.card := by
  calc
    (∑ v : Fin n, (S.filter fun i => v ∈ (cells i).vertices).card) =
        ∑ v : Fin n, ∑ i ∈ S, if v ∈ (cells i).vertices then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = ∑ i ∈ S, ∑ v : Fin n, if v ∈ (cells i).vertices then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ i ∈ S, (cells i).vertices.card := by simp

theorem all_vertex_incidences_five {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin c → Cell 10}
    (E : Encoding P lab cells) (hdim : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, (actualNeighbors P v.val).card ≠ 4)
    (hfacets : E.family.card = 10)
    (hsize : ∀ i ∈ E.family, (cells i).vertices.card = 5) :
    ∀ v : Fin 10, (E.vertexIncidence v).card = 5 := by
  have hsum : (∑ v : Fin 10, (E.vertexIncidence v).card) = 50 := by
    change (∑ v : Fin 10, (E.family.filter fun i => v ∈ (cells i).vertices).card) = 50
    rw [sum_vertex_incidence]
    calc
      (∑ i ∈ E.family, (cells i).vertices.card) = ∑ i ∈ E.family, (5:ℕ) :=
        Finset.sum_congr rfl hsize
      _ = 50 := by simp [hfacets]
  have hlow (v : Fin 10) : 5 ≤ (E.vertexIncidence v).card :=
    E.vertex_incidence_ge_five hdim hnonsimple v
  intro v
  by_contra hne
  have hv : 5 < (E.vertexIncidence v).card := by have h:=hlow v; omega
  have hlt := Finset.sum_lt_sum (s:=Finset.univ)
    (fun w _ => hlow w) ⟨v,Finset.mem_univ _,hv⟩
  have hconst : (∑ v : Fin 10, (5:ℕ)) = 50 := by simp
  rw [hconst,hsum] at hlt
  omega


/-- Ten five-vertex facets with at least six triangular bipyramids cannot
form a nonsimple ten-vertex convex four-polytope. -/
theorem impossible {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin c → Cell 10}
    (E : Encoding P lab cells) (hdim : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, (actualNeighbors P v.val).card ≠ 4)
    (hfacets : E.family.card = 10)
    (hsize : ∀ i ∈ E.family, (cells i).vertices.card = 5)
    (hEdges : ∀ i ∈ E.family, ∀ e ∈ (cells i).edges, e.card = 2)
    (B : Finset (Fin c)) (hBS : B ⊆ E.family) (hB : 6 ≤ B.card)
    (htriangle : ∀ i ∈ E.family, ∀ R ∈ (cells i).ridges,
      R.card = 3 → R.powersetCard 2 ⊆ (cells i).edges)
    (hshape : ∀ i ∈ E.family, ((cells i).ridges.filter fun R => R.card = 3).card =
      4 + if i ∈ B then 2 else 0)
    (base : Fin c → Finset (Fin 10)) (hrules : ∀ i ∈ B, BaseRules (cells i) (base i)) :
    False := by
  have hinc := all_vertex_incidences_five E hdim hnonsimple hfacets hsize
  let edges := E.family.biUnion fun i => (cells i).edges
  have hE : ∀ e ∈ edges, e.card = 2 := by
    intro e he
    obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
    exact hEdges i hi e hei
  have hdegree (v : Fin 10) : 3 ≤ (edges.filter fun e => v ∈ e).card ∧
      (edges.filter fun e => v ∈ e).card ≤ 6 := by
    have hlo := E.vertex_edge_incidence_ge_five hdim hnonsimple v
    have hhi := E.vertex_link_bound hdim v
    rw [hinc v] at hhi
    change 5 ≤ (edges.filter fun e => v ∈ e).card at hlo
    change (edges.filter fun e => v ∈ e).card + 4 ≤ 2 * 5 at hhi
    omega
  have hupper := GoodmanTen.triangle_card_le_thirty edges hE hdegree
  have hlower := actual_graph_triangle_lower_bound E hdim B hBS htriangle hshape base hrules
  change (graphTriangles edges).card ≤ 30 at hupper
  change 2 * E.family.card + 2 * B.card ≤ (graphTriangles edges).card at hlower
  rw [hfacets] at hlower
  omega

end Papers.RationalityTen.MatroidChecked.TenFiveFacetExclusion
