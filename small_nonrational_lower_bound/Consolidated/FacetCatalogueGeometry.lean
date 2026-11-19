module
public import Consolidated.ThreeDimensionalIncidences
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.EquivFin
public import BoundaryGeometry
public import Papers.RationalityTenPolygonCatalogue
public import PolygonCycleGeometry
public import FiniteCycleData4
public import FiniteCycleN5K3
public import FiniteCycleN5K4
public import FiniteCycleCandidates
public import FiniteChecks
public import FiniteCycleData5
public import FiniteCycleData6
public import WitnessGrowthDAG
public import Mathlib.Logic.Equiv.Fin.Basic
public import PolygonN5DAG
public import FiniteFacetCells
public import MatroidChecked.FacetBoundaryEncoding

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: ActualFaceTransport.lean -/






@[expose] public section

/-!
# Exact transport of a face boundary into the ambient vertex labels

A three-dimensional facet is itself a convex polytope. A catalogue may
therefore label its vertices independently of the ambient four-polytope.
This file proves that changing from these local labels to ambient labels
preserves every actual face, in both directions. In particular it preserves
both the edge family and the polygon family; vertex masks alone are not
used as a substitute for the complete facet boundary.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFaceTransport

open Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open scoped Classical

variable {d m n k l : ℕ}

/-- Vertex labels of an actual face. -/
def labels (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P k) : Finset (Fin n) :=
  (faceCode P k F).image lab

/-- The complete family of actual faces of one dimension. -/
def family (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (k : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Face P k)).image (labels P lab)

/-- The actual faces of one dimension contained in a fixed face. -/
def lowerFamily (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P l) (k : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Face P k)).filter
    (fun G => G.val.carrier ⊆ F.val.carrier)).image (labels P lab)

/-- Inclusion of the actual vertices of a face into the ambient vertices. -/
def includeVertex (P : ConvexPolytope d) (F : Face P l) :
    (facePolytope P F.val.isFace).vertices ↪ P.vertices where
  toFun v := ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun z : P.vertices => z.val) h

/-- The injective change from independently chosen local labels to the
ambient labels. There is no unproved incidence or genericity condition. -/
def labelEmbedding (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P l)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m) : Fin m ↪ Fin n where
  toFun i := lab (includeVertex P F (loc.symm i))
  inj' := by
    intro i j h
    exact loc.symm.injective ((includeVertex P F).injective (lab.injective h))

/-- A local face is the same exposed face in the ambient polytope. -/
def liftFace (P : ConvexPolytope d) (F : Face P l)
    (G : Face (facePolytope P F.val.isFace) k) : Face P k :=
  ((faceBelowEquiv P F.val.isFace k).symm G).val

@[simp] theorem liftFace_carrier (P : ConvexPolytope d) (F : Face P l)
    (G : Face (facePolytope P F.val.isFace) k) :
    (liftFace P F G).val.carrier = G.val.carrier := rfl

/-- Every lifted face is contained in the selected ambient face. -/
theorem liftFace_subset (P : ConvexPolytope d) (F : Face P l)
    (G : Face (facePolytope P F.val.isFace) k) :
    (liftFace P F G).val.carrier ⊆ F.val.carrier :=
  ((faceBelowEquiv P F.val.isFace k).symm G).property

/-- Exact transport of one face's vertex set. -/
theorem labels_image (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P l) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m)
    (G : Face (facePolytope P F.val.isFace) k) :
    (labels _ loc G).image (labelEmbedding P lab F loc) =
      labels P lab (liftFace P F G) := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    apply Finset.mem_image.mpr
    refine ⟨includeVertex P F v, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
    · rw [← hji, ← hvj]
      change lab (includeVertex P F v) =
        lab (includeVertex P F (loc.symm (loc v)))
      rw [loc.symm_apply_apply]
  · intro hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    have hvG : v.val ∈ G.val.carrier := (Finset.mem_filter.mp hv).2
    have hvF : v.val ∈ F.val.carrier := liftFace_subset P F G hvG
    let w : (facePolytope P F.val.isFace).vertices :=
      ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hvF⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨loc w, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨w,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvG⟩, rfl⟩
    · change lab (includeVertex P F (loc.symm (loc w))) = i
      rw [loc.symm_apply_apply]
      exact hvi

/-- Exact transport of all faces in any dimension, including their
completeness in the ambient face lattice. -/
theorem family_image (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P l) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m) (k : ℕ) :
    (family _ loc k).image (fun S => S.image (labelEmbedding P lab F loc)) =
      lowerFamily P lab F k := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    obtain ⟨G, _, hGT⟩ := Finset.mem_image.mp hT
    apply Finset.mem_image.mpr
    refine ⟨liftFace P F G,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, liftFace_subset P F G⟩, ?_⟩
    rw [← labels_image P lab F loc G, hGT, hTS]
  · intro hS
    obtain ⟨G, hG, hGS⟩ := Finset.mem_image.mp hS
    let G' : Face (facePolytope P F.val.isFace) k :=
      faceBelowEquiv P F.val.isFace k ⟨G, (Finset.mem_filter.mp hG).2⟩
    apply Finset.mem_image.mpr
    refine ⟨labels _ loc G', Finset.mem_image.mpr ⟨G', Finset.mem_univ _, rfl⟩, ?_⟩
    rw [labels_image]
    exact hGS

/-- The image of all local vertices is exactly the ambient vertex mask
of the selected face. -/
theorem vertices_image (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P l) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m) :
    (Finset.univ : Finset (Fin m)).image (labelEmbedding P lab F loc) =
      labels P lab F := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
    apply Finset.mem_image.mpr
    refine ⟨includeVertex P F (loc.symm j), ?_, hji⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (loc.symm j).property).2⟩
  · intro hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    let w : (facePolytope P F.val.isFace).vertices :=
      ⟨v.val, Finset.mem_filter.mpr ⟨v.property, (Finset.mem_filter.mp hv).2⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨loc w, Finset.mem_univ _, ?_⟩
    change lab (includeVertex P F (loc.symm (loc w))) = i
    rw [loc.symm_apply_apply]
    exact hvi

/-- A local catalogue that preserves every edge and polygon gives exactly
the corresponding ambient edge and polygon families. This is the
geometric transport needed before applying a finite boundary search. -/
theorem facet_template_transport (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m)
    (edges polygons : Finset (Finset (Fin m)))
    (hedges : family (facePolytope P F.val.isFace) loc 1 = edges)
    (hpolygons : family (facePolytope P F.val.isFace) loc 2 = polygons) :
    ∃ f : Fin m ↪ Fin n,
      (Finset.univ.image f = labels P lab F) ∧
      (edges.image (fun S => S.image f) = lowerFamily P lab F 1) ∧
      (polygons.image (fun S => S.image f) = lowerFamily P lab F 2) := by
  refine ⟨labelEmbedding P lab F loc, vertices_image P lab F loc, ?_, ?_⟩
  · rw [← hedges]
    exact family_image P lab F loc 1
  · rw [← hpolygons]
    exact family_image P lab F loc 2

end Papers.RationalityTen.ActualFaceTransport

end
end
end BundlePart0

section BundlePart1
/- Source: TriangularRootNormalization.lean -/






@[expose] public section

/-!
# Triangular roots obtained from actual three-dimensional geometry

Every three-dimensional convex polytope with at most seven vertices has
an actual triangular facet. We derive this from the already verified
Euler equation, ridge incidence and tangent-cone degree bound, and then
extend a bijection of the triangle's vertices to a permutation of all
vertex labels. This justifies the triangular root used by the finite
five-, six- and seven-vertex catalogues.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFaceTransport

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeEulerThree
open Papers.PolytopeThreeIncidences Papers.FaceIncidenceEuler

variable {d n k : ℕ}

/-- Local tangent geometry gives the graph-degree lower bound. -/
theorem graph_degree_ge_dimension (P : ConvexPolytope d) (v : P.vertices) :
    P.dim ≤ (vertexGraph P).degree v := by
  let e : (vertexGraph P).neighborSet v ≃
      Papers.PolytopeVertexCone.actualNeighbors P v.val :=
    { toFun w := ⟨w.val.val, Finset.mem_filter.mpr ⟨w.val.property, w.property⟩⟩
      invFun w := ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩,
        (Finset.mem_filter.mp w.property).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hc := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] at hc
  rw [hc]
  exact actual_neighbor_card_ge_dim P v.property

/-- The sum of the genuine graph degrees is at least three per vertex. -/
theorem three_vertex_edge_bound (P : ConvexPolytope d) (hP : P.dim = 3) :
    3 * P.vertices.card ≤ 2 * Nat.card (Face P 1) := by
  have hdeg (v : P.vertices) : 3 ≤ (vertexGraph P).degree v := by
    simpa only [hP] using graph_degree_ge_dimension P v
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
  have hc : (vertexGraph P).edgeFinset.card = Nat.card (Face P 1) := by
    rw [← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card]
    exact graph_edge_card_eq_one_face_card P
  rw [(vertexGraph P).sum_degrees_eq_twice_card_edges, hc] at hs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul, mul_comm] using hs

/-- Existence of an actual triangular facet, with no catalogue premise. -/
theorem actual_triangle (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card ≤ 7) :
    ∃ R : Face P 2, Nat.card (VerticesOn P R.val.carrier) = 3 := by
  have heuler := euler_three P hP
  have hvertex := three_vertex_edge_bound P hP
  have hinc := total_vertex_facet_incidences P hP
  apply exists_triangular_face_of_counts
    (fun R : Face P 2 => Nat.card (VerticesOn P R.val.carrier))
    (n := (P.vertices.card : ℤ)) (e := (Nat.card (Face P 1) : ℤ))
    (f := (Nat.card (Face P 2) : ℤ))
  · simp only [Nat.card_eq_fintype_card]
  · exact_mod_cast hn
  · exact heuler
  · exact_mod_cast hvertex
  · linarith
  · intro R
    have h := face_vertex_card_gt_dimension P 2 R
    omega

/-- The actual number of polygonal facets has the catalogue's bound. -/
theorem actual_face_bound (P : ConvexPolytope d) (hP : P.dim = 3) :
    Nat.card (Face P 2) ≤ 2 * P.vertices.card - 4 := by
  have hinc := total_vertex_facet_incidences P hP
  have hmin (R : Face P 2) : (3 : ℤ) ≤ Nat.card (VerticesOn P R.val.carrier) := by
    have h := face_vertex_card_gt_dimension P 2 R
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun R _ => hmin R)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  rw [hinc] at hs
  have hv := actual_vertices_card_gt_dim P
  rw [hP] at hv
  rw [← Nat.card_eq_fintype_card] at hs
  omega

/-- Cardinality of a face mask equals its actual number of vertices. -/
theorem labels_card (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P k) :
    (labels P lab F).card = Nat.card (VerticesOn P F.val.carrier) := by
  rw [labels, Finset.card_image_of_injective _ lab.injective]
  simp only [faceCode, VerticesOn, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Relabeling the vertices relabels all actual face masks. -/
theorem labels_relabel (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (σ : Equiv.Perm (Fin n)) (F : Face P k) :
    labels P (lab.trans σ) F = (labels P lab F).image σ := by
  simp only [labels, Finset.image_image]
  rfl

/-- The first `k` labels, without any convention about numerals in `Fin n`. -/
def firstLabels (n k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)

@[simp] theorem firstLabels_card (n k : ℕ) (hk : k ≤ n) :
    (firstLabels n k hk).card = k := by
  rw [firstLabels, Finset.card_image_of_injective]
  · simp
  · intro a b h
    apply Fin.ext
    exact congrArg (fun i : Fin n => i.val) h

/-- Normalize an actual triangle to the first three labels by a permutation
of all vertices. No incidence is changed by this normalization. -/
theorem normalize_triangle (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (R : Face P 2)
    (hR : Nat.card (VerticesOn P R.val.carrier) = 3) (hn : 3 ≤ n) :
    ∃ σ : Equiv.Perm (Fin n),
      labels P (lab.trans σ) R = firstLabels n 3 hn := by
  have hc : (labels P lab R).card = (firstLabels n 3 hn).card := by
    rw [labels_card, hR, firstLabels_card]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (labels P lab R) (firstLabels n 3 hn) hc
  refine ⟨σ, ?_⟩
  rw [labels_relabel]
  rw [Finset.map_eq_image] at hσ
  change (labels P lab R).image σ = firstLabels n 3 hn at hσ
  exact hσ

/-- Every actual polytope in the small three-dimensional catalogues admits
the normalized triangular root used by their finite search. -/
theorem actual_normalized_triangle (P : ConvexPolytope d)
    (hP : P.dim = 3) (hn : P.vertices.card ≤ 7) :
    ∃ (hthree : 3 ≤ P.vertices.card) (lab : P.vertices ≃ Fin P.vertices.card)
      (R : Face P 2), labels P lab R = firstLabels P.vertices.card 3 hthree := by
  obtain ⟨R, hR⟩ := actual_triangle P hP hn
  have hv := actual_vertices_card_gt_dim P
  rw [hP] at hv
  have hthree : 3 ≤ P.vertices.card := by omega
  let lab := P.vertices.equivFin
  obtain ⟨σ, hσ⟩ := normalize_triangle P lab R hR hthree
  exact ⟨hthree, lab.trans σ, R, hσ⟩

/-- Apply the same normalization to each actual three-face. This is the
local geometric input for the four-dimensional facet-cell universe. -/
theorem actual_facet_normalized_triangle (P : ConvexPolytope d) (F : Face P 3)
    (hF : Nat.card (VerticesOn P F.val.carrier) ≤ 7) :
    ∃ (hthree : 3 ≤ (facePolytope P F.val.isFace).vertices.card)
      (loc : (facePolytope P F.val.isFace).vertices ≃
        Fin (facePolytope P F.val.isFace).vertices.card)
      (R : Face (facePolytope P F.val.isFace) 2),
      labels (facePolytope P F.val.isFace) loc R =
        firstLabels (facePolytope P F.val.isFace).vertices.card 3 hthree := by
  apply actual_normalized_triangle
  · change faceDim (facePolytope P F.val.isFace).toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  · have hc : (facePolytope P F.val.isFace).vertices.card =
        Nat.card (VerticesOn P F.val.carrier) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm
    omega

end Papers.RationalityTen.ActualFaceTransport

end
end
end BundlePart1

section BundlePart2
/- Source: ActualPolygonBoundary.lean -/






@[expose] public section

/-!
# Polygon cells of an actual three-dimensional polytope

Each cell records its actual vertices and every actual edge as a canonical
ordered pair. The encoding theorems derive edge pairing, connectedness,
minimum vertex degree and Euler's equation from convex geometry. A finite
catalogue is required only to supply its explicit finite cell coverage.
-/

noncomputable section
namespace Papers.RationalityTen.ActualPolygonBoundary

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeEulerThree
open Papers.PolytopeBoundaryIncidence
open BoundarySearch PolygonBoundaryCatalogue ActualFaceTransport

variable {d n c : ℕ}

@[simp] theorem mem_labels (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    {k : ℕ} (F : Face P k) (i : Fin n) :
    i ∈ labels P lab F ↔ (lab.symm i).val ∈ F.val.carrier := by
  constructor
  · intro hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    have he : v = lab.symm i := by simpa using congrArg lab.symm hvi
    subst v
    exact (Finset.mem_filter.mp hv).2
  · intro hi
    exact Finset.mem_image.mpr ⟨lab.symm i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, lab.apply_symm_apply i⟩

theorem labels_injective (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    {k : ℕ} : Function.Injective (labels P lab (k := k)) := by
  intro F G h
  exact faceCode_injective P k ((Finset.image_injective lab.injective) h)

/-- The canonical endpoint pair of a genuine edge. -/
def edgeData (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (E : Face P 1) :
    {p : Fin n × Fin n // p.1 < p.2 ∧ {p.1, p.2} = labels P lab E} := by
  have hex : ∃ p : Fin n × Fin n,
      p.1 < p.2 ∧ {p.1, p.2} = labels P lab E := by
    have hc : (labels P lab E).card = 2 :=
      (labels_card P lab E).trans (one_face_vertex_card P E)
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hc
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨(a, b), hlt, hset.symm⟩
    · exact ⟨(b, a), hgt, by simpa only [Finset.pair_comm] using hset.symm⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

def edgePair (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (E : Face P 1) :
    Fin n × Fin n := (edgeData P lab E).val

theorem edgePair_lt (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (E : Face P 1) :
    (edgePair P lab E).1 < (edgePair P lab E).2 := (edgeData P lab E).property.1

theorem edgePair_labels (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (E : Face P 1) :
    {(edgePair P lab E).1, (edgePair P lab E).2} = labels P lab E :=
  (edgeData P lab E).property.2

theorem edgePair_injective (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) :
    Function.Injective (edgePair P lab) := by
  intro E F h
  apply labels_injective P lab
  rw [← edgePair_labels, ← edgePair_labels, h]

theorem edgePair_vertex_iff (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (E : Face P 1) (i : Fin n) :
    (edgePair P lab E).1 = i ∨ (edgePair P lab E).2 = i ↔
      (lab.symm i).val ∈ E.val.carrier := by
  rw [← mem_labels, ← edgePair_labels]
  simp only [Finset.mem_insert, Finset.mem_singleton, eq_comm]

/-- Complete polygon cell of an actual two-face. -/
def polygon (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (F : Face P 2) :
    Polygon n where
  vertices := labels P lab F
  edges := (actualRidges P 1 F).image (edgePair P lab)

theorem polygon_injective (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) :
    Function.Injective (polygon P lab) := by
  intro F G h
  exact labels_injective P lab (congrArg Polygon.vertices h)

theorem polygon_edge_iff (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 2) (r : Fin n × Fin n) :
    r ∈ (polygon P lab F).edges ↔
      ∃ E : Face P 1, E.val.carrier ⊆ F.val.carrier ∧ edgePair P lab E = r := by
  simp [polygon]

/-- An explicit candidate-cell universe covers an actual polygon boundary. -/
structure Encoding (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (cells : Fin c → Polygon n) where
  index : Face P 2 → Fin c
  index_spec : ∀ F, cells (index F) = polygon P lab F

/-- Coverage is the only input needed to construct the exact encoding. -/
theorem encoding_of_coverage (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (cells : Fin c → Polygon n)
    (h : ∀ F : Face P 2, ∃ i, cells i = polygon P lab F) :
    Nonempty (Encoding P lab cells) := by
  choose f hf using h
  exact ⟨⟨f, hf⟩⟩

/-- Vertex-mask inclusion is exactly actual face inclusion. -/
theorem labels_subset_iff (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    {k l : ℕ} (A : Face P k) (B : Face P l) :
    labels P lab A ⊆ labels P lab B ↔ A.val.carrier ⊆ B.val.carrier := by
  constructor
  · intro h
    rw [face_eq_hull_vertices P A.val.isFace]
    apply convexHull_min
    · intro x hx
      change x ∈ P.vertices.filter (· ∈ A.val.carrier) at hx
      obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
      let v : P.vertices := ⟨x, hxP⟩
      have hvA : lab v ∈ labels P lab A := by
        rw [mem_labels, lab.symm_apply_apply]
        exact hxA
      have hvB := (mem_labels P lab B (lab v)).mp (h hvA)
      simpa only [lab.symm_apply_apply] using hvB
    · exact B.val.isFace.1.convex (convex_convexHull ℝ _)
  · intro h i hi
    exact (mem_labels P lab B i).mpr (h ((mem_labels P lab A i).mp hi))

/-- Two actual polygonal facets meet in a vertex, an edge, or the empty
face. When they share an edge, both cells record precisely that edge. -/
theorem polygons_compatible (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (A B : Face P 2) (hne : A ≠ B) :
    compatible (polygon P lab A) (polygon P lab B) := by
  let I := labels P lab A ∩ labels P lab B
  change I.card ≤ 1 ∨ ∃ e ∈ (polygon P lab A).edges,
    e ∈ (polygon P lab B).edges ∧ I = {e.1, e.2}
  by_cases hI : I = ∅
  · left
    simp [hI]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  have hiAB : (lab.symm i).val ∈ A.val.carrier ∩ B.val.carrier :=
    ⟨(mem_labels P lab A i).mp (Finset.mem_inter.mp hi).1,
      (mem_labels P lab B i).mp (Finset.mem_inter.mp hi).2⟩
  have hface : P.IsFace (A.val.carrier ∩ B.val.carrier) :=
    ⟨A.val.isFace.1.inter B.val.isFace.1, ⟨_, hiAB⟩⟩
  have hproper : A.val.carrier ∩ B.val.carrier ⊂ A.val.carrier := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hback
    have hAB : A.val.carrier ⊆ B.val.carrier := fun x hx => (hback hx).2
    have heq : A.val.carrier = B.val.carrier := by
      by_contra hne
      have hlt := faceDim_lt_of_ssubset P A.val.isFace B.val.isFace
        (hAB.ssubset_of_ne hne)
      rw [A.property, B.property] at hlt
      omega
    exact hne (Subtype.ext (PolytopeFace.ext heq))
  have hlt := faceDim_lt_of_ssubset P hface A.val.isFace hproper
  rw [A.property] at hlt
  have hcases : faceDim (A.val.carrier ∩ B.val.carrier) = 0 ∨
      faceDim (A.val.carrier ∩ B.val.carrier) = 1 := by omega
  rcases hcases with hzero | hedge
  · left
    obtain ⟨x, hx, hIx⟩ := actual_zeroFace_is_vertex P
      (A.val.carrier ∩ B.val.carrier) hface hzero
    let xx : P.vertices := ⟨x, hx⟩
    have heq : I = {lab xx} := by
      ext j
      simp only [I, Finset.mem_inter, mem_labels, Finset.mem_singleton]
      constructor
      · intro hj
        have hjI : (lab.symm j).val ∈ A.val.carrier ∩ B.val.carrier := hj
        have hvx : lab.symm j = xx := Subtype.ext (by
          simpa only [hIx, Set.mem_singleton_iff] using hjI)
        simpa only [lab.apply_symm_apply] using congrArg lab hvx
      · intro hj
        subst j
        rw [lab.symm_apply_apply]
        change x ∈ A.val.carrier ∩ B.val.carrier
        rw [hIx]
        exact Set.mem_singleton x
    simp [heq]
  · right
    let E : Face P 1 := ⟨⟨A.val.carrier ∩ B.val.carrier, hface⟩, hedge⟩
    have hlabels : labels P lab E = I := by
      ext j
      simp only [I, Finset.mem_inter, mem_labels]
      rfl
    refine ⟨edgePair P lab E, ?_, ?_, ?_⟩
    · exact (polygon_edge_iff P lab A _).mpr ⟨E, Set.inter_subset_left, rfl⟩
    · exact (polygon_edge_iff P lab B _).mpr ⟨E, Set.inter_subset_right, rfl⟩
    · rw [edgePair_labels, hlabels]

/-- Every edge of a three-polytope lies in an actual polygonal facet. -/
theorem edge_in_polygon (P : ConvexPolytope d) (hP : P.dim = 3) (A : Face P 1) :
    ∃ F : Face P 2, A.val.carrier ⊆ F.val.carrier := by
  have hproper : A.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P A.val.isFace).ssubset_of_ne ?_
    intro h
    have he := congrArg faceDim h
    change faceDim A.val.carrier = P.dim at he
    rw [A.property, hP] at he
    omega
  obtain ⟨F, hF, hAF, _, hdim⟩ := facet_above_proper_face P A.val.isFace hproper
  have hdF : faceDim F = 2 := by
    change faceDim F + 1 = P.dim at hdim
    omega
  exact ⟨⟨⟨F, hF⟩, hdF⟩, hAF⟩

/-- Incident graph edges and incident one-dimensional faces coincide. -/
def incidentEdgeFaceEquiv (P : ConvexPolytope d) (v : P.vertices) :
    (vertexGraph P).incidenceSet v ≃ IncidentFace P v.val 1 where
  toFun e := ⟨edgeFace P ⟨e.val, e.property.1⟩,
    (edgeFace_vertex_iff P ⟨e.val, e.property.1⟩ v).mpr e.property.2⟩
  invFun F :=
    let e := (edgeFaceEquiv P).symm F.val
    ⟨e.val, e.property, (edgeFace_vertex_iff P e v).mp (by
      have he : edgeFace P e = F.val := (edgeFaceEquiv P).apply_symm_apply F.val
      rw [he]
      exact F.property)⟩
  left_inv e := by
    apply Subtype.ext
    change ((edgeFaceEquiv P).symm ((edgeFaceEquiv P) ⟨e.val, e.property.1⟩)).val = e.val
    exact congrArg (fun z : (vertexGraph P).edgeSet => z.val)
      ((edgeFaceEquiv P).symm_apply_apply ⟨e.val, e.property.1⟩)
  right_inv F := by
    apply Subtype.ext
    exact (edgeFaceEquiv P).apply_symm_apply F.val

theorem incident_face_card_eq_degree (P : ConvexPolytope d) (v : P.vertices) :
    Nat.card (IncidentFace P v.val 1) = (vertexGraph P).degree v := by
  rw [← Nat.card_congr (incidentEdgeFaceEquiv P v), Nat.card_eq_fintype_card]
  exact SimpleGraph.card_incidenceSet_eq_degree (vertexGraph P) v

namespace Encoding
variable {P : ConvexPolytope d} {lab : P.vertices ≃ Fin n}
  {cells : Fin c → Polygon n}

theorem index_injective (E : Encoding P lab cells) : Function.Injective E.index := by
  intro F G h
  apply polygon_injective P lab
  rw [← E.index_spec, ← E.index_spec, h]

def family (E : Encoding P lab cells) : Finset (Fin c) := Finset.univ.image E.index

@[simp] theorem mem_family (E : Encoding P lab cells) (i : Fin c) :
    i ∈ E.family ↔ ∃ F : Face P 2, E.index F = i := by
  simp [family]

theorem family_card (E : Encoding P lab cells) :
    E.family.card = Nat.card (Face P 2) := by
  rw [family, Finset.card_image_of_injective _ E.index_injective, Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

/-- Exact edge-incidence transport. -/
theorem incidence_image (E : Encoding P lab cells) (A : Face P 1) :
    incidence (ridges cells) E.family (edgePair P lab A) =
      (incidence (actualRidges P 1) Finset.univ A).image E.index := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiB, hir⟩ := Finset.mem_filter.mp hi
    obtain ⟨F, hFi⟩ := (E.mem_family i).mp hiB
    rw [ridges, ← hFi, E.index_spec] at hir
    obtain ⟨A', hA'F, hA'A⟩ := (polygon_edge_iff P lab F _).mp hir
    have heq : A' = A := edgePair_injective P lab hA'A
    subst A'
    exact Finset.mem_image.mpr ⟨F,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_actualRidges P 1 F A).mpr hA'F⟩,
      hFi⟩
  · intro hi
    obtain ⟨F, hF, hFi⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨(E.mem_family i).mpr ⟨F, hFi⟩, ?_⟩
    rw [ridges, ← hFi, E.index_spec]
    exact (polygon_edge_iff P lab F _).mpr ⟨A,
      (mem_actualRidges P 1 F A).mp (Finset.mem_filter.mp hF).2, rfl⟩

/-- Each encoded edge belongs to exactly two actual polygonal facets;
a pair that is not an actual edge has no incidences. -/
theorem edge_pairing (E : Encoding P lab cells) (hP : P.dim = 3) :
    ∀ r : Fin n × Fin n,
      (incidence (ridges cells) E.family r).card = 0 ∨
      (incidence (ridges cells) E.family r).card = 2 := by
  intro r
  by_cases hex : ∃ A : Face P 1, edgePair P lab A = r
  · obtain ⟨A, rfl⟩ := hex
    right
    rw [E.incidence_image, Finset.card_image_of_injective _ E.index_injective]
    exact actual_ridge_incidence_card P 1 hP A
  · left
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hiB, hir⟩ := Finset.mem_filter.mp hi
    obtain ⟨F, hFi⟩ := (E.mem_family i).mp hiB
    rw [ridges, ← hFi, E.index_spec] at hir
    obtain ⟨A, _, hAr⟩ := (polygon_edge_iff P lab F r).mp hir
    exact hex ⟨A, hAr⟩

/-- Connectedness of the genuine polytope boundary, expressed on the
literal candidate-cell indices. -/
theorem ridge_connected (E : Encoding P lab cells) (hP : P.dim = 3) :
    RidgeConnected (ridges cells) E.family := by
  intro S hSB hSne hSneq
  let T : Finset (Face P 2) := Finset.univ.filter fun F => E.index F ∈ S
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hSne
    obtain ⟨F, hFi⟩ := (E.mem_family i).mp (hSB hi)
    exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hFi] using hi⟩⟩
  have hTneq : T ≠ Finset.univ := by
    intro hT
    apply hSneq
    apply Finset.Subset.antisymm hSB
    intro i hi
    obtain ⟨F, hFi⟩ := (E.mem_family i).mp hi
    have hF : F ∈ T := by rw [hT]; exact Finset.mem_univ _
    exact hFi ▸ (Finset.mem_filter.mp hF).2
  obtain ⟨A, hA, B, _, hBT, R, hRA, hRB⟩ :=
    actual_boundary_ridge_connected P 1 hP T (Finset.filter_subset _ _) hTne hTneq
  have hiA : E.index A ∈ S := (Finset.mem_filter.mp hA).2
  have hiB : E.index B ∉ S := by
    intro hi
    exact hBT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  refine ⟨E.index A, hiA, E.index B, (E.mem_family _).mpr ⟨B, rfl⟩, hiB,
    edgePair P lab R, ?_, ?_⟩
  · rw [ridges, E.index_spec]
    exact Finset.mem_image.mpr ⟨R, hRA, rfl⟩
  · rw [ridges, E.index_spec]
    exact Finset.mem_image.mpr ⟨R, hRB, rfl⟩

/-- All pairs of selected cells satisfy the literal polygon compatibility
predicate used by the checked finite catalogue. -/
theorem pairwise_compatible (E : Encoding P lab cells) :
    (E.family : Set (Fin c)).Pairwise fun i j => compatible (cells i) (cells j) := by
  intro i hi j hj hij
  obtain ⟨A, hAi⟩ := (E.mem_family i).mp hi
  obtain ⟨B, hBj⟩ := (E.mem_family j).mp hj
  have hAB : A ≠ B := by
    intro h
    exact hij (hAi.symm.trans ((congrArg E.index h).trans hBj))
  rw [← hAi, ← hBj, E.index_spec, E.index_spec]
  exact polygons_compatible P lab A B hAB

/-- The union of encoded polygon edges is the complete actual edge set. -/
theorem edges_eq_actual (E : Encoding P lab cells) (hP : P.dim = 3) :
    edges cells E.family =
      (Finset.univ : Finset (Face P 1)).image (edgePair P lab) := by
  ext r
  constructor
  · intro hr
    obtain ⟨i, hi, hir⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨F, hFi⟩ := (E.mem_family i).mp hi
    rw [← hFi, E.index_spec] at hir
    obtain ⟨A, _, hAr⟩ := (polygon_edge_iff P lab F r).mp hir
    exact Finset.mem_image.mpr ⟨A, Finset.mem_univ _, hAr⟩
  · intro hr
    obtain ⟨A, _, hAr⟩ := Finset.mem_image.mp hr
    obtain ⟨F, hAF⟩ := edge_in_polygon P hP A
    apply Finset.mem_biUnion.mpr
    refine ⟨E.index F, (E.mem_family _).mpr ⟨F, rfl⟩, ?_⟩
    rw [E.index_spec]
    exact (polygon_edge_iff P lab F r).mpr ⟨A, hAF, hAr⟩

theorem edge_card (E : Encoding P lab cells) (hP : P.dim = 3) :
    (edges cells E.family).card = Nat.card (Face P 1) := by
  rw [E.edges_eq_actual hP, Finset.card_image_of_injective _ (edgePair_injective P lab),
    Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

/-- The literal vertex degree counts actual edges incident to that vertex. -/
theorem vertexDegree_eq (E : Encoding P lab cells) (hP : P.dim = 3) (i : Fin n) :
    vertexDegree cells E.family i = (vertexGraph P).degree (lab.symm i) := by
  unfold vertexDegree
  rw [E.edges_eq_actual hP, Finset.filter_image]
  simp_rw [edgePair_vertex_iff]
  rw [Finset.card_image_of_injective _ (edgePair_injective P lab)]
  have hc : ((Finset.univ : Finset (Face P 1)).filter
      (fun A => (lab.symm i).val ∈ A.val.carrier)).card =
      Nat.card (IncidentFace P (lab.symm i).val 1) := by
    simp only [IncidentFace, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  exact incident_face_card_eq_degree P (lab.symm i)

/-- Every numeric and incidence hypothesis in the polygon catalogue's
`valid` predicate follows from actual convex geometry. -/
theorem valid_boundary (E : Encoding P lab cells) (hP : P.dim = 3) :
    valid cells E.family := by
  refine ⟨E.edge_pairing hP, ?_, ?_⟩
  · intro i
    rw [E.vertexDegree_eq hP]
    simpa only [hP] using graph_degree_ge_dimension P (lab.symm i)
  · have hn : P.vertices.card = n := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr lab
    rw [E.family_card, E.edge_card hP, ← hn]
    exact vertices_add_faces_eq_edges_add_two P hP

/-- The finite catalogue's facet-count bound is also a geometric theorem. -/
theorem family_card_le (E : Encoding P lab cells) (hP : P.dim = 3) :
    E.family.card ≤ 2 * n - 4 := by
  have hn : P.vertices.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr lab
  rw [E.family_card, ← hn]
  exact actual_face_bound P hP

/-- The selected cells are precisely all actual polygonal facets. -/
theorem exact_family (E : Encoding P lab cells) :
    E.family.image cells =
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) := by
  simp only [family, Finset.image_image]
  congr 1
  funext F
  exact E.index_spec F

end Encoding
end Papers.RationalityTen.ActualPolygonBoundary

end
end
end BundlePart2

section BundlePart3
/- Source: CycleCandidateGeometry.lean -/





@[expose] public section

/-!
# Actual polygons belong to a finite cycle candidate universe

The finite universe is parameterized by injections from a cycle graph.
All edges are included and adjacency is reflected. This converts the
remaining catalogue-coverage obligation into a finite statement about
cycles on at most seven labels, with no realization hypothesis.
-/

noncomputable section
namespace Papers.RationalityTen.ActualPolygonBoundary

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeBoundaryIncidence
open Papers.PolytopeCyclicLabeling
open PolygonBoundaryCatalogue ActualFaceTransport

variable {d n k : ℕ}

/-- Canonical ordering loses no information about a two-element set. -/
theorem sorted_pair_unique (a b : Fin n × Fin n) (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2)
    (h : ({a.1, a.2} : Finset (Fin n)) = {b.1, b.2}) : a = b := by
  have hs : ({a.1, a.2} : Set (Fin n)) = {b.1, b.2} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun S : Finset (Fin n) => (S : Set (Fin n))) h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · have he : a₁ = a₂ := le_antisymm ha hb
    subst a₂
    rfl

/-- A polygon edge is exactly an ambient graph edge on two of its vertices,
represented in increasing order. -/
theorem polygon_edge_geometric_iff (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 2) (r : Fin n × Fin n) :
    r ∈ (polygon P lab F).edges ↔ r.1 < r.2 ∧
      r.1 ∈ labels P lab F ∧ r.2 ∈ labels P lab F ∧
      (vertexGraph P).Adj (lab.symm r.1) (lab.symm r.2) := by
  constructor
  · intro hr
    obtain ⟨E, hEF, hEr⟩ := (polygon_edge_iff P lab F r).mp hr
    subst r
    have hv₁ := (edgePair_vertex_iff P lab E (edgePair P lab E).1).mp (Or.inl rfl)
    have hv₂ := (edgePair_vertex_iff P lab E (edgePair P lab E).2).mp (Or.inr rfl)
    refine ⟨edgePair_lt P lab E, (mem_labels P lab F _).mpr (hEF hv₁),
      (mem_labels P lab F _).mpr (hEF hv₂), ?_⟩
    refine ⟨(lab.symm (edgePair P lab E).2).property, ?_, E.val.carrier,
      E.val.isFace, E.property, hv₁, hv₂⟩
    intro he
    have he' := congrArg lab (Subtype.ext he :
      lab.symm (edgePair P lab E).1 = lab.symm (edgePair P lab E).2)
    exact (ne_of_lt (edgePair_lt P lab E)) (by simpa using he')
  · rintro ⟨hr, hv₁, hv₂, hadj⟩
    let v := lab.symm r.1
    let w := lab.symm r.2
    let e : (vertexGraph P).edgeSet := ⟨s(v, w), hadj⟩
    let E := edgeFace P e
    have hlabels : labels P lab E = {r.1, r.2} := by
      ext i
      rw [mem_labels, edgeFace_vertex_iff]
      change lab.symm i ∈ s(lab.symm r.1, lab.symm r.2) ↔ i ∈ ({r.1, r.2} : Finset (Fin n))
      simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      exact or_congr lab.symm.injective.eq_iff lab.symm.injective.eq_iff
    have hpair : edgePair P lab E = r :=
      sorted_pair_unique _ _ (edgePair_lt P lab E).le hr.le
        ((edgePair_labels P lab E).trans hlabels)
    apply (polygon_edge_iff P lab F r).mpr
    refine ⟨E, (labels_subset_iff P lab E F).mp ?_, hpair⟩
    rw [hlabels]
    exact Finset.insert_subset_iff.mpr ⟨hv₁, Finset.singleton_subset_iff.mpr hv₂⟩

/-- Restricting to a face preserves and reflects adjacency on its actual
vertices. Convexity ensures that an ambient edge with both endpoints in
the face is an edge of the face polytope. -/
theorem face_vertex_adj_iff (P : ConvexPolytope d) (F : Face P 2)
    (x y : (facePolytope P F.val.isFace).vertices) :
    (vertexGraph (facePolytope P F.val.isFace)).Adj x y ↔
      (vertexGraph P).Adj (includeVertex P F x) (includeVertex P F y) := by
  constructor
  · rintro ⟨hy, hxy, A, hA, hdA, hxA, hyA⟩
    exact ⟨(Finset.mem_filter.mp hy).1, hxy, A,
      isFace_of_facePolytope P F.val.isFace hA, hdA, hxA, hyA⟩
  · intro hxy
    have hxP := (Finset.mem_filter.mp x.property).1
    have hxF := (Finset.mem_filter.mp x.property).2
    have hyF := (Finset.mem_filter.mp y.property).2
    have hs := segment_isFace_of_generalVertexStep P hxP hxy
    have hd := segment_faceDim_of_generalVertexStep P hxP hxy
    have hconv : Convex ℝ F.val.carrier :=
      F.val.isFace.1.convex (convex_convexHull ℝ _)
    have hsub : segment ℝ x.val y.val ⊆ F.val.carrier := hconv.segment_subset hxF hyF
    exact ⟨y.property, hxy.2.1, segment ℝ x.val y.val,
      facePolytope_isFace_of P F.val.isFace hs hsub, hd,
      left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩

/-- The cycle candidate contains all vertices and exactly the edges of the
cycle graph. There are no hidden or omitted chords. -/
def cyclePolygon (f : Fin k ↪ Fin n) : Polygon n where
  vertices := (Finset.univ : Finset (Fin k)).image f
  edges := ((Finset.univ : Finset (Fin k × Fin k)).filter
    (fun ij => (SimpleGraph.cycleGraph k).Adj ij.1 ij.2)).image
      (fun ij => orderedEdge (f ij.1) (f ij.2))

theorem polygon_ext (A B : Polygon n) (hv : A.vertices = B.vertices)
    (he : A.edges = B.edges) : A = B := by
  cases A
  cases B
  cases hv
  cases he
  rfl

/-- Every actual polygon is exactly a candidate obtained from its cyclic
vertex labeling. -/
theorem polygon_eq_cycle (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 2) :
    ∃ f : Fin (facePolytope P F.val.isFace).vertices.card ↪ Fin n,
      polygon P lab F = cyclePolygon f := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 2 := by
    change faceDim Q.toSet = 2
    rw [facePolytope_toSet]
    exact F.property
  obtain ⟨cy⟩ := actual_polygon_cyclic_labeling Q hQ
  let loc : Q.vertices ≃ Fin Q.vertices.card := cy.toEquiv.symm
  let f : Fin Q.vertices.card ↪ Fin n := labelEmbedding P lab F loc
  have hf (i : Fin Q.vertices.card) : f i = lab (includeVertex P F (cy i)) := rfl
  have hv : (Finset.univ : Finset (Fin Q.vertices.card)).image f = labels P lab F :=
    vertices_image P lab F loc
  have hadj (i j : Fin Q.vertices.card) :
      (SimpleGraph.cycleGraph Q.vertices.card).Adj i j ↔
        (vertexGraph P).Adj (lab.symm (f i)) (lab.symm (f j)) := by
    rw [hf, hf, lab.symm_apply_apply, lab.symm_apply_apply]
    exact cy.map_adj_iff.symm.trans (face_vertex_adj_iff P F (cy i) (cy j))
  refine ⟨f, polygon_ext _ _ hv.symm ?_⟩
  ext r
  constructor
  · intro hr
    obtain ⟨hrlt, hr₁, hr₂, hrAdj⟩ := (polygon_edge_geometric_iff P lab F r).mp hr
    rw [← hv] at hr₁ hr₂
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr₁
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr₂
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · apply (hadj i j).mpr
      simpa only [hi, hj] using hrAdj
    · simp only [hi, hj, orderedEdge, if_pos hrlt.le, Prod.eta]
  · intro hr
    obtain ⟨⟨i, j⟩, hij, hpair⟩ := Finset.mem_image.mp hr
    have hijAdj := (Finset.mem_filter.mp hij).2
    have hne : f i ≠ f j := fun h =>
      (SimpleGraph.ne_of_adj _ hijAdj) (f.injective h)
    have hfi : f i ∈ labels P lab F := by
      rw [← hv]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hfj : f j ∈ labels P lab F := by
      rw [← hv]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hAdj := (hadj i j).mp hijAdj
    apply (polygon_edge_geometric_iff P lab F r).mpr
    rw [← hpair]
    by_cases hle : f i ≤ f j
    · simp only [orderedEdge, if_pos hle]
      exact ⟨lt_of_le_of_ne hle hne, hfi, hfj, hAdj⟩
    · simp only [orderedEdge, if_neg hle]
      exact ⟨lt_of_not_ge hle, hfj, hfi, hAdj.symm⟩

/-- A proper polygonal facet has strictly fewer vertices than the actual
three-dimensional polytope. -/
theorem polygon_vertex_count_lt (P : ConvexPolytope d) (hP : P.dim = 3)
    (F : Face P 2) : (facePolytope P F.val.isFace).vertices.card < P.vertices.card := by
  have hproper := proper_facet P 2 hP F
  have hsub : (facePolytope P F.val.isFace).vertices ⊆ P.vertices :=
    Finset.filter_subset _ _
  have hne : (facePolytope P F.val.isFace).vertices ≠ P.vertices := by
    intro heq
    have hs : (facePolytope P F.val.isFace).toSet = P.toSet := by
      change convexHull ℝ (↑(facePolytope P F.val.isFace).vertices : Set (E d)) =
        convexHull ℝ (↑P.vertices : Set (E d))
      rw [heq]
    rw [facePolytope_toSet] at hs
    exact hproper.ne hs
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- Every actual polygonal facet lies in the finite candidate universe of
cycles of length between three and one less than the total vertex count. -/
theorem actual_cycle_candidate (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (hP : P.dim = 3) (F : Face P 2) :
    ∃ k, 3 ≤ k ∧ k < n ∧ ∃ f : Fin k ↪ Fin n, polygon P lab F = cyclePolygon f := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 2 := by
    change faceDim Q.toSet = 2
    rw [facePolytope_toSet]
    exact F.property
  have hmin := actual_vertices_card_gt_dim Q
  rw [hQ] at hmin
  have hmax := polygon_vertex_count_lt P hP F
  have hn : P.vertices.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr lab
  rw [hn] at hmax
  obtain ⟨f, hf⟩ := polygon_eq_cycle P lab F
  exact ⟨Q.vertices.card, by omega, hmax, f, hf⟩

end Papers.RationalityTen.ActualPolygonBoundary

end
end
end BundlePart3

section BundlePart4
/- Source: RootedCatalogueGeometry.lean -/




@[expose] public section

/-!
# From actual convex geometry to the normalized finite catalogue

The two remaining coverage hypotheses in this file are finite statements
about cycle candidates and permutations of their labels. All statements
about an actual polytope—root existence, a second facet on the root edge,
face compatibility, edge pairing, connectedness, degree and Euler—are
proved here or in the preceding geometry files.
-/

noncomputable section
namespace Papers.RationalityTen.ActualPolygonBoundary

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeBoundaryIncidence
open Papers.PolytopeCyclicLabeling
open PolygonBoundaryCatalogue BoundarySearch ActualFaceTransport

variable {d n c t : ℕ}

theorem orderedEdge_le (a b : Fin n) : (orderedEdge a b).1 ≤ (orderedEdge a b).2 := by
  unfold orderedEdge
  split_ifs with h
  · exact h
  · exact (le_of_not_ge h)

theorem orderedEdge_vertices (a b : Fin n) :
    ({(orderedEdge a b).1, (orderedEdge a b).2} : Finset (Fin n)) = {a, b} := by
  unfold orderedEdge
  split_ifs <;> simp only [Finset.pair_comm]

/-- Canonical edge pairs commute with arbitrary vertex relabeling. -/
theorem edgePair_relabel (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (σ : Equiv.Perm (Fin n)) (E : Face P 1) :
    edgePair P (lab.trans σ) E =
      orderedEdge (σ (edgePair P lab E).1) (σ (edgePair P lab E).2) := by
  apply sorted_pair_unique _ _ (edgePair_lt P (lab.trans σ) E).le (orderedEdge_le _ _)
  rw [orderedEdge_vertices, edgePair_labels, labels_relabel, ← edgePair_labels]
  simp only [Finset.image_insert, Finset.image_singleton]

/-- The complete actual polygon, including its edge cycle, is transported
by relabeling. -/
theorem polygon_relabel (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (σ : Equiv.Perm (Fin n)) (F : Face P 2) :
    polygon P (lab.trans σ) F = relabelPolygon σ (polygon P lab F) := by
  apply polygon_ext
  · exact labels_relabel P lab σ F
  · change (actualRidges P 1 F).image (edgePair P (lab.trans σ)) =
      ((actualRidges P 1 F).image (edgePair P lab)).image
        (fun e => orderedEdge (σ e.1) (σ e.2))
    rw [Finset.image_image]
    congr 1
    funext E
    exact edgePair_relabel P lab σ E

/-- The normalized triangle records every one of its three edges. -/
def rootTriangle (n : ℕ) (hn : 3 ≤ n) : Polygon n where
  vertices := firstLabels n 3 hn
  edges := (Finset.univ : Finset (Fin n × Fin n)).filter fun e =>
    e.1 < e.2 ∧ e.1 ∈ firstLabels n 3 hn ∧ e.2 ∈ firstLabels n 3 hn

def rootEdge (n : ℕ) (hn : 3 ≤ n) : Fin n × Fin n :=
  (Fin.castLE hn (0 : Fin 3), Fin.castLE hn (1 : Fin 3))

theorem rootEdge_mem (hn : 3 ≤ n) : rootEdge n hn ∈ (rootTriangle n hn).edges := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · change (0 : ℕ) < 1
    decide
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩

/-- A genuine triangle has all three possible edges. This uses the actual
cyclic graph, rather than assigning edges by definition. -/
theorem triangle_vertices_adj (P : ConvexPolytope d) (F : Face P 2)
    (hF : Nat.card (VerticesOn P F.val.carrier) = 3)
    (x y : P.vertices) (hx : x.val ∈ F.val.carrier) (hy : y.val ∈ F.val.carrier)
    (hne : x ≠ y) : (vertexGraph P).Adj x y := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 2 := by
    change faceDim Q.toSet = 2
    rw [facePolytope_toSet]
    exact F.property
  have hcard : Q.vertices.card = 3 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm.trans hF
  obtain ⟨cy⟩ := actual_polygon_cyclic_labeling Q hQ
  let x' : Q.vertices := ⟨x.val, Finset.mem_filter.mpr ⟨x.property, hx⟩⟩
  let y' : Q.vertices := ⟨y.val, Finset.mem_filter.mpr ⟨y.property, hy⟩⟩
  have hxy : x' ≠ y' := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun z : Q.vertices => z.val) h
  have hcomplete : SimpleGraph.cycleGraph Q.vertices.card = ⊤ := by
    rw [hcard]
    exact SimpleGraph.cycleGraph_three_eq_top
  have hadj_of_ne : ∀ a b : Fin Q.vertices.card, a ≠ b →
      (SimpleGraph.cycleGraph Q.vertices.card).Adj a b := by
    intro a b hab
    simpa only [hcomplete, SimpleGraph.top_adj] using hab
  have hAdj : (vertexGraph Q).Adj x' y' := by
    have hne' : cy.symm x' ≠ cy.symm y' := fun h => hxy (cy.symm.injective h)
    have hc := hadj_of_ne (cy.symm x') (cy.symm y') hne'
    exact cy.symm.map_adj_iff.mp hc
  exact (face_vertex_adj_iff P F x' y').mp hAdj

theorem normalized_triangle_eq (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 2) (hn : 3 ≤ n)
    (hF : Nat.card (VerticesOn P F.val.carrier) = 3)
    (hlabels : labels P lab F = firstLabels n 3 hn) :
    polygon P lab F = rootTriangle n hn := by
  apply polygon_ext _ _ hlabels
  ext r
  rw [polygon_edge_geometric_iff]
  change _ ↔ r ∈ (Finset.univ : Finset (Fin n × Fin n)).filter _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hlabels]
  constructor
  · rintro ⟨h, h₁, h₂, _⟩
    exact ⟨h, h₁, h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨h, h₁, h₂, triangle_vertices_adj P F hF (lab.symm r.1) (lab.symm r.2)
      ((mem_labels P lab F r.1).mp h₁) ((mem_labels P lab F r.2).mp h₂) ?_⟩
    intro he
    exact (ne_of_lt h) (lab.symm.injective he)

/-- Every edge of a three-polytope belongs to a second, distinct facet. -/
theorem second_polygon_on_edge (P : ConvexPolytope d) (hP : P.dim = 3)
    (F : Face P 2) (A : Face P 1) (hAF : A.val.carrier ⊆ F.val.carrier) :
    ∃ G : Face P 2, G ≠ F ∧ A.val.carrier ⊆ G.val.carrier := by
  let S : Finset (Face P 2) := Finset.univ.filter fun G => A.val.carrier ⊆ G.val.carrier
  have hcard : S.card = 2 := by
    have h := ridge_coface_card P 1 hP A
    simpa only [S, Coface, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  obtain ⟨G, hG, hGF⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) F
  exact ⟨G, hGF, (Finset.mem_filter.mp hG).2⟩

/-- Pure finite coverage: every cycle compatible with the normalized root
appears in the literal candidate universe. -/
def CoversRootedCycles (cells : Fin c → Polygon n) (root : Polygon n) : Prop :=
  ∀ k, 3 ≤ k → k < n → ∀ f : Fin k ↪ Fin n,
    cyclePolygon f = root ∨ compatible (cyclePolygon f) root →
      ∃ i, cells i = cyclePolygon f

/-- Pure finite normalization: the other polygon on the distinguished
root edge can be relabeled to one of the listed neighbor cells while
preserving the normalized triangular root. -/
def NormalizesRootNeighbor (cells : Fin c → Polygon n) (neighbors : Finset (Fin c))
    (hn : 3 ≤ n) : Prop :=
  ∀ k, 3 ≤ k → k < n → ∀ f : Fin k ↪ Fin n,
    compatible (cyclePolygon f) (rootTriangle n hn) →
    rootEdge n hn ∈ (cyclePolygon f).edges →
    ∃ σ : Equiv.Perm (Fin n),
      relabelPolygon σ (rootTriangle n hn) = rootTriangle n hn ∧
      ∃ i ∈ neighbors, cells i = relabelPolygon σ (cyclePolygon f)

/-- An actual three-polytope enters the normalized finite search once the
two explicit finite cycle-coverage facts have been checked. All geometric
search hypotheses are established, not assumed. -/
theorem actual_rooted_encoding (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = n) (hsmall : n ≤ 7) (hthree : 3 ≤ n)
    (cells : Fin c → Polygon n) (root : Fin c) (neighbors : Finset (Fin c))
    (hinj : Function.Injective cells) (hroot : cells root = rootTriangle n hthree)
    (hcover : CoversRootedCycles cells (rootTriangle n hthree))
    (hnormalize : NormalizesRootNeighbor cells neighbors hthree) :
    ∃ (lab : P.vertices ≃ Fin n) (E : Encoding P lab cells),
      root ∈ E.family ∧ (E.family ∩ neighbors).Nonempty := by
  have hsmallP : P.vertices.card ≤ 7 := by omega
  obtain ⟨R, hR⟩ := actual_triangle P hP hsmallP
  let initial := P.vertices.equivFinOfCardEq hn
  obtain ⟨σ₀, hσ₀⟩ := normalize_triangle P initial R hR hthree
  let lab := initial.trans σ₀
  have hRroot : polygon P lab R = rootTriangle n hthree :=
    normalized_triangle_eq P lab R hthree hR hσ₀
  have hedge : rootEdge n hthree ∈ (polygon P lab R).edges := by
    rw [hRroot]
    exact rootEdge_mem hthree
  obtain ⟨A, hAR, hAedge⟩ := (polygon_edge_iff P lab R _).mp hedge
  obtain ⟨G, hGR, hAG⟩ := second_polygon_on_edge P hP R A hAR
  have hGedge : rootEdge n hthree ∈ (polygon P lab G).edges :=
    (polygon_edge_iff P lab G _).mpr ⟨A, hAG, hAedge⟩
  have hGRcompat : compatible (polygon P lab G) (rootTriangle n hthree) := by
    rw [← hRroot]
    exact polygons_compatible P lab G R hGR
  obtain ⟨k, hk, hkn, f, hGf⟩ := actual_cycle_candidate P lab hP G
  obtain ⟨σ, hσroot, j, hjN, hj⟩ := hnormalize k hk hkn f
    (by simpa only [← hGf] using hGRcompat) (by simpa only [← hGf] using hGedge)
  let lab' := lab.trans σ
  have hRroot' : polygon P lab' R = rootTriangle n hthree := by
    rw [polygon_relabel, hRroot]
    exact hσroot
  have hj' : cells j = polygon P lab' G := by
    rw [polygon_relabel, hGf]
    exact hj
  have hcoverage : ∀ F : Face P 2, ∃ i, cells i = polygon P lab' F := by
    intro F
    obtain ⟨k, hk, hkn, f, hFf⟩ := actual_cycle_candidate P lab' hP F
    rw [hFf]
    apply hcover k hk hkn f
    by_cases hFR : F = R
    · left
      rw [← hFf, hFR]
      exact hRroot'
    · right
      rw [← hFf, ← hRroot']
      exact polygons_compatible P lab' F R hFR
  obtain ⟨E⟩ := encoding_of_coverage P lab' cells hcoverage
  have hindexR : E.index R = root := hinj ((E.index_spec R).trans (hRroot'.trans hroot.symm))
  have hindexG : E.index G = j := hinj ((E.index_spec G).trans hj'.symm)
  refine ⟨lab', E, (E.mem_family root).mpr ⟨R, hindexR⟩, ?_⟩
  exact ⟨j, Finset.mem_inter.mpr ⟨(E.mem_family j).mpr ⟨G, hindexG⟩, hjN⟩⟩

/-- A complete pure normalized classification becomes a classification of
all actual convex three-polytopes of the given size. The conclusion is
literal equality of complete labeled polygon boundaries. -/
theorem actual_classification_of_finite (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = n) (hsmall : n ≤ 7) (hthree : 3 ≤ n)
    (cells : Fin c → Polygon n) (root : Fin c) (neighbors : Finset (Fin c))
    (templates : Fin t → Finset (Polygon n))
    (hinj : Function.Injective cells) (hroot : cells root = rootTriangle n hthree)
    (hcover : CoversRootedCycles cells (rootTriangle n hthree))
    (hnormalize : NormalizesRootNeighbor cells neighbors hthree)
    (hclass : ∀ S : Finset (Fin c), S.card ≤ 2 * n - 4 →
      (S : Set _).Pairwise (fun i j => compatible (cells i) (cells j)) →
      valid cells S → RidgeConnected (ridges cells) S →
      root ∈ S → (S ∩ neighbors).Nonempty →
      ∃ (σ : Equiv.Perm (Fin n)) (i : Fin t), relabelBoundary cells σ S = templates i) :
    ∃ (lab : P.vertices ≃ Fin n) (i : Fin t),
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) = templates i := by
  obtain ⟨lab, E, hR, hN⟩ := actual_rooted_encoding P hP hn hsmall hthree
    cells root neighbors hinj hroot hcover hnormalize
  obtain ⟨σ, i, hi⟩ := hclass E.family (E.family_card_le hP)
    E.pairwise_compatible (E.valid_boundary hP) (E.ridge_connected hP) hR hN
  refine ⟨lab.trans σ, i, ?_⟩
  have heq : (Finset.univ : Finset (Face P 2)).image (polygon P (lab.trans σ)) =
      relabelBoundary cells σ E.family := by
    calc
      _ = (Finset.univ : Finset (Face P 2)).image
          (fun F => relabelPolygon σ (polygon P lab F)) := by
        congr 1
        funext F
        exact polygon_relabel P lab σ F
      _ = ((Finset.univ : Finset (Face P 2)).image (polygon P lab)).image
          (relabelPolygon σ) := by rw [Finset.image_image]; rfl
      _ = (E.family.image cells).image (relabelPolygon σ) := by rw [E.exact_family]
      _ = relabelBoundary cells σ E.family := by
        rw [Finset.image_image]
        rfl
  exact heq.trans hi

end Papers.RationalityTen.ActualPolygonBoundary

end
end
end BundlePart4

section BundlePart5
/- Source: ConcreteRootCoverageSmall.lean -/







@[expose] public section
noncomputable section

namespace Papers.RationalityTen.FiniteCycleCandidates
open ActualPolygonBoundary PolygonBoundaryCatalogue

namespace N4

theorem covers_rooted_cycles :
    CoversRootedCycles cells (rootTriangle 4 (by decide)) := by
  intro k hk hkn f h
  have cases : k = 3 := by omega
  rcases cases with rfl
  · exact covered_3 f f.injective h

theorem normalizes_root_neighbor :
    NormalizesRootNeighbor cells neighbors (by decide : 3 ≤ 4) := by
  intro k hk hkn f hcompat hedge
  have cases : k = 3 := by omega
  rcases cases with rfl
  · obtain ⟨a, i, hi, heq⟩ := neighbor_3 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a

end N4

namespace N5

theorem covers_rooted_cycles :
    CoversRootedCycles cells (rootTriangle 5 (by decide)) := by
  intro k hk hkn f h
  have cases : k = 3 ∨ k = 4 := by omega
  rcases cases with rfl | rfl
  · exact covered_3 f f.injective h
  · exact covered_4 f f.injective h

theorem normalizes_root_neighbor :
    NormalizesRootNeighbor cells neighbors (by decide : 3 ≤ 5) := by
  intro k hk hkn f hcompat hedge
  have cases : k = 3 ∨ k = 4 := by omega
  rcases cases with rfl | rfl
  · obtain ⟨a, i, hi, heq⟩ := neighbor_3 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_4 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a

end N5

end Papers.RationalityTen.FiniteCycleCandidates

end
end
end BundlePart5

section BundlePart6
/- Source: FiniteCycleData7.lean -/





@[expose] public section

namespace Papers.RationalityTen.FiniteCycleCandidates
open MatroidChecked PolygonBoundaryCatalogue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace N7
noncomputable def cellTable : LiteralLookup (Polygon 7) := (.node 145 (.node 72 (.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩)) (.leaf (⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩))) (.node 3 (.leaf (⟨{0,1,4},{(0,1),(0,4),(1,4)}⟩)) (.leaf (⟨{0,1,5},{(0,1),(0,5),(1,5)}⟩)))) (.node 6 (.node 5 (.leaf (⟨{0,1,6},{(0,1),(0,6),(1,6)}⟩)) (.leaf (⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩))) (.node 7 (.leaf (⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩)) (.node 8 (.leaf (⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩)) (.leaf (⟨{0,2,6},{(0,2),(0,6),(2,6)}⟩)))))) (.node 13 (.node 11 (.node 10 (.leaf (⟨{0,3,4},{(0,3),(0,4),(3,4)}⟩)) (.leaf (⟨{0,3,5},{(0,3),(0,5),(3,5)}⟩))) (.node 12 (.leaf (⟨{0,3,6},{(0,3),(0,6),(3,6)}⟩)) (.leaf (⟨{0,4,5},{(0,4),(0,5),(4,5)}⟩)))) (.node 15 (.node 14 (.leaf (⟨{0,4,6},{(0,4),(0,6),(4,6)}⟩)) (.leaf (⟨{0,5,6},{(0,5),(0,6),(5,6)}⟩))) (.node 16 (.leaf (⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩)) (.node 17 (.leaf (⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩)) (.leaf (⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩))))))) (.node 27 (.node 22 (.node 20 (.node 19 (.leaf (⟨{1,2,6},{(1,2),(1,6),(2,6)}⟩)) (.leaf (⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩))) (.node 21 (.leaf (⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩)) (.leaf (⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩)))) (.node 24 (.node 23 (.leaf (⟨{1,4,5},{(1,4),(1,5),(4,5)}⟩)) (.leaf (⟨{1,4,6},{(1,4),(1,6),(4,6)}⟩))) (.node 25 (.leaf (⟨{1,5,6},{(1,5),(1,6),(5,6)}⟩)) (.node 26 (.leaf (⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩)) (.leaf (⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩)))))) (.node 31 (.node 29 (.node 28 (.leaf (⟨{2,3,6},{(2,3),(2,6),(3,6)}⟩)) (.leaf (⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩))) (.node 30 (.leaf (⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩)) (.leaf (⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩)))) (.node 33 (.node 32 (.leaf (⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩)) (.leaf (⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩))) (.node 34 (.leaf (⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩)) (.node 35 (.leaf (⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩)) (.leaf (⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩)))))))) (.node 54 (.node 45 (.node 40 (.node 38 (.node 37 (.leaf (⟨{0,1,3,4},{(0,1),(0,3),(1,4),(3,4)}⟩)) (.leaf (⟨{0,1,3,5},{(0,1),(0,5),(1,3),(3,5)}⟩))) (.node 39 (.leaf (⟨{0,1,3,5},{(0,1),(0,3),(1,5),(3,5)}⟩)) (.leaf (⟨{0,1,3,6},{(0,1),(0,6),(1,3),(3,6)}⟩)))) (.node 42 (.node 41 (.leaf (⟨{0,1,3,6},{(0,1),(0,3),(1,6),(3,6)}⟩)) (.leaf (⟨{0,1,4,5},{(0,1),(0,5),(1,4),(4,5)}⟩))) (.node 43 (.leaf (⟨{0,1,4,5},{(0,1),(0,4),(1,5),(4,5)}⟩)) (.node 44 (.leaf (⟨{0,1,4,6},{(0,1),(0,6),(1,4),(4,6)}⟩)) (.leaf (⟨{0,1,4,6},{(0,1),(0,4),(1,6),(4,6)}⟩)))))) (.node 49 (.node 47 (.node 46 (.leaf (⟨{0,1,5,6},{(0,1),(0,6),(1,5),(5,6)}⟩)) (.leaf (⟨{0,1,5,6},{(0,1),(0,5),(1,6),(5,6)}⟩))) (.node 48 (.leaf (⟨{0,2,3,4},{(0,2),(0,4),(2,3),(3,4)}⟩)) (.leaf (⟨{0,2,3,4},{(0,2),(0,3),(2,4),(3,4)}⟩)))) (.node 51 (.node 50 (.leaf (⟨{0,2,3,5},{(0,2),(0,5),(2,3),(3,5)}⟩)) (.leaf (⟨{0,2,3,5},{(0,2),(0,3),(2,5),(3,5)}⟩))) (.node 52 (.leaf (⟨{0,2,3,6},{(0,2),(0,6),(2,3),(3,6)}⟩)) (.node 53 (.leaf (⟨{0,2,3,6},{(0,2),(0,3),(2,6),(3,6)}⟩)) (.leaf (⟨{0,2,4,5},{(0,2),(0,5),(2,4),(4,5)}⟩))))))) (.node 63 (.node 58 (.node 56 (.node 55 (.leaf (⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩)) (.leaf (⟨{0,2,4,6},{(0,2),(0,6),(2,4),(4,6)}⟩))) (.node 57 (.leaf (⟨{0,2,4,6},{(0,2),(0,4),(2,6),(4,6)}⟩)) (.leaf (⟨{0,2,5,6},{(0,2),(0,6),(2,5),(5,6)}⟩)))) (.node 60 (.node 59 (.leaf (⟨{0,2,5,6},{(0,2),(0,5),(2,6),(5,6)}⟩)) (.leaf (⟨{0,3,4,5},{(0,3),(0,5),(3,4),(4,5)}⟩))) (.node 61 (.leaf (⟨{0,3,4,5},{(0,3),(0,4),(3,5),(4,5)}⟩)) (.node 62 (.leaf (⟨{0,3,4,5},{(0,4),(0,5),(3,4),(3,5)}⟩)) (.leaf (⟨{0,3,4,6},{(0,3),(0,6),(3,4),(4,6)}⟩)))))) (.node 67 (.node 65 (.node 64 (.leaf (⟨{0,3,4,6},{(0,3),(0,4),(3,6),(4,6)}⟩)) (.leaf (⟨{0,3,4,6},{(0,4),(0,6),(3,4),(3,6)}⟩))) (.node 66 (.leaf (⟨{0,3,5,6},{(0,3),(0,6),(3,5),(5,6)}⟩)) (.leaf (⟨{0,3,5,6},{(0,3),(0,5),(3,6),(5,6)}⟩)))) (.node 69 (.node 68 (.leaf (⟨{0,3,5,6},{(0,5),(0,6),(3,5),(3,6)}⟩)) (.leaf (⟨{0,4,5,6},{(0,4),(0,6),(4,5),(5,6)}⟩))) (.node 70 (.leaf (⟨{0,4,5,6},{(0,4),(0,5),(4,6),(5,6)}⟩)) (.node 71 (.leaf (⟨{0,4,5,6},{(0,5),(0,6),(4,5),(4,6)}⟩)) (.leaf (⟨{1,2,3,4},{(1,2),(1,4),(2,3),(3,4)}⟩))))))))) (.node 108 (.node 90 (.node 81 (.node 76 (.node 74 (.node 73 (.leaf (⟨{1,2,3,4},{(1,2),(1,3),(2,4),(3,4)}⟩)) (.leaf (⟨{1,2,3,5},{(1,2),(1,5),(2,3),(3,5)}⟩))) (.node 75 (.leaf (⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩)) (.leaf (⟨{1,2,3,6},{(1,2),(1,6),(2,3),(3,6)}⟩)))) (.node 78 (.node 77 (.leaf (⟨{1,2,3,6},{(1,2),(1,3),(2,6),(3,6)}⟩)) (.leaf (⟨{1,2,4,5},{(1,2),(1,5),(2,4),(4,5)}⟩))) (.node 79 (.leaf (⟨{1,2,4,5},{(1,2),(1,4),(2,5),(4,5)}⟩)) (.node 80 (.leaf (⟨{1,2,4,6},{(1,2),(1,6),(2,4),(4,6)}⟩)) (.leaf (⟨{1,2,4,6},{(1,2),(1,4),(2,6),(4,6)}⟩)))))) (.node 85 (.node 83 (.node 82 (.leaf (⟨{1,2,5,6},{(1,2),(1,6),(2,5),(5,6)}⟩)) (.leaf (⟨{1,2,5,6},{(1,2),(1,5),(2,6),(5,6)}⟩))) (.node 84 (.leaf (⟨{1,3,4,5},{(1,3),(1,5),(3,4),(4,5)}⟩)) (.leaf (⟨{1,3,4,5},{(1,3),(1,4),(3,5),(4,5)}⟩)))) (.node 87 (.node 86 (.leaf (⟨{1,3,4,5},{(1,4),(1,5),(3,4),(3,5)}⟩)) (.leaf (⟨{1,3,4,6},{(1,3),(1,6),(3,4),(4,6)}⟩))) (.node 88 (.leaf (⟨{1,3,4,6},{(1,3),(1,4),(3,6),(4,6)}⟩)) (.node 89 (.leaf (⟨{1,3,4,6},{(1,4),(1,6),(3,4),(3,6)}⟩)) (.leaf (⟨{1,3,5,6},{(1,3),(1,6),(3,5),(5,6)}⟩))))))) (.node 99 (.node 94 (.node 92 (.node 91 (.leaf (⟨{1,3,5,6},{(1,3),(1,5),(3,6),(5,6)}⟩)) (.leaf (⟨{1,3,5,6},{(1,5),(1,6),(3,5),(3,6)}⟩))) (.node 93 (.leaf (⟨{1,4,5,6},{(1,4),(1,6),(4,5),(5,6)}⟩)) (.leaf (⟨{1,4,5,6},{(1,4),(1,5),(4,6),(5,6)}⟩)))) (.node 96 (.node 95 (.leaf (⟨{1,4,5,6},{(1,5),(1,6),(4,5),(4,6)}⟩)) (.leaf (⟨{2,3,4,5},{(2,3),(2,5),(3,4),(4,5)}⟩))) (.node 97 (.leaf (⟨{2,3,4,5},{(2,3),(2,4),(3,5),(4,5)}⟩)) (.node 98 (.leaf (⟨{2,3,4,5},{(2,4),(2,5),(3,4),(3,5)}⟩)) (.leaf (⟨{2,3,4,6},{(2,3),(2,6),(3,4),(4,6)}⟩)))))) (.node 103 (.node 101 (.node 100 (.leaf (⟨{2,3,4,6},{(2,3),(2,4),(3,6),(4,6)}⟩)) (.leaf (⟨{2,3,4,6},{(2,4),(2,6),(3,4),(3,6)}⟩))) (.node 102 (.leaf (⟨{2,3,5,6},{(2,3),(2,6),(3,5),(5,6)}⟩)) (.leaf (⟨{2,3,5,6},{(2,3),(2,5),(3,6),(5,6)}⟩)))) (.node 105 (.node 104 (.leaf (⟨{2,3,5,6},{(2,5),(2,6),(3,5),(3,6)}⟩)) (.leaf (⟨{2,4,5,6},{(2,4),(2,6),(4,5),(5,6)}⟩))) (.node 106 (.leaf (⟨{2,4,5,6},{(2,4),(2,5),(4,6),(5,6)}⟩)) (.node 107 (.leaf (⟨{2,4,5,6},{(2,5),(2,6),(4,5),(4,6)}⟩)) (.leaf (⟨{3,4,5,6},{(3,4),(3,6),(4,5),(5,6)}⟩)))))))) (.node 126 (.node 117 (.node 112 (.node 110 (.node 109 (.leaf (⟨{3,4,5,6},{(3,4),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{3,4,5,6},{(3,5),(3,6),(4,5),(4,6)}⟩))) (.node 111 (.leaf (⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩)) (.leaf (⟨{0,1,3,4,5},{(0,1),(0,4),(1,3),(3,5),(4,5)}⟩)))) (.node 114 (.node 113 (.leaf (⟨{0,1,3,4,5},{(0,1),(0,5),(1,4),(3,4),(3,5)}⟩)) (.leaf (⟨{0,1,3,4,5},{(0,1),(0,3),(1,4),(3,5),(4,5)}⟩))) (.node 115 (.leaf (⟨{0,1,3,4,5},{(0,1),(0,4),(1,5),(3,4),(3,5)}⟩)) (.node 116 (.leaf (⟨{0,1,3,4,5},{(0,1),(0,3),(1,5),(3,4),(4,5)}⟩)) (.leaf (⟨{0,1,3,4,6},{(0,1),(0,6),(1,3),(3,4),(4,6)}⟩)))))) (.node 121 (.node 119 (.node 118 (.leaf (⟨{0,1,3,4,6},{(0,1),(0,4),(1,3),(3,6),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,6},{(0,1),(0,6),(1,4),(3,4),(3,6)}⟩))) (.node 120 (.leaf (⟨{0,1,3,4,6},{(0,1),(0,3),(1,4),(3,6),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,6},{(0,1),(0,4),(1,6),(3,4),(3,6)}⟩)))) (.node 123 (.node 122 (.leaf (⟨{0,1,3,4,6},{(0,1),(0,3),(1,6),(3,4),(4,6)}⟩)) (.leaf (⟨{0,1,3,5,6},{(0,1),(0,6),(1,3),(3,5),(5,6)}⟩))) (.node 124 (.leaf (⟨{0,1,3,5,6},{(0,1),(0,5),(1,3),(3,6),(5,6)}⟩)) (.node 125 (.leaf (⟨{0,1,3,5,6},{(0,1),(0,6),(1,5),(3,5),(3,6)}⟩)) (.leaf (⟨{0,1,3,5,6},{(0,1),(0,3),(1,5),(3,6),(5,6)}⟩))))))) (.node 135 (.node 130 (.node 128 (.node 127 (.leaf (⟨{0,1,3,5,6},{(0,1),(0,5),(1,6),(3,5),(3,6)}⟩)) (.leaf (⟨{0,1,3,5,6},{(0,1),(0,3),(1,6),(3,5),(5,6)}⟩))) (.node 129 (.leaf (⟨{0,1,4,5,6},{(0,1),(0,6),(1,4),(4,5),(5,6)}⟩)) (.leaf (⟨{0,1,4,5,6},{(0,1),(0,5),(1,4),(4,6),(5,6)}⟩)))) (.node 132 (.node 131 (.leaf (⟨{0,1,4,5,6},{(0,1),(0,6),(1,5),(4,5),(4,6)}⟩)) (.leaf (⟨{0,1,4,5,6},{(0,1),(0,4),(1,5),(4,6),(5,6)}⟩))) (.node 133 (.leaf (⟨{0,1,4,5,6},{(0,1),(0,5),(1,6),(4,5),(4,6)}⟩)) (.node 134 (.leaf (⟨{0,1,4,5,6},{(0,1),(0,4),(1,6),(4,5),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5},{(0,2),(0,5),(2,3),(3,4),(4,5)}⟩)))))) (.node 140 (.node 137 (.node 136 (.leaf (⟨{0,2,3,4,5},{(0,2),(0,4),(2,3),(3,5),(4,5)}⟩)) (.leaf (⟨{0,2,3,4,5},{(0,2),(0,5),(2,4),(3,4),(3,5)}⟩))) (.node 138 (.leaf (⟨{0,2,3,4,5},{(0,2),(0,3),(2,4),(3,5),(4,5)}⟩)) (.node 139 (.leaf (⟨{0,2,3,4,5},{(0,2),(0,4),(2,5),(3,4),(3,5)}⟩)) (.leaf (⟨{0,2,3,4,5},{(0,2),(0,3),(2,5),(3,4),(4,5)}⟩))))) (.node 142 (.node 141 (.leaf (⟨{0,2,3,4,6},{(0,2),(0,6),(2,3),(3,4),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,6},{(0,2),(0,4),(2,3),(3,6),(4,6)}⟩))) (.node 143 (.leaf (⟨{0,2,3,4,6},{(0,2),(0,6),(2,4),(3,4),(3,6)}⟩)) (.node 144 (.leaf (⟨{0,2,3,4,6},{(0,2),(0,3),(2,4),(3,6),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,6},{(0,2),(0,4),(2,6),(3,4),(3,6)}⟩)))))))))) (.node 217 (.node 181 (.node 163 (.node 154 (.node 149 (.node 147 (.node 146 (.leaf (⟨{0,2,3,4,6},{(0,2),(0,3),(2,6),(3,4),(4,6)}⟩)) (.leaf (⟨{0,2,3,5,6},{(0,2),(0,6),(2,3),(3,5),(5,6)}⟩))) (.node 148 (.leaf (⟨{0,2,3,5,6},{(0,2),(0,5),(2,3),(3,6),(5,6)}⟩)) (.leaf (⟨{0,2,3,5,6},{(0,2),(0,6),(2,5),(3,5),(3,6)}⟩)))) (.node 151 (.node 150 (.leaf (⟨{0,2,3,5,6},{(0,2),(0,3),(2,5),(3,6),(5,6)}⟩)) (.leaf (⟨{0,2,3,5,6},{(0,2),(0,5),(2,6),(3,5),(3,6)}⟩))) (.node 152 (.leaf (⟨{0,2,3,5,6},{(0,2),(0,3),(2,6),(3,5),(5,6)}⟩)) (.node 153 (.leaf (⟨{0,2,4,5,6},{(0,2),(0,6),(2,4),(4,5),(5,6)}⟩)) (.leaf (⟨{0,2,4,5,6},{(0,2),(0,5),(2,4),(4,6),(5,6)}⟩)))))) (.node 158 (.node 156 (.node 155 (.leaf (⟨{0,2,4,5,6},{(0,2),(0,6),(2,5),(4,5),(4,6)}⟩)) (.leaf (⟨{0,2,4,5,6},{(0,2),(0,4),(2,5),(4,6),(5,6)}⟩))) (.node 157 (.leaf (⟨{0,2,4,5,6},{(0,2),(0,5),(2,6),(4,5),(4,6)}⟩)) (.leaf (⟨{0,2,4,5,6},{(0,2),(0,4),(2,6),(4,5),(5,6)}⟩)))) (.node 160 (.node 159 (.leaf (⟨{0,3,4,5,6},{(0,3),(0,6),(3,4),(4,5),(5,6)}⟩)) (.leaf (⟨{0,3,4,5,6},{(0,3),(0,5),(3,4),(4,6),(5,6)}⟩))) (.node 161 (.leaf (⟨{0,3,4,5,6},{(0,3),(0,6),(3,5),(4,5),(4,6)}⟩)) (.node 162 (.leaf (⟨{0,3,4,5,6},{(0,3),(0,4),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{0,3,4,5,6},{(0,3),(0,5),(3,6),(4,5),(4,6)}⟩))))))) (.node 172 (.node 167 (.node 165 (.node 164 (.leaf (⟨{0,3,4,5,6},{(0,3),(0,4),(3,6),(4,5),(5,6)}⟩)) (.leaf (⟨{0,3,4,5,6},{(0,4),(0,6),(3,4),(3,5),(5,6)}⟩))) (.node 166 (.leaf (⟨{0,3,4,5,6},{(0,4),(0,5),(3,4),(3,6),(5,6)}⟩)) (.leaf (⟨{0,3,4,5,6},{(0,4),(0,6),(3,5),(3,6),(4,5)}⟩)))) (.node 169 (.node 168 (.leaf (⟨{0,3,4,5,6},{(0,4),(0,5),(3,5),(3,6),(4,6)}⟩)) (.leaf (⟨{0,3,4,5,6},{(0,5),(0,6),(3,4),(3,5),(4,6)}⟩))) (.node 170 (.leaf (⟨{0,3,4,5,6},{(0,5),(0,6),(3,4),(3,6),(4,5)}⟩)) (.node 171 (.leaf (⟨{1,2,3,4,5},{(1,2),(1,5),(2,3),(3,4),(4,5)}⟩)) (.leaf (⟨{1,2,3,4,5},{(1,2),(1,4),(2,3),(3,5),(4,5)}⟩)))))) (.node 176 (.node 174 (.node 173 (.leaf (⟨{1,2,3,4,5},{(1,2),(1,5),(2,4),(3,4),(3,5)}⟩)) (.leaf (⟨{1,2,3,4,5},{(1,2),(1,3),(2,4),(3,5),(4,5)}⟩))) (.node 175 (.leaf (⟨{1,2,3,4,5},{(1,2),(1,4),(2,5),(3,4),(3,5)}⟩)) (.leaf (⟨{1,2,3,4,5},{(1,2),(1,3),(2,5),(3,4),(4,5)}⟩)))) (.node 178 (.node 177 (.leaf (⟨{1,2,3,4,6},{(1,2),(1,6),(2,3),(3,4),(4,6)}⟩)) (.leaf (⟨{1,2,3,4,6},{(1,2),(1,4),(2,3),(3,6),(4,6)}⟩))) (.node 179 (.leaf (⟨{1,2,3,4,6},{(1,2),(1,6),(2,4),(3,4),(3,6)}⟩)) (.node 180 (.leaf (⟨{1,2,3,4,6},{(1,2),(1,3),(2,4),(3,6),(4,6)}⟩)) (.leaf (⟨{1,2,3,4,6},{(1,2),(1,4),(2,6),(3,4),(3,6)}⟩)))))))) (.node 199 (.node 190 (.node 185 (.node 183 (.node 182 (.leaf (⟨{1,2,3,4,6},{(1,2),(1,3),(2,6),(3,4),(4,6)}⟩)) (.leaf (⟨{1,2,3,5,6},{(1,2),(1,6),(2,3),(3,5),(5,6)}⟩))) (.node 184 (.leaf (⟨{1,2,3,5,6},{(1,2),(1,5),(2,3),(3,6),(5,6)}⟩)) (.leaf (⟨{1,2,3,5,6},{(1,2),(1,6),(2,5),(3,5),(3,6)}⟩)))) (.node 187 (.node 186 (.leaf (⟨{1,2,3,5,6},{(1,2),(1,3),(2,5),(3,6),(5,6)}⟩)) (.leaf (⟨{1,2,3,5,6},{(1,2),(1,5),(2,6),(3,5),(3,6)}⟩))) (.node 188 (.leaf (⟨{1,2,3,5,6},{(1,2),(1,3),(2,6),(3,5),(5,6)}⟩)) (.node 189 (.leaf (⟨{1,2,4,5,6},{(1,2),(1,6),(2,4),(4,5),(5,6)}⟩)) (.leaf (⟨{1,2,4,5,6},{(1,2),(1,5),(2,4),(4,6),(5,6)}⟩)))))) (.node 194 (.node 192 (.node 191 (.leaf (⟨{1,2,4,5,6},{(1,2),(1,6),(2,5),(4,5),(4,6)}⟩)) (.leaf (⟨{1,2,4,5,6},{(1,2),(1,4),(2,5),(4,6),(5,6)}⟩))) (.node 193 (.leaf (⟨{1,2,4,5,6},{(1,2),(1,5),(2,6),(4,5),(4,6)}⟩)) (.leaf (⟨{1,2,4,5,6},{(1,2),(1,4),(2,6),(4,5),(5,6)}⟩)))) (.node 196 (.node 195 (.leaf (⟨{1,3,4,5,6},{(1,3),(1,6),(3,4),(4,5),(5,6)}⟩)) (.leaf (⟨{1,3,4,5,6},{(1,3),(1,5),(3,4),(4,6),(5,6)}⟩))) (.node 197 (.leaf (⟨{1,3,4,5,6},{(1,3),(1,6),(3,5),(4,5),(4,6)}⟩)) (.node 198 (.leaf (⟨{1,3,4,5,6},{(1,3),(1,4),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{1,3,4,5,6},{(1,3),(1,5),(3,6),(4,5),(4,6)}⟩))))))) (.node 208 (.node 203 (.node 201 (.node 200 (.leaf (⟨{1,3,4,5,6},{(1,3),(1,4),(3,6),(4,5),(5,6)}⟩)) (.leaf (⟨{1,3,4,5,6},{(1,4),(1,6),(3,4),(3,5),(5,6)}⟩))) (.node 202 (.leaf (⟨{1,3,4,5,6},{(1,4),(1,5),(3,4),(3,6),(5,6)}⟩)) (.leaf (⟨{1,3,4,5,6},{(1,4),(1,6),(3,5),(3,6),(4,5)}⟩)))) (.node 205 (.node 204 (.leaf (⟨{1,3,4,5,6},{(1,4),(1,5),(3,5),(3,6),(4,6)}⟩)) (.leaf (⟨{1,3,4,5,6},{(1,5),(1,6),(3,4),(3,5),(4,6)}⟩))) (.node 206 (.leaf (⟨{1,3,4,5,6},{(1,5),(1,6),(3,4),(3,6),(4,5)}⟩)) (.node 207 (.leaf (⟨{2,3,4,5,6},{(2,3),(2,6),(3,4),(4,5),(5,6)}⟩)) (.leaf (⟨{2,3,4,5,6},{(2,3),(2,5),(3,4),(4,6),(5,6)}⟩)))))) (.node 212 (.node 210 (.node 209 (.leaf (⟨{2,3,4,5,6},{(2,3),(2,6),(3,5),(4,5),(4,6)}⟩)) (.leaf (⟨{2,3,4,5,6},{(2,3),(2,4),(3,5),(4,6),(5,6)}⟩))) (.node 211 (.leaf (⟨{2,3,4,5,6},{(2,3),(2,5),(3,6),(4,5),(4,6)}⟩)) (.leaf (⟨{2,3,4,5,6},{(2,3),(2,4),(3,6),(4,5),(5,6)}⟩)))) (.node 214 (.node 213 (.leaf (⟨{2,3,4,5,6},{(2,4),(2,6),(3,4),(3,5),(5,6)}⟩)) (.leaf (⟨{2,3,4,5,6},{(2,4),(2,5),(3,4),(3,6),(5,6)}⟩))) (.node 215 (.leaf (⟨{2,3,4,5,6},{(2,4),(2,6),(3,5),(3,6),(4,5)}⟩)) (.node 216 (.leaf (⟨{2,3,4,5,6},{(2,4),(2,5),(3,5),(3,6),(4,6)}⟩)) (.leaf (⟨{2,3,4,5,6},{(2,5),(2,6),(3,4),(3,5),(4,6)}⟩))))))))) (.node 253 (.node 235 (.node 226 (.node 221 (.node 219 (.node 218 (.leaf (⟨{2,3,4,5,6},{(2,5),(2,6),(3,4),(3,6),(4,5)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,3),(3,4),(4,5),(5,6)}⟩))) (.node 220 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,3),(3,4),(4,6),(5,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,3),(3,5),(4,5),(4,6)}⟩)))) (.node 223 (.node 222 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,3),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,3),(3,6),(4,5),(4,6)}⟩))) (.node 224 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,3),(3,6),(4,5),(5,6)}⟩)) (.node 225 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,4),(3,4),(3,5),(5,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,4),(3,4),(3,6),(5,6)}⟩)))))) (.node 230 (.node 228 (.node 227 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,4),(3,5),(3,6),(4,5)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,4),(3,6),(4,5),(5,6)}⟩))) (.node 229 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,4),(3,5),(3,6),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,4),(3,5),(4,6),(5,6)}⟩)))) (.node 232 (.node 231 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,5),(3,4),(3,5),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,5),(3,5),(3,6),(4,6)}⟩))) (.node 233 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,5),(3,4),(3,6),(4,5)}⟩)) (.node 234 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,5),(3,6),(4,5),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,5),(3,4),(3,6),(5,6)}⟩))))))) (.node 244 (.node 239 (.node 237 (.node 236 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,5),(3,4),(4,6),(5,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,6),(3,4),(3,6),(4,5)}⟩))) (.node 238 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,6),(3,5),(3,6),(4,5)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,5),(1,6),(3,4),(3,5),(4,6)}⟩)))) (.node 241 (.node 240 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,6),(3,5),(4,5),(4,6)}⟩)) (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,4),(1,6),(3,4),(3,5),(5,6)}⟩))) (.node 242 (.leaf (⟨{0,1,3,4,5,6},{(0,1),(0,3),(1,6),(3,4),(4,5),(5,6)}⟩)) (.node 243 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,3),(3,4),(4,5),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,3),(3,4),(4,6),(5,6)}⟩)))))) (.node 248 (.node 246 (.node 245 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,3),(3,5),(4,5),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,3),(3,5),(4,6),(5,6)}⟩))) (.node 247 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,3),(3,6),(4,5),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,3),(3,6),(4,5),(5,6)}⟩)))) (.node 250 (.node 249 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,4),(3,4),(3,5),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,4),(3,4),(3,6),(5,6)}⟩))) (.node 251 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,4),(3,5),(3,6),(4,5)}⟩)) (.node 252 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,4),(3,6),(4,5),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,4),(3,5),(3,6),(4,6)}⟩)))))))) (.node 271 (.node 262 (.node 257 (.node 255 (.node 254 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,4),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,5),(3,4),(3,5),(4,6)}⟩))) (.node 256 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,5),(3,5),(3,6),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,6),(2,5),(3,4),(3,6),(4,5)}⟩)))) (.node 259 (.node 258 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,5),(3,6),(4,5),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,5),(3,4),(3,6),(5,6)}⟩))) (.node 260 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,5),(3,4),(4,6),(5,6)}⟩)) (.node 261 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,6),(3,4),(3,6),(4,5)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,6),(3,5),(3,6),(4,5)}⟩)))))) (.node 266 (.node 264 (.node 263 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,5),(2,6),(3,4),(3,5),(4,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,6),(3,5),(4,5),(4,6)}⟩))) (.node 265 (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,4),(2,6),(3,4),(3,5),(5,6)}⟩)) (.leaf (⟨{0,2,3,4,5,6},{(0,2),(0,3),(2,6),(3,4),(4,5),(5,6)}⟩)))) (.node 268 (.node 267 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,3),(3,4),(4,5),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,3),(3,4),(4,6),(5,6)}⟩))) (.node 269 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,3),(3,5),(4,5),(4,6)}⟩)) (.node 270 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,3),(3,5),(4,6),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,3),(3,6),(4,5),(4,6)}⟩))))))) (.node 280 (.node 275 (.node 273 (.node 272 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,3),(3,6),(4,5),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,4),(3,4),(3,5),(5,6)}⟩))) (.node 274 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,4),(3,4),(3,6),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,4),(3,5),(3,6),(4,5)}⟩)))) (.node 277 (.node 276 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,4),(3,6),(4,5),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,4),(3,5),(3,6),(4,6)}⟩))) (.node 278 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,4),(3,5),(4,6),(5,6)}⟩)) (.node 279 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,5),(3,4),(3,5),(4,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,5),(3,5),(3,6),(4,6)}⟩)))))) (.node 285 (.node 282 (.node 281 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,6),(2,5),(3,4),(3,6),(4,5)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,5),(3,6),(4,5),(4,6)}⟩))) (.node 283 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,5),(3,4),(3,6),(5,6)}⟩)) (.node 284 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,5),(3,4),(4,6),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,6),(3,4),(3,6),(4,5)}⟩))))) (.node 287 (.node 286 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,6),(3,5),(3,6),(4,5)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,5),(2,6),(3,4),(3,5),(4,6)}⟩))) (.node 288 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,6),(3,5),(4,5),(4,6)}⟩)) (.node 289 (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,4),(2,6),(3,4),(3,5),(5,6)}⟩)) (.leaf (⟨{1,2,3,4,5,6},{(1,2),(1,3),(2,6),(3,4),(4,5),(5,6)}⟩)))))))))))
noncomputable def cells (i : Fin 290) : Polygon 7 := cellTable.get i.val

noncomputable def neighbors : Finset (Fin 290) := {1,35,110,218}
noncomputable def permMaps : Fin 24 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],
  ![0,1,2,3,4,6,5],
  ![0,1,2,3,5,4,6],
  ![0,1,2,3,5,6,4],
  ![0,1,2,3,6,4,5],
  ![0,1,2,3,6,5,4],
  ![0,1,2,4,3,5,6],
  ![0,1,2,4,3,6,5],
  ![0,1,2,4,5,3,6],
  ![0,1,2,4,5,6,3],
  ![0,1,2,4,6,3,5],
  ![0,1,2,4,6,5,3],
  ![0,1,2,5,3,4,6],
  ![0,1,2,5,3,6,4],
  ![0,1,2,5,4,3,6],
  ![0,1,2,5,4,6,3],
  ![0,1,2,5,6,3,4],
  ![0,1,2,5,6,4,3],
  ![0,1,2,6,3,4,5],
  ![0,1,2,6,3,5,4],
  ![0,1,2,6,4,3,5],
  ![0,1,2,6,4,5,3],
  ![0,1,2,6,5,3,4],
  ![0,1,2,6,5,4,3]]

/-- A small numeric observation of a polygon. No global injectivity is assumed. -/
noncomputable def edgeFingerprint (p : Polygon 7) : Nat :=
  p.edges.sum fun e => (2 : Nat) ^ (7 * e.1.val + e.2.val)

/-- The producer supplies an inverse candidate; every returned index is checked below. -/
noncomputable def edgeInverseTable : LiteralLookup Nat := (.node 17314220544 (.node 8590201344 (.node 100930048 (.node 33688064 (.node 524324 (.node 8258 (.node 2066 (.node 1034 (.leaf 0) (.leaf 1)) (.node 4130 (.leaf 2) (.leaf 3))) (.node 132608 (.node 131084 (.leaf 4) (.leaf 5)) (.node 262164 (.leaf 15) (.node 264704 (.leaf 6) (.leaf 16))))) (.node 33554456 (.node 1048644 (.node 528896 (.leaf 7) (.leaf 17)) (.node 1057280 (.leaf 8) (.leaf 18))) (.node 33556490 (.node 33555474 (.leaf 9) (.leaf 35)) (.node 33557504 (.leaf 36) (.node 33685524 (.leaf 19) (.leaf 47)))))) (.node 67244544 (.node 67108904 (.node 33818112 (.node 33816588 (.leaf 71) (.leaf 48)) (.node 33947648 (.leaf 72) (.leaf 25))) (.node 67112970 (.node 67109922 (.leaf 10) (.leaf 37)) (.node 67113984 (.leaf 38) (.node 67239972 (.leaf 20) (.leaf 49))))) (.node 100663344 (.node 67634688 (.node 67633164 (.leaf 73) (.leaf 50)) (.node 67764224 (.leaf 74) (.leaf 26))) (.node 100667410 (.node 100665378 (.leaf 61) (.leaf 112)) (.node 100669440 (.leaf 114) (.node 100925476 (.leaf 85) (.leaf 136))))))) (.node 168043008 (.node 134357504 (.node 134217800 (.node 101190144 (.node 101187604 (.leaf 172) (.leaf 138)) (.node 101449728 (.leaf 174) (.leaf 97))) (.node 134225930 (.node 134218818 (.leaf 11) (.leaf 39)) (.node 134226944 (.leaf 40) (.node 134348868 (.leaf 21) (.leaf 51))))) (.node 167772240 (.node 135267840 (.node 135266316 (.leaf 75) (.leaf 52)) (.node 135397376 (.leaf 76) (.leaf 27))) (.node 167780370 (.node 167774274 (.leaf 64) (.leaf 118)) (.node 167782400 (.leaf 120) (.node 168034372 (.leaf 88) (.leaf 142)))))) (.node 201859584 (.node 201326688 (.node 168823296 (.node 168820756 (.leaf 178) (.leaf 144)) (.node 169082880 (.leaf 180) (.leaf 100))) (.node 201334818 (.node 201330754 (.leaf 67) (.leaf 124)) (.node 201338880 (.leaf 126) (.node 201850948 (.leaf 91) (.leaf 148))))) (.node 8589934640 (.node 202379776 (.node 202375204 (.leaf 184) (.leaf 150)) (.node 202899456 (.leaf 186) (.leaf 103))) (.node 8589938706 (.node 8589936674 (.leaf 12) (.leaf 41)) (.node 8589940736 (.leaf 42) (.node 8590196772 (.leaf 22) (.leaf 53)))))))) (.node 8791523396 (.node 8657177088 (.node 8623624704 (.node 8623489064 (.node 8590461440 (.node 8590458900 (.leaf 77) (.leaf 54)) (.node 8590721024 (.leaf 78) (.leaf 28))) (.node 8623493130 (.node 8623490082 (.leaf 59) (.leaf 110)) (.node 8623494144 (.leaf 115) (.node 8623620132 (.leaf 83) (.leaf 134))))) (.node 8657043480 (.node 8624014848 (.node 8624013324 (.leaf 170) (.leaf 139)) (.node 8624144384 (.leaf 175) (.leaf 95))) (.node 8657045514 (.node 8657044498 (.leaf 60) (.leaf 111)) (.node 8657046528 (.leaf 113) (.node 8657174548 (.leaf 84) (.leaf 135)))))) (.node 8758231108 (.node 8690597888 (.node 8657307136 (.node 8657305612 (.leaf 171) (.leaf 137)) (.node 8657436672 (.leaf 173) (.leaf 96))) (.node 8757710914 (.node 8757706848 (.leaf 31) (.leaf 169)) (.node 8757714978 (.leaf 232) (.node 8757719040 (.leaf 236) (.leaf 205))))) (.node 8759279616 (.node 8758755364 (.node 8758239744 (.leaf 256) (.leaf 280)) (.node 8758759936 (.leaf 260) (.leaf 284))) (.node 8791263298 (.node 8791261264 (.leaf 217) (.leaf 166)) (.node 8791269394 (.leaf 226) (.node 8791271424 (.leaf 237) (.leaf 202))))))) (.node 17213554756 (.node 17180131396 (.node 8792571904 (.node 8792309780 (.node 8791532032 (.leaf 250) (.leaf 274)) (.node 8792312320 (.leaf 261) (.leaf 285))) (.node 17179871298 (.node 17179869264 (.leaf 214) (.leaf 13)) (.node 17179877394 (.leaf 43) (.node 17179879424 (.leaf 44) (.leaf 23))))) (.node 17181179904 (.node 17180917780 (.node 17180140032 (.leaf 55) (.leaf 79)) (.node 17180920320 (.leaf 56) (.leaf 80))) (.node 17213424706 (.node 17213423688 (.leaf 29) (.leaf 62)) (.node 17213431818 (.leaf 116) (.node 17213432832 (.leaf 121) (.leaf 86)))))) (.node 17281056836 (.node 17214603264 (.node 17214472204 (.node 17213563392 (.leaf 140) (.leaf 176)) (.node 17214473728 (.leaf 145) (.leaf 181))) (.node 17280536642 (.node 17280532576 (.leaf 98) (.leaf 168)) (.node 17280540706 (.leaf 230) (.node 17280544768 (.leaf 238) (.leaf 204))))) (.node 17314086936 (.node 17281581092 (.node 17281065472 (.leaf 254) (.leaf 278)) (.node 17281585664 (.leaf 262) (.node 17282105344 (.leaf 286) (.leaf 216)))) (.node 17314088970 (.node 17314087954 (.leaf 63) (.leaf 117)) (.node 17314089984 (.leaf 119) (.node 17314218004 (.leaf 87) (.leaf 141))))))))) (.node 2199157478400 (.node 25904152612 (.node 25770328132 (.node 17381457956 (.node 17347641344 (.node 17314350592 (.node 17314349068 (.leaf 177) (.leaf 143)) (.node 17314480128 (.leaf 179) (.leaf 99))) (.node 17381197858 (.node 17381195824 (.leaf 32) (.leaf 167)) (.node 17381199890 (.leaf 228) (.node 17381201920 (.leaf 231) (.leaf 203))))) (.node 17381982208 (.node 17381720084 (.node 17381462528 (.leaf 252) (.leaf 276)) (.node 17381722624 (.leaf 255) (.leaf 279))) (.node 25769807938 (.node 25769803872 (.leaf 215) (.leaf 70)) (.node 25769812002 (.leaf 130) (.node 25769816064 (.leaf 132) (.leaf 94)))))) (.node 25837043780 (.node 25771376640 (.node 25770852388 (.node 25770336768 (.leaf 154) (.leaf 190)) (.node 25770856960 (.leaf 156) (.leaf 192))) (.node 25836913730 (.node 25836912712 (.leaf 106) (.leaf 160)) (.node 25836920842 (.leaf 220) (.node 25836921856 (.leaf 239) (.leaf 196))))) (.node 25838092288 (.node 25837961228 (.node 25837052416 (.leaf 244) (.leaf 268)) (.node 25837962752 (.leaf 263) (.leaf 287))) (.node 25904022562 (.node 25904021544 (.leaf 208) (.leaf 162)) (.node 25904025610 (.leaf 222) (.node 25904026624 (.leaf 233) (.leaf 198))))))) (.node 2199090373632 (.node 2199023267840 (.node 25904676864 (.node 25904545804 (.node 25904157184 (.leaf 246) (.leaf 270)) (.node 25904547328 (.leaf 257) (.leaf 281))) (.node 2199023255648 (.node 25971130368 (.leaf 210) (.leaf 109)) (.node 2199023259714 (.leaf 14) (.node 2199023263778 (.leaf 45) (.leaf 46))))) (.node 2199024308736 (.node 2199023788544 (.node 2199023779908 (.leaf 24) (.leaf 57)) (.node 2199024304164 (.leaf 81) (.leaf 58))) (.node 2199090364488 (.node 2199024828416 (.leaf 82) (.leaf 30)) (.node 2199090365506 (.leaf 65) (.node 2199090372618 (.leaf 122) (.leaf 127)))))) (.node 2199123929088 (.node 2199091414528 (.node 2199090504192 (.node 2199090495556 (.leaf 89) (.leaf 146)) (.node 2199091413004 (.leaf 182) (.leaf 151))) (.node 2199123918928 (.node 2199091544064 (.leaf 187) (.leaf 101)) (.node 2199123920962 (.leaf 164) (.node 2199123927058 (.leaf 224) (.leaf 240))))) (.node 2199124969984 (.node 2199124189696 (.node 2199124181060 (.leaf 200) (.leaf 248)) (.node 2199124967444 (.leaf 272) (.leaf 264))) (.node 2199157473320 (.node 2199125229568 (.leaf 288) (.leaf 212)) (.node 2199157474338 (.leaf 66) (.node 2199157477386 (.leaf 123) (.leaf 125)))))))) (.node 2207747409930 (.node 2207613198354 (.node 2199191033856 (.node 2199157999104 (.node 2199157608960 (.node 2199157604388 (.leaf 90) (.leaf 147)) (.node 2199157997580 (.leaf 183) (.leaf 149))) (.node 2199191027760 (.node 2199158128640 (.leaf 185) (.leaf 102)) (.node 2199191029794 (.leaf 165) (.node 2199191031826 (.leaf 225) (.leaf 234))))) (.node 2199191554560 (.node 2199191294464 (.node 2199191289892 (.leaf 201) (.leaf 249)) (.node 2199191552020 (.leaf 273) (.leaf 258))) (.node 2199224582144 (.node 2199191814144 (.leaf 282) (.leaf 213)) (.node 2207613190224 (.leaf 33) (.node 2207613192258 (.leaf 68) (.leaf 128)))))) (.node 2207646752778 (.node 2207614238740 (.node 2207613452356 (.node 2207613200384 (.leaf 133) (.leaf 92)) (.node 2207613460992 (.leaf 152) (.leaf 188))) (.node 2207614500864 (.node 2207614241280 (.leaf 157) (.leaf 193)) (.node 2207646744648 (.leaf 104) (.node 2207646745666 (.leaf 158) (.leaf 218))))) (.node 2207647793164 (.node 2207646875716 (.node 2207646753792 (.leaf 241) (.leaf 194)) (.node 2207646884352 (.leaf 242) (.leaf 266))) (.node 2207647924224 (.node 2207647794688 (.leaf 265) (.leaf 289)) (.node 2207747407896 (.leaf 206) (.node 2207747408914 (.leaf 163) (.leaf 223))))))) (.node 2216236680226 (.node 2216203126818 (.node 2207747670028 (.node 2207747538964 (.node 2207747410944 (.leaf 227) (.leaf 199)) (.node 2207747541504 (.leaf 247) (.leaf 271))) (.node 2207747801088 (.node 2207747671552 (.leaf 251) (.leaf 275)) (.node 2207780962304 (.leaf 211) (.node 2216203124784 (.leaf 107) (.leaf 69))))) (.node 2216203391488 (.node 2216203130880 (.node 2216203128850 (.leaf 129) (.leaf 131)) (.node 2216203386916 (.leaf 93) (.leaf 153))) (.node 2216203651584 (.node 2216203649044 (.leaf 189) (.leaf 155)) (.node 2216203911168 (.leaf 191) (.node 2216236679208 (.leaf 105) (.leaf 159)))))) (.node 2216270234642 (.node 2216236814848 (.node 2216236684288 (.node 2216236683274 (.leaf 219) (.leaf 235)) (.node 2216236810276 (.leaf 195) (.leaf 243))) (.node 2216237204992 (.node 2216237203468 (.leaf 267) (.leaf 259)) (.node 2216237334528 (.leaf 283) (.node 2216270233624 (.leaf 207) (.leaf 161))))) (.node 2216270495756 (.node 2216270236672 (.node 2216270235658 (.leaf 221) (.leaf 229)) (.node 2216270364692 (.leaf 197) (.node 2216270367232 (.leaf 245) (.leaf 269)))) (.node 2216270626816 (.node 2216270497280 (.leaf 253) (.leaf 277)) (.node 2216303788032 (.leaf 209) (.node 2224793059328 (.leaf 108) (.leaf 34))))))))))

noncomputable def edgeInverse (p : Polygon 7) : Nat :=
  edgeInverseTable.get (edgeFingerprint p)

noncomputable def injectivityTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 290 index
  decide (edgeInverse (cells a) = a.val)

theorem injective_rows_000 : FiniteChecks.Interval injectivityTest 0 4 :=
  FiniteChecks.interval_of_check injectivityTest 0 4 (by decide +kernel)

theorem injective_rows_004 : FiniteChecks.Interval injectivityTest 4 8 :=
  FiniteChecks.interval_of_check injectivityTest 4 4 (by decide +kernel)

theorem injective_rows_008 : FiniteChecks.Interval injectivityTest 8 12 :=
  FiniteChecks.interval_of_check injectivityTest 8 4 (by decide +kernel)

theorem injective_rows_012 : FiniteChecks.Interval injectivityTest 12 16 :=
  FiniteChecks.interval_of_check injectivityTest 12 4 (by decide +kernel)

theorem injective_rows_016 : FiniteChecks.Interval injectivityTest 16 20 :=
  FiniteChecks.interval_of_check injectivityTest 16 4 (by decide +kernel)

theorem injective_rows_020 : FiniteChecks.Interval injectivityTest 20 24 :=
  FiniteChecks.interval_of_check injectivityTest 20 4 (by decide +kernel)

theorem injective_rows_024 : FiniteChecks.Interval injectivityTest 24 28 :=
  FiniteChecks.interval_of_check injectivityTest 24 4 (by decide +kernel)

theorem injective_rows_028 : FiniteChecks.Interval injectivityTest 28 32 :=
  FiniteChecks.interval_of_check injectivityTest 28 4 (by decide +kernel)

theorem injective_rows_032 : FiniteChecks.Interval injectivityTest 32 36 :=
  FiniteChecks.interval_of_check injectivityTest 32 4 (by decide +kernel)

theorem injective_rows_036 : FiniteChecks.Interval injectivityTest 36 40 :=
  FiniteChecks.interval_of_check injectivityTest 36 4 (by decide +kernel)

theorem injective_rows_040 : FiniteChecks.Interval injectivityTest 40 44 :=
  FiniteChecks.interval_of_check injectivityTest 40 4 (by decide +kernel)

theorem injective_rows_044 : FiniteChecks.Interval injectivityTest 44 48 :=
  FiniteChecks.interval_of_check injectivityTest 44 4 (by decide +kernel)

theorem injective_rows_048 : FiniteChecks.Interval injectivityTest 48 52 :=
  FiniteChecks.interval_of_check injectivityTest 48 4 (by decide +kernel)

theorem injective_rows_052 : FiniteChecks.Interval injectivityTest 52 56 :=
  FiniteChecks.interval_of_check injectivityTest 52 4 (by decide +kernel)

theorem injective_rows_056 : FiniteChecks.Interval injectivityTest 56 60 :=
  FiniteChecks.interval_of_check injectivityTest 56 4 (by decide +kernel)

theorem injective_rows_060 : FiniteChecks.Interval injectivityTest 60 64 :=
  FiniteChecks.interval_of_check injectivityTest 60 4 (by decide +kernel)

theorem injective_rows_064 : FiniteChecks.Interval injectivityTest 64 68 :=
  FiniteChecks.interval_of_check injectivityTest 64 4 (by decide +kernel)

theorem injective_rows_068 : FiniteChecks.Interval injectivityTest 68 72 :=
  FiniteChecks.interval_of_check injectivityTest 68 4 (by decide +kernel)

theorem injective_rows_072 : FiniteChecks.Interval injectivityTest 72 76 :=
  FiniteChecks.interval_of_check injectivityTest 72 4 (by decide +kernel)

theorem injective_rows_076 : FiniteChecks.Interval injectivityTest 76 80 :=
  FiniteChecks.interval_of_check injectivityTest 76 4 (by decide +kernel)

theorem injective_rows_080 : FiniteChecks.Interval injectivityTest 80 84 :=
  FiniteChecks.interval_of_check injectivityTest 80 4 (by decide +kernel)

theorem injective_rows_084 : FiniteChecks.Interval injectivityTest 84 88 :=
  FiniteChecks.interval_of_check injectivityTest 84 4 (by decide +kernel)

theorem injective_rows_088 : FiniteChecks.Interval injectivityTest 88 92 :=
  FiniteChecks.interval_of_check injectivityTest 88 4 (by decide +kernel)

theorem injective_rows_092 : FiniteChecks.Interval injectivityTest 92 96 :=
  FiniteChecks.interval_of_check injectivityTest 92 4 (by decide +kernel)

theorem injective_rows_096 : FiniteChecks.Interval injectivityTest 96 100 :=
  FiniteChecks.interval_of_check injectivityTest 96 4 (by decide +kernel)

theorem injective_rows_100 : FiniteChecks.Interval injectivityTest 100 104 :=
  FiniteChecks.interval_of_check injectivityTest 100 4 (by decide +kernel)

theorem injective_rows_104 : FiniteChecks.Interval injectivityTest 104 108 :=
  FiniteChecks.interval_of_check injectivityTest 104 4 (by decide +kernel)

theorem injective_rows_108 : FiniteChecks.Interval injectivityTest 108 112 :=
  FiniteChecks.interval_of_check injectivityTest 108 4 (by decide +kernel)

theorem injective_rows_112 : FiniteChecks.Interval injectivityTest 112 116 :=
  FiniteChecks.interval_of_check injectivityTest 112 4 (by decide +kernel)

theorem injective_rows_116 : FiniteChecks.Interval injectivityTest 116 120 :=
  FiniteChecks.interval_of_check injectivityTest 116 4 (by decide +kernel)

theorem injective_rows_120 : FiniteChecks.Interval injectivityTest 120 124 :=
  FiniteChecks.interval_of_check injectivityTest 120 4 (by decide +kernel)

theorem injective_rows_124 : FiniteChecks.Interval injectivityTest 124 128 :=
  FiniteChecks.interval_of_check injectivityTest 124 4 (by decide +kernel)

theorem injective_rows_128 : FiniteChecks.Interval injectivityTest 128 132 :=
  FiniteChecks.interval_of_check injectivityTest 128 4 (by decide +kernel)

theorem injective_rows_132 : FiniteChecks.Interval injectivityTest 132 136 :=
  FiniteChecks.interval_of_check injectivityTest 132 4 (by decide +kernel)

theorem injective_rows_136 : FiniteChecks.Interval injectivityTest 136 140 :=
  FiniteChecks.interval_of_check injectivityTest 136 4 (by decide +kernel)

theorem injective_rows_140 : FiniteChecks.Interval injectivityTest 140 144 :=
  FiniteChecks.interval_of_check injectivityTest 140 4 (by decide +kernel)

theorem injective_rows_144 : FiniteChecks.Interval injectivityTest 144 148 :=
  FiniteChecks.interval_of_check injectivityTest 144 4 (by decide +kernel)

theorem injective_rows_148 : FiniteChecks.Interval injectivityTest 148 152 :=
  FiniteChecks.interval_of_check injectivityTest 148 4 (by decide +kernel)

theorem injective_rows_152 : FiniteChecks.Interval injectivityTest 152 156 :=
  FiniteChecks.interval_of_check injectivityTest 152 4 (by decide +kernel)

theorem injective_rows_156 : FiniteChecks.Interval injectivityTest 156 160 :=
  FiniteChecks.interval_of_check injectivityTest 156 4 (by decide +kernel)

theorem injective_rows_160 : FiniteChecks.Interval injectivityTest 160 164 :=
  FiniteChecks.interval_of_check injectivityTest 160 4 (by decide +kernel)

theorem injective_rows_164 : FiniteChecks.Interval injectivityTest 164 168 :=
  FiniteChecks.interval_of_check injectivityTest 164 4 (by decide +kernel)

theorem injective_rows_168 : FiniteChecks.Interval injectivityTest 168 172 :=
  FiniteChecks.interval_of_check injectivityTest 168 4 (by decide +kernel)

theorem injective_rows_172 : FiniteChecks.Interval injectivityTest 172 176 :=
  FiniteChecks.interval_of_check injectivityTest 172 4 (by decide +kernel)

theorem injective_rows_176 : FiniteChecks.Interval injectivityTest 176 180 :=
  FiniteChecks.interval_of_check injectivityTest 176 4 (by decide +kernel)

theorem injective_rows_180 : FiniteChecks.Interval injectivityTest 180 184 :=
  FiniteChecks.interval_of_check injectivityTest 180 4 (by decide +kernel)

theorem injective_rows_184 : FiniteChecks.Interval injectivityTest 184 188 :=
  FiniteChecks.interval_of_check injectivityTest 184 4 (by decide +kernel)

theorem injective_rows_188 : FiniteChecks.Interval injectivityTest 188 192 :=
  FiniteChecks.interval_of_check injectivityTest 188 4 (by decide +kernel)

theorem injective_rows_192 : FiniteChecks.Interval injectivityTest 192 196 :=
  FiniteChecks.interval_of_check injectivityTest 192 4 (by decide +kernel)

theorem injective_rows_196 : FiniteChecks.Interval injectivityTest 196 200 :=
  FiniteChecks.interval_of_check injectivityTest 196 4 (by decide +kernel)

theorem injective_rows_200 : FiniteChecks.Interval injectivityTest 200 204 :=
  FiniteChecks.interval_of_check injectivityTest 200 4 (by decide +kernel)

theorem injective_rows_204 : FiniteChecks.Interval injectivityTest 204 208 :=
  FiniteChecks.interval_of_check injectivityTest 204 4 (by decide +kernel)

theorem injective_rows_208 : FiniteChecks.Interval injectivityTest 208 212 :=
  FiniteChecks.interval_of_check injectivityTest 208 4 (by decide +kernel)

theorem injective_rows_212 : FiniteChecks.Interval injectivityTest 212 216 :=
  FiniteChecks.interval_of_check injectivityTest 212 4 (by decide +kernel)

theorem injective_rows_216 : FiniteChecks.Interval injectivityTest 216 220 :=
  FiniteChecks.interval_of_check injectivityTest 216 4 (by decide +kernel)

theorem injective_rows_220 : FiniteChecks.Interval injectivityTest 220 224 :=
  FiniteChecks.interval_of_check injectivityTest 220 4 (by decide +kernel)

theorem injective_rows_224 : FiniteChecks.Interval injectivityTest 224 228 :=
  FiniteChecks.interval_of_check injectivityTest 224 4 (by decide +kernel)

theorem injective_rows_228 : FiniteChecks.Interval injectivityTest 228 232 :=
  FiniteChecks.interval_of_check injectivityTest 228 4 (by decide +kernel)

theorem injective_rows_232 : FiniteChecks.Interval injectivityTest 232 236 :=
  FiniteChecks.interval_of_check injectivityTest 232 4 (by decide +kernel)

theorem injective_rows_236 : FiniteChecks.Interval injectivityTest 236 240 :=
  FiniteChecks.interval_of_check injectivityTest 236 4 (by decide +kernel)

theorem injective_rows_240 : FiniteChecks.Interval injectivityTest 240 244 :=
  FiniteChecks.interval_of_check injectivityTest 240 4 (by decide +kernel)

theorem injective_rows_244 : FiniteChecks.Interval injectivityTest 244 248 :=
  FiniteChecks.interval_of_check injectivityTest 244 4 (by decide +kernel)

theorem injective_rows_248 : FiniteChecks.Interval injectivityTest 248 252 :=
  FiniteChecks.interval_of_check injectivityTest 248 4 (by decide +kernel)

theorem injective_rows_252 : FiniteChecks.Interval injectivityTest 252 256 :=
  FiniteChecks.interval_of_check injectivityTest 252 4 (by decide +kernel)

theorem injective_rows_256 : FiniteChecks.Interval injectivityTest 256 260 :=
  FiniteChecks.interval_of_check injectivityTest 256 4 (by decide +kernel)

theorem injective_rows_260 : FiniteChecks.Interval injectivityTest 260 264 :=
  FiniteChecks.interval_of_check injectivityTest 260 4 (by decide +kernel)

theorem injective_rows_264 : FiniteChecks.Interval injectivityTest 264 268 :=
  FiniteChecks.interval_of_check injectivityTest 264 4 (by decide +kernel)

theorem injective_rows_268 : FiniteChecks.Interval injectivityTest 268 272 :=
  FiniteChecks.interval_of_check injectivityTest 268 4 (by decide +kernel)

theorem injective_rows_272 : FiniteChecks.Interval injectivityTest 272 276 :=
  FiniteChecks.interval_of_check injectivityTest 272 4 (by decide +kernel)

theorem injective_rows_276 : FiniteChecks.Interval injectivityTest 276 280 :=
  FiniteChecks.interval_of_check injectivityTest 276 4 (by decide +kernel)

theorem injective_rows_280 : FiniteChecks.Interval injectivityTest 280 284 :=
  FiniteChecks.interval_of_check injectivityTest 280 4 (by decide +kernel)

theorem injective_rows_284 : FiniteChecks.Interval injectivityTest 284 288 :=
  FiniteChecks.interval_of_check injectivityTest 284 4 (by decide +kernel)

theorem injective_rows_288 : FiniteChecks.Interval injectivityTest 288 290 :=
  FiniteChecks.interval_of_check injectivityTest 288 2 (by decide +kernel)

theorem injective_join_0_8 : FiniteChecks.Interval injectivityTest 0 8 :=
  FiniteChecks.interval_append injectivityTest 0 4 8 injective_rows_000 injective_rows_004

theorem injective_join_8_16 : FiniteChecks.Interval injectivityTest 8 16 :=
  FiniteChecks.interval_append injectivityTest 8 12 16 injective_rows_008 injective_rows_012

theorem injective_join_0_16 : FiniteChecks.Interval injectivityTest 0 16 :=
  FiniteChecks.interval_append injectivityTest 0 8 16 injective_join_0_8 injective_join_8_16

theorem injective_join_16_24 : FiniteChecks.Interval injectivityTest 16 24 :=
  FiniteChecks.interval_append injectivityTest 16 20 24 injective_rows_016 injective_rows_020

theorem injective_join_28_36 : FiniteChecks.Interval injectivityTest 28 36 :=
  FiniteChecks.interval_append injectivityTest 28 32 36 injective_rows_028 injective_rows_032

theorem injective_join_24_36 : FiniteChecks.Interval injectivityTest 24 36 :=
  FiniteChecks.interval_append injectivityTest 24 28 36 injective_rows_024 injective_join_28_36

theorem injective_join_16_36 : FiniteChecks.Interval injectivityTest 16 36 :=
  FiniteChecks.interval_append injectivityTest 16 24 36 injective_join_16_24 injective_join_24_36

theorem injective_join_0_36 : FiniteChecks.Interval injectivityTest 0 36 :=
  FiniteChecks.interval_append injectivityTest 0 16 36 injective_join_0_16 injective_join_16_36

theorem injective_join_36_44 : FiniteChecks.Interval injectivityTest 36 44 :=
  FiniteChecks.interval_append injectivityTest 36 40 44 injective_rows_036 injective_rows_040

theorem injective_join_44_52 : FiniteChecks.Interval injectivityTest 44 52 :=
  FiniteChecks.interval_append injectivityTest 44 48 52 injective_rows_044 injective_rows_048

theorem injective_join_36_52 : FiniteChecks.Interval injectivityTest 36 52 :=
  FiniteChecks.interval_append injectivityTest 36 44 52 injective_join_36_44 injective_join_44_52

theorem injective_join_52_60 : FiniteChecks.Interval injectivityTest 52 60 :=
  FiniteChecks.interval_append injectivityTest 52 56 60 injective_rows_052 injective_rows_056

theorem injective_join_64_72 : FiniteChecks.Interval injectivityTest 64 72 :=
  FiniteChecks.interval_append injectivityTest 64 68 72 injective_rows_064 injective_rows_068

theorem injective_join_60_72 : FiniteChecks.Interval injectivityTest 60 72 :=
  FiniteChecks.interval_append injectivityTest 60 64 72 injective_rows_060 injective_join_64_72

theorem injective_join_52_72 : FiniteChecks.Interval injectivityTest 52 72 :=
  FiniteChecks.interval_append injectivityTest 52 60 72 injective_join_52_60 injective_join_60_72

theorem injective_join_36_72 : FiniteChecks.Interval injectivityTest 36 72 :=
  FiniteChecks.interval_append injectivityTest 36 52 72 injective_join_36_52 injective_join_52_72

theorem injective_join_0_72 : FiniteChecks.Interval injectivityTest 0 72 :=
  FiniteChecks.interval_append injectivityTest 0 36 72 injective_join_0_36 injective_join_36_72

theorem injective_join_72_80 : FiniteChecks.Interval injectivityTest 72 80 :=
  FiniteChecks.interval_append injectivityTest 72 76 80 injective_rows_072 injective_rows_076

theorem injective_join_80_88 : FiniteChecks.Interval injectivityTest 80 88 :=
  FiniteChecks.interval_append injectivityTest 80 84 88 injective_rows_080 injective_rows_084

theorem injective_join_72_88 : FiniteChecks.Interval injectivityTest 72 88 :=
  FiniteChecks.interval_append injectivityTest 72 80 88 injective_join_72_80 injective_join_80_88

theorem injective_join_88_96 : FiniteChecks.Interval injectivityTest 88 96 :=
  FiniteChecks.interval_append injectivityTest 88 92 96 injective_rows_088 injective_rows_092

theorem injective_join_100_108 : FiniteChecks.Interval injectivityTest 100 108 :=
  FiniteChecks.interval_append injectivityTest 100 104 108 injective_rows_100 injective_rows_104

theorem injective_join_96_108 : FiniteChecks.Interval injectivityTest 96 108 :=
  FiniteChecks.interval_append injectivityTest 96 100 108 injective_rows_096 injective_join_100_108

theorem injective_join_88_108 : FiniteChecks.Interval injectivityTest 88 108 :=
  FiniteChecks.interval_append injectivityTest 88 96 108 injective_join_88_96 injective_join_96_108

theorem injective_join_72_108 : FiniteChecks.Interval injectivityTest 72 108 :=
  FiniteChecks.interval_append injectivityTest 72 88 108 injective_join_72_88 injective_join_88_108

theorem injective_join_108_116 : FiniteChecks.Interval injectivityTest 108 116 :=
  FiniteChecks.interval_append injectivityTest 108 112 116 injective_rows_108 injective_rows_112

theorem injective_join_116_124 : FiniteChecks.Interval injectivityTest 116 124 :=
  FiniteChecks.interval_append injectivityTest 116 120 124 injective_rows_116 injective_rows_120

theorem injective_join_108_124 : FiniteChecks.Interval injectivityTest 108 124 :=
  FiniteChecks.interval_append injectivityTest 108 116 124 injective_join_108_116 injective_join_116_124

theorem injective_join_124_132 : FiniteChecks.Interval injectivityTest 124 132 :=
  FiniteChecks.interval_append injectivityTest 124 128 132 injective_rows_124 injective_rows_128

theorem injective_join_136_144 : FiniteChecks.Interval injectivityTest 136 144 :=
  FiniteChecks.interval_append injectivityTest 136 140 144 injective_rows_136 injective_rows_140

theorem injective_join_132_144 : FiniteChecks.Interval injectivityTest 132 144 :=
  FiniteChecks.interval_append injectivityTest 132 136 144 injective_rows_132 injective_join_136_144

theorem injective_join_124_144 : FiniteChecks.Interval injectivityTest 124 144 :=
  FiniteChecks.interval_append injectivityTest 124 132 144 injective_join_124_132 injective_join_132_144

theorem injective_join_108_144 : FiniteChecks.Interval injectivityTest 108 144 :=
  FiniteChecks.interval_append injectivityTest 108 124 144 injective_join_108_124 injective_join_124_144

theorem injective_join_72_144 : FiniteChecks.Interval injectivityTest 72 144 :=
  FiniteChecks.interval_append injectivityTest 72 108 144 injective_join_72_108 injective_join_108_144

theorem injective_join_0_144 : FiniteChecks.Interval injectivityTest 0 144 :=
  FiniteChecks.interval_append injectivityTest 0 72 144 injective_join_0_72 injective_join_72_144

theorem injective_join_144_152 : FiniteChecks.Interval injectivityTest 144 152 :=
  FiniteChecks.interval_append injectivityTest 144 148 152 injective_rows_144 injective_rows_148

theorem injective_join_152_160 : FiniteChecks.Interval injectivityTest 152 160 :=
  FiniteChecks.interval_append injectivityTest 152 156 160 injective_rows_152 injective_rows_156

theorem injective_join_144_160 : FiniteChecks.Interval injectivityTest 144 160 :=
  FiniteChecks.interval_append injectivityTest 144 152 160 injective_join_144_152 injective_join_152_160

theorem injective_join_160_168 : FiniteChecks.Interval injectivityTest 160 168 :=
  FiniteChecks.interval_append injectivityTest 160 164 168 injective_rows_160 injective_rows_164

theorem injective_join_172_180 : FiniteChecks.Interval injectivityTest 172 180 :=
  FiniteChecks.interval_append injectivityTest 172 176 180 injective_rows_172 injective_rows_176

theorem injective_join_168_180 : FiniteChecks.Interval injectivityTest 168 180 :=
  FiniteChecks.interval_append injectivityTest 168 172 180 injective_rows_168 injective_join_172_180

theorem injective_join_160_180 : FiniteChecks.Interval injectivityTest 160 180 :=
  FiniteChecks.interval_append injectivityTest 160 168 180 injective_join_160_168 injective_join_168_180

theorem injective_join_144_180 : FiniteChecks.Interval injectivityTest 144 180 :=
  FiniteChecks.interval_append injectivityTest 144 160 180 injective_join_144_160 injective_join_160_180

theorem injective_join_180_188 : FiniteChecks.Interval injectivityTest 180 188 :=
  FiniteChecks.interval_append injectivityTest 180 184 188 injective_rows_180 injective_rows_184

theorem injective_join_188_196 : FiniteChecks.Interval injectivityTest 188 196 :=
  FiniteChecks.interval_append injectivityTest 188 192 196 injective_rows_188 injective_rows_192

theorem injective_join_180_196 : FiniteChecks.Interval injectivityTest 180 196 :=
  FiniteChecks.interval_append injectivityTest 180 188 196 injective_join_180_188 injective_join_188_196

theorem injective_join_196_204 : FiniteChecks.Interval injectivityTest 196 204 :=
  FiniteChecks.interval_append injectivityTest 196 200 204 injective_rows_196 injective_rows_200

theorem injective_join_208_216 : FiniteChecks.Interval injectivityTest 208 216 :=
  FiniteChecks.interval_append injectivityTest 208 212 216 injective_rows_208 injective_rows_212

theorem injective_join_204_216 : FiniteChecks.Interval injectivityTest 204 216 :=
  FiniteChecks.interval_append injectivityTest 204 208 216 injective_rows_204 injective_join_208_216

theorem injective_join_196_216 : FiniteChecks.Interval injectivityTest 196 216 :=
  FiniteChecks.interval_append injectivityTest 196 204 216 injective_join_196_204 injective_join_204_216

theorem injective_join_180_216 : FiniteChecks.Interval injectivityTest 180 216 :=
  FiniteChecks.interval_append injectivityTest 180 196 216 injective_join_180_196 injective_join_196_216

theorem injective_join_144_216 : FiniteChecks.Interval injectivityTest 144 216 :=
  FiniteChecks.interval_append injectivityTest 144 180 216 injective_join_144_180 injective_join_180_216

theorem injective_join_216_224 : FiniteChecks.Interval injectivityTest 216 224 :=
  FiniteChecks.interval_append injectivityTest 216 220 224 injective_rows_216 injective_rows_220

theorem injective_join_224_232 : FiniteChecks.Interval injectivityTest 224 232 :=
  FiniteChecks.interval_append injectivityTest 224 228 232 injective_rows_224 injective_rows_228

theorem injective_join_216_232 : FiniteChecks.Interval injectivityTest 216 232 :=
  FiniteChecks.interval_append injectivityTest 216 224 232 injective_join_216_224 injective_join_224_232

theorem injective_join_232_240 : FiniteChecks.Interval injectivityTest 232 240 :=
  FiniteChecks.interval_append injectivityTest 232 236 240 injective_rows_232 injective_rows_236

theorem injective_join_244_252 : FiniteChecks.Interval injectivityTest 244 252 :=
  FiniteChecks.interval_append injectivityTest 244 248 252 injective_rows_244 injective_rows_248

theorem injective_join_240_252 : FiniteChecks.Interval injectivityTest 240 252 :=
  FiniteChecks.interval_append injectivityTest 240 244 252 injective_rows_240 injective_join_244_252

theorem injective_join_232_252 : FiniteChecks.Interval injectivityTest 232 252 :=
  FiniteChecks.interval_append injectivityTest 232 240 252 injective_join_232_240 injective_join_240_252

theorem injective_join_216_252 : FiniteChecks.Interval injectivityTest 216 252 :=
  FiniteChecks.interval_append injectivityTest 216 232 252 injective_join_216_232 injective_join_232_252

theorem injective_join_252_260 : FiniteChecks.Interval injectivityTest 252 260 :=
  FiniteChecks.interval_append injectivityTest 252 256 260 injective_rows_252 injective_rows_256

theorem injective_join_264_272 : FiniteChecks.Interval injectivityTest 264 272 :=
  FiniteChecks.interval_append injectivityTest 264 268 272 injective_rows_264 injective_rows_268

theorem injective_join_260_272 : FiniteChecks.Interval injectivityTest 260 272 :=
  FiniteChecks.interval_append injectivityTest 260 264 272 injective_rows_260 injective_join_264_272

theorem injective_join_252_272 : FiniteChecks.Interval injectivityTest 252 272 :=
  FiniteChecks.interval_append injectivityTest 252 260 272 injective_join_252_260 injective_join_260_272

theorem injective_join_272_280 : FiniteChecks.Interval injectivityTest 272 280 :=
  FiniteChecks.interval_append injectivityTest 272 276 280 injective_rows_272 injective_rows_276

theorem injective_join_284_290 : FiniteChecks.Interval injectivityTest 284 290 :=
  FiniteChecks.interval_append injectivityTest 284 288 290 injective_rows_284 injective_rows_288

theorem injective_join_280_290 : FiniteChecks.Interval injectivityTest 280 290 :=
  FiniteChecks.interval_append injectivityTest 280 284 290 injective_rows_280 injective_join_284_290

theorem injective_join_272_290 : FiniteChecks.Interval injectivityTest 272 290 :=
  FiniteChecks.interval_append injectivityTest 272 280 290 injective_join_272_280 injective_join_280_290

theorem injective_join_252_290 : FiniteChecks.Interval injectivityTest 252 290 :=
  FiniteChecks.interval_append injectivityTest 252 272 290 injective_join_252_272 injective_join_272_290

theorem injective_join_216_290 : FiniteChecks.Interval injectivityTest 216 290 :=
  FiniteChecks.interval_append injectivityTest 216 252 290 injective_join_216_252 injective_join_252_290

theorem injective_join_144_290 : FiniteChecks.Interval injectivityTest 144 290 :=
  FiniteChecks.interval_append injectivityTest 144 216 290 injective_join_144_216 injective_join_216_290

theorem injective_join_0_290 : FiniteChecks.Interval injectivityTest 0 290 :=
  FiniteChecks.interval_append injectivityTest 0 144 290 injective_join_0_144 injective_join_144_290

theorem cells_injective : Function.Injective cells := by
  have hinverse (a : Fin 290) : edgeInverse (cells a) = a.val :=
    of_decide_eq_true (FiniteChecks.fin_of_interval
      (fun a : Fin 290 => decide (edgeInverse (cells a) = a.val))
      injective_join_0_290 a)
  intro a b hab
  apply Fin.ext
  rw [← hinverse a, ← hinverse b, hab]
 theorem root_exact : cells 0 = triangle 7 (by decide) := by decide +kernel
 theorem permMaps_injective : ∀ p, Function.Injective (permMaps p) := by decide +kernel
 theorem permMaps_preserve_root : ∀ p,
    relabelPolygon (permMaps p) (triangle 7 (by decide)) = triangle 7 (by decide) := by
  decide +kernel

end N7
end Papers.RationalityTen.FiniteCycleCandidates

end
end BundlePart6

section BundlePart7
/- Source: FinitePolygonTemplates.lean -/







@[expose] public section

namespace Papers.RationalityTen.FiniteCycleCandidates
open MatroidChecked PolygonBoundaryCatalogue
set_option maxRecDepth 100000

namespace N5
def templateTable : LiteralLookup (Finset (Polygon 5)) := (.node 1 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,4},{(0,1),(0,4),(1,4)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{0,3,4},{(0,3),(0,4),(3,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩})))
def templates (i : Fin 2) := templateTable.get i.val
end N5

namespace N6
def templateTable : LiteralLookup (Finset (Polygon 6)) := (.node 3 (.node 1 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩,⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})) (.node 2 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{0,3,4},{(0,3),(0,4),(3,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})))) (.node 5 (.node 4 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩}))) (.node 6 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩})))))
def templates (i : Fin 7) := templateTable.get i.val
end N6

namespace N7
def templateTable : LiteralLookup (Finset (Polygon 7)) := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩,⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩,⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩}))) (.node 3 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})))) (.node 6 (.node 5 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{1,4,5},{(1,4),(1,5),(4,5)}⟩,⟨{2,3,6},{(2,3),(2,6),(3,6)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩,⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{1,4,5},{(1,4),(1,5),(4,5)}⟩,⟨{2,3,6},{(2,3),(2,6),(3,6)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))) (.node 7 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))))) (.node 12 (.node 10 (.node 9 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{0,4,5},{(0,4),(0,5),(4,5)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,3,6},{(2,3),(2,6),(3,6)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩}))) (.node 11 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})))) (.node 14 (.node 13 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))) (.node 15 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{0,3,4},{(0,3),(0,4),(3,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})) (.node 16 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{1,5,6},{(1,5),(1,6),(5,6)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))))))) (.node 25 (.node 21 (.node 19 (.node 18 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,6},{(2,3),(2,6),(3,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩}))) (.node 20 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩,⟨{1,2,6},{(1,2),(1,6),(2,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5},{(1,2),(1,5),(2,5)}⟩,⟨{1,3,5},{(1,3),(1,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5,6},{(3,4),(3,5),(4,6),(5,6)}⟩})))) (.node 23 (.node 22 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,5},{(2,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5,6},{(3,4),(3,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5,6},{(0,1),(0,6),(1,3),(3,4),(4,5),(5,6)}⟩,⟨{0,2,6},{(0,2),(0,6),(2,6)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩}))) (.node 24 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,5,6},{(2,3),(2,6),(3,5),(5,6)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5,6},{(1,2),(1,6),(2,5),(5,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))))) (.node 29 (.node 27 (.node 26 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,6},{(2,4),(2,6),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5,6},{(3,4),(3,5),(4,6),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩,⟨{2,3,4,6},{(2,3),(2,6),(3,4),(4,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))) (.node 28 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩,⟨{1,2,6},{(1,2),(1,6),(2,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,5,6},{(3,4),(3,6),(4,5),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5,6},{(1,2),(1,6),(2,5),(5,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5},{(3,4),(3,5),(4,5)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})))) (.node 31 (.node 30 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,5,6},{(1,2),(1,6),(2,5),(5,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{2,4,5},{(2,4),(2,5),(4,5)}⟩,⟨{3,4,5,6},{(3,4),(3,6),(4,5),(5,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3,6},{(1,2),(1,3),(2,6),(3,6)}⟩,⟨{2,5,6},{(2,5),(2,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{4,5,6},{(4,5),(4,6),(5,6)}⟩}))) (.node 32 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩,⟨{1,2,3,5},{(1,2),(1,3),(2,5),(3,5)}⟩,⟨{2,4,5,6},{(2,4),(2,5),(4,6),(5,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩,⟨{3,5,6},{(3,5),(3,6),(5,6)}⟩})) (.node 33 (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4,5},{(0,1),(0,5),(1,3),(3,4),(4,5)}⟩,⟨{0,2,5},{(0,2),(0,5),(2,5)}⟩,⟨{1,2,3,6},{(1,2),(1,3),(2,6),(3,6)}⟩,⟨{2,4,5,6},{(2,5),(2,6),(4,5),(4,6)}⟩,⟨{3,4,6},{(3,4),(3,6),(4,6)}⟩})) (.leaf ({⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩,⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩,⟨{0,2,4,5},{(0,2),(0,4),(2,5),(4,5)}⟩,⟨{1,2,5,6},{(1,2),(1,6),(2,5),(5,6)}⟩,⟨{1,3,6},{(1,3),(1,6),(3,6)}⟩,⟨{3,4,5,6},{(3,4),(3,6),(4,5),(5,6)}⟩}))))))))
def templates (i : Fin 34) := templateTable.get i.val
end N7

end Papers.RationalityTen.FiniteCycleCandidates

end
end BundlePart7

section BundlePart8
/- Source: PolygonDAGSemantics.lean -/






@[expose] public section

/-!
# Exact semantic bridge from polygon boundaries to the growth checker

The executable ridge labels are a bijective coding of ordered endpoint
pairs. The complete ridge lists and compatibility data must be checked
against the literal polygons. Once they agree, the mathematical validity
and connectedness hypotheses supply every premise of the growth theorem.
-/

noncomputable section
namespace Papers.RationalityTen.PolygonDAGSemantics

open Finset Set
open scoped Classical
open PolygonBoundaryCatalogue BoundarySearch
open GrowthDAG SparseGrowthDAG GrowthPruning

variable {n c r : ℕ}

theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

@[simp] theorem family_toList (S : Finset (Fin c)) (a : Fin c) :
    SparseGrowthDAG.family S.toList a = true ↔ a ∈ S := by
  rw [SparseGrowthDAG.family, has_true, Finset.mem_toList]

/-- The pairing count supplies a distinct mate for each actual occurrence. -/
theorem hasMate_of_valid (cells : Fin c → Polygon n) (S : Finset (Fin c))
    (ridgeList : Fin c → List (Fin r)) (code : (Fin n × Fin n) ≃ Fin r)
    (hridges : ∀ a q, has (ridgeList a) (code q) = true ↔ q ∈ (cells a).edges)
    (hv : valid cells S) :
    HasMate (fun a => has (ridgeList a)) (SparseGrowthDAG.family S.toList) := by
  intro q a ha
  let I := incidence (ridges cells) S (code.symm q)
  have haI : a ∈ I := Finset.mem_filter.mpr
    ⟨(family_toList S a).mp ha.1, (hridges a _).mp (by simpa using ha.2)⟩
  have hcard : I.card = 2 := by
    have hp := Finset.card_pos.mpr ⟨a, haI⟩
    have hcounts : I.card = 0 ∨ I.card = 2 := hv.1 (code.symm q)
    rcases hcounts with h | h <;> omega
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) a
  obtain ⟨hbS, hbq⟩ := Finset.mem_filter.mp hb
  refine ⟨b, ⟨(family_toList S b).mpr hbS, ?_⟩, hba⟩
  simpa using (hridges b (code.symm q)).mpr hbq

/-- The same incidence count rules out any three distinct incident cells. -/
theorem noThree_of_valid (cells : Fin c → Polygon n) (S : Finset (Fin c))
    (ridgeList : Fin c → List (Fin r)) (code : (Fin n × Fin n) ≃ Fin r)
    (hridges : ∀ a q, has (ridgeList a) (code q) = true ↔ q ∈ (cells a).edges)
    (hv : valid cells S) :
    NoThree (fun a => has (ridgeList a)) (SparseGrowthDAG.family S.toList) := by
  intro q a b z ha hb hz
  by_cases hab : a = b
  · exact Or.inl hab
  by_cases haz : a = z
  · exact Or.inr (Or.inl haz)
  by_cases hbz : b = z
  · exact Or.inr (Or.inr hbz)
  exfalso
  let I := incidence (ridges cells) S (code.symm q)
  have memI (x : Fin c) (hx : Incident (fun a => has (ridgeList a))
      (SparseGrowthDAG.family S.toList) q x) : x ∈ I :=
    Finset.mem_filter.mpr ⟨(family_toList S x).mp hx.1,
      (hridges x _).mp (by simpa using hx.2)⟩
  have hsub : ({a, b, z} : Finset (Fin c)) ⊆ I := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact hx.symm ▸ memI a ha
    · exact hx.symm ▸ memI b hb
    · exact hx.symm ▸ memI z hz
  have hc := Finset.card_le_card hsub
  have hthree : ({a, b, z} : Finset (Fin c)).card = 3 := by simp [hab, haz, hbz]
  rw [hthree] at hc
  have hcounts : I.card = 0 ∨ I.card = 2 := hv.1 (code.symm q)
  rcases hcounts with h | h <;> omega

/-- Every nonempty proper Boolean subfamily corresponds to an ordinary
finite subfamily, so actual ridge connectedness transfers exactly. -/
theorem connected_of_ridgeConnected (cells : Fin c → Polygon n) (S : Finset (Fin c))
    (ridgeList : Fin c → List (Fin r)) (code : (Fin n × Fin n) ≃ Fin r)
    (hridges : ∀ a q, has (ridgeList a) (code q) = true ↔ q ∈ (cells a).edges)
    (hc : RidgeConnected (ridges cells) S) :
    Connected (fun a => has (ridgeList a)) (SparseGrowthDAG.family S.toList) := by
  intro U hUS hUne hUneS
  let T : Finset (Fin c) := Finset.univ.filter fun a => U a = true
  have hTsub : T ⊆ S := by
    intro a ha
    exact (family_toList S a).mp (hUS a (Finset.mem_filter.mp ha).2)
  have hTne : T.Nonempty := by
    obtain ⟨a, ha⟩ := hUne
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hTneq : T ≠ S := by
    intro hTS
    apply hUneS
    intro a
    apply bool_eq_of_true_iff
    rw [family_toList, ← hTS]
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨a, haT, b, hbS, hbT, q, hqa, hqb⟩ := hc T hTsub hTne hTneq
  refine ⟨code q, a, b, ⟨(Finset.mem_filter.mp haT).2, (hridges a q).mpr hqa⟩,
    ⟨(family_toList S b).mpr hbS, (hridges b q).mpr hqb⟩, ?_⟩
  cases hUb : U b with
  | false => rfl
  | true => exact (hbT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUb⟩)).elim

/-- Constant cell kind zero represents a bound on the total facet count. -/
theorem constant_kind_budget (S : Finset (Fin c)) (bound : ℕ) (hS : S.card ≤ bound) :
    ∀ j, kindCount (fun _ : Fin c => 0) S.toList j ≤ if j = 0 then bound else 0 := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa only [kindCount, decide_true, List.filter_true, Finset.length_toList, ite_true] using hS
  · simp [kindCount, hj, Ne.symm hj]

/-- Pointwise Boolean equality gives literal equality of the finite cell
families, with no dependence on list order or duplicate entries. -/
theorem finset_eq_of_same (L : List (Fin c)) (S : Finset (Fin c))
    (h : Same (SparseGrowthDAG.family L) (SparseGrowthDAG.family S.toList)) :
    L.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  constructor
  · intro ha
    exact (family_toList S a).mp ((h a).symm.trans ((has_true L a).mpr ha))
  · intro ha
    exact (has_true L a).mp ((h a).trans ((family_toList S a).mpr ha))

/-- A per-cell equality is sufficient to certify the complete ridge code. -/
theorem ridge_code_of_lists (cells : Fin c → Polygon n)
    (ridgeList : Fin c → List (Fin r)) (code : (Fin n × Fin n) ≃ Fin r)
    (h : ∀ a, (ridgeList a).toFinset = (cells a).edges.image code) :
    ∀ a q, has (ridgeList a) (code q) = true ↔ q ∈ (cells a).edges := by
  intro a q
  rw [has_true, ← List.mem_toFinset, h a]
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    exact code.injective hpq ▸ hp
  · intro hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- A terminal either has a checked relabeling to a literal template, or
it is checked to violate the geometric validity predicate. The branch is
determined by data, but no claim about that data is trusted. -/
def terminalCheck {t : ℕ} (cells : Fin c → Polygon n)
    (templates : Fin t → Finset (Polygon n)) (L : List (Fin c))
    (target : ℕ) (permutation : Fin n → Fin n) : Bool :=
  if h : target < t then
    decide (Function.Injective permutation ∧
      relabelBoundary cells permutation L.toFinset = templates ⟨target, h⟩)
  else decide (¬ valid cells L.toFinset)

/-- Checked terminal data give an actual permutation and exact equality
of complete polygon boundaries. Invalid terminals cannot represent a
valid target boundary. -/
theorem terminalCheck_sound {t : ℕ} (cells : Fin c → Polygon n)
    (templates : Fin t → Finset (Polygon n)) (L : List (Fin c))
    (target : ℕ) (permutation : Fin n → Fin n)
    (hcheck : terminalCheck cells templates L target permutation = true)
    (S : Finset (Fin c)) (hLS : L.toFinset = S) (hvalid : valid cells S) :
    ∃ (σ : Equiv.Perm (Fin n)) (i : Fin t),
      relabelBoundary cells σ S = templates i := by
  by_cases ht : target < t
  · have hgood : Function.Injective permutation ∧
        relabelBoundary cells permutation L.toFinset = templates ⟨target, ht⟩ := by
      exact of_decide_eq_true (by simpa only [terminalCheck, dif_pos ht] using hcheck)
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective permutation
      ⟨hgood.1, Finite.surjective_of_injective hgood.1⟩
    refine ⟨σ, ⟨target, ht⟩, ?_⟩
    change relabelBoundary cells permutation S = templates ⟨target, ht⟩
    rw [← hLS]
    exact hgood.2
  · have hbad : ¬ valid cells L.toFinset :=
      of_decide_eq_true (by simpa only [terminalCheck, dif_neg ht] using hcheck)
    exact (hbad (hLS.symm ▸ hvalid)).elim

end Papers.RationalityTen.PolygonDAGSemantics

end
end
end BundlePart8

section BundlePart9
/- Source: PolygonN5Classification.lean -/







@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N5
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

noncomputable def edgeCode : (Fin 5 × Fin 5) ≃ Fin 25 := finProdFinEquiv

noncomputable def ridgeDataTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 16 index
  decide ((PolygonGrowth.N5.ridgeList a).toFinset = (FiniteCycleCandidates.N5.cells a).edges.image edgeCode)

noncomputable def compatibilityTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 16 index
  decide (∀ b : Fin 16, PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N5.cells a) (FiniteCycleCandidates.N5.cells b) →
    PolygonGrowth.N5.compatible a b = true)

noncomputable def terminalTest (index : ℕ) : Bool :=
  let j := Fin.ofNat 7 index
  terminalCheck FiniteCycleCandidates.N5.cells FiniteCycleCandidates.N5.templates (PolygonGrowth.N5.terminals j)
    (PolygonGrowth.N5.targetTemplate j) (decode (by decide : 0 < 5) (PolygonGrowth.N5.permutationCode j))

theorem ridge_data_00000 : FiniteChecks.Interval ridgeDataTest 0 8 :=
  FiniteChecks.interval_of_check ridgeDataTest 0 8 (by decide +kernel)

theorem ridge_data_00008 : FiniteChecks.Interval ridgeDataTest 8 16 :=
  FiniteChecks.interval_of_check ridgeDataTest 8 8 (by decide +kernel)

theorem ridge_data_join_00000_00016 : FiniteChecks.Interval ridgeDataTest 0 16 :=
  FiniteChecks.interval_append ridgeDataTest 0 8 16 ridge_data_00000 ridge_data_00008

theorem compatibility_data_00000 : FiniteChecks.Interval compatibilityTest 0 8 :=
  FiniteChecks.interval_of_check compatibilityTest 0 8 (by decide +kernel)

theorem compatibility_data_00008 : FiniteChecks.Interval compatibilityTest 8 16 :=
  FiniteChecks.interval_of_check compatibilityTest 8 8 (by decide +kernel)

theorem compatibility_data_join_00000_00016 : FiniteChecks.Interval compatibilityTest 0 16 :=
  FiniteChecks.interval_append compatibilityTest 0 8 16 compatibility_data_00000 compatibility_data_00008

theorem terminal_data_00000 : FiniteChecks.Interval terminalTest 0 7 :=
  FiniteChecks.interval_of_check terminalTest 0 7 (by decide +kernel)

theorem ridgeData_exact (a : Fin 16) :
    (PolygonGrowth.N5.ridgeList a).toFinset = (FiniteCycleCandidates.N5.cells a).edges.image edgeCode := by
  exact of_decide_eq_true (FiniteChecks.fin_of_interval
    (fun a : Fin 16 => decide ((PolygonGrowth.N5.ridgeList a).toFinset =
      (FiniteCycleCandidates.N5.cells a).edges.image edgeCode)) ridge_data_join_00000_00016 a)

theorem ridge_encoding : ∀ a q,
    has (PolygonGrowth.N5.ridgeList a) (edgeCode q) = true ↔ q ∈ (FiniteCycleCandidates.N5.cells a).edges :=
  ridge_code_of_lists FiniteCycleCandidates.N5.cells PolygonGrowth.N5.ridgeList edgeCode ridgeData_exact

theorem compatibility_sound (a b : Fin 16)
    (h : PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N5.cells a) (FiniteCycleCandidates.N5.cells b)) :
    PolygonGrowth.N5.compatible a b = true := by
  have ha := of_decide_eq_true (FiniteChecks.fin_of_interval
    (fun a : Fin 16 => decide (∀ b : Fin 16,
      PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N5.cells a) (FiniteCycleCandidates.N5.cells b) →
        PolygonGrowth.N5.compatible a b = true)) compatibility_data_join_00000_00016 a)
  exact ha b h

theorem terminal_checked (j : Fin 7) :
    terminalCheck FiniteCycleCandidates.N5.cells FiniteCycleCandidates.N5.templates (PolygonGrowth.N5.terminals j)
      (PolygonGrowth.N5.targetTemplate j) (decode (by decide : 0 < 5) (PolygonGrowth.N5.permutationCode j)) = true :=
  FiniteChecks.fin_of_interval (fun j : Fin 7 =>
    terminalCheck FiniteCycleCandidates.N5.cells FiniteCycleCandidates.N5.templates (PolygonGrowth.N5.terminals j)
      (PolygonGrowth.N5.targetTemplate j) (decode (by decide : 0 < 5) (PolygonGrowth.N5.permutationCode j)))
    terminal_data_00000 j

theorem neighbor_coverage : ∀ i ∈ FiniteCycleCandidates.N5.neighbors,
    ∃ seed : Fin 2, PolygonGrowth.N5.neighbors seed = i := by decide +kernel

/-- Complete classification of every paired, compatible, connected polygon
boundary in the normalized universe, with all minimum-degree and Euler
conditions. Every finite certificate premise has been checked above. -/
theorem normalized_classification (S : Finset (Fin 16))
    (hcard : S.card ≤ 2 * 5 - 4)
    (hpair : (S : Set _).Pairwise (fun a b =>
      PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N5.cells a) (FiniteCycleCandidates.N5.cells b)))
    (hvalid : valid FiniteCycleCandidates.N5.cells S) (hconn : RidgeConnected (ridges FiniteCycleCandidates.N5.cells) S)
    (hroot : (0 : Fin 16) ∈ S) (hneighbor : (S ∩ FiniteCycleCandidates.N5.neighbors).Nonempty) :
    ∃ (σ : Equiv.Perm (Fin 5)) (i : Fin 2),
      relabelBoundary FiniteCycleCandidates.N5.cells σ S = FiniteCycleCandidates.N5.templates i := by
  obtain ⟨neighbor, hneighbor⟩ := hneighbor
  obtain ⟨hneighborS, hneighborN⟩ := Finset.mem_inter.mp hneighbor
  obtain ⟨seed, hseed⟩ := neighbor_coverage neighbor hneighborN
  have hquota : ∀ j, kindCount PolygonGrowth.N5.kind S.toList j ≤ PolygonGrowth.N5.quota j := by
    change ∀ j, kindCount (fun _ : Fin 16 => 0) S.toList j ≤ if j = 0 then 6 else 0
    exact constant_kind_budget S 6 hcard
  have hcompatible : ∀ a b, a ∈ S.toList → b ∈ S.toList → a ≠ b →
      PolygonGrowth.N5.compatible a b = true := by
    intro a b ha hb hab
    exact compatibility_sound a b (hpair (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab)
  obtain ⟨j, hj⟩ := PolygonGrowth.N5.boundary_classification S.toList hquota hcompatible
    (hasMate_of_valid FiniteCycleCandidates.N5.cells S PolygonGrowth.N5.ridgeList edgeCode ridge_encoding hvalid)
    (noThree_of_valid FiniteCycleCandidates.N5.cells S PolygonGrowth.N5.ridgeList edgeCode ridge_encoding hvalid)
    (connected_of_ridgeConnected FiniteCycleCandidates.N5.cells S PolygonGrowth.N5.ridgeList edgeCode ridge_encoding hconn)
    seed (Finset.mem_toList.mpr hroot) (by rw [hseed]; exact Finset.mem_toList.mpr hneighborS)
  exact terminalCheck_sound FiniteCycleCandidates.N5.cells FiniteCycleCandidates.N5.templates (PolygonGrowth.N5.terminals j)
    (PolygonGrowth.N5.targetTemplate j) (decode (by decide : 0 < 5) (PolygonGrowth.N5.permutationCode j))
    (terminal_checked j) S (finset_eq_of_same _ S hj) hvalid

#print axioms normalized_classification
end Papers.RationalityTen.ConcretePolygonClassification.N5

end
end BundlePart9

section BundlePart10
/- Source: ActualSmallFacetClassification.lean -/





@[expose] public section

/-!
# Actual four- and five-vertex three-polytope classification

The finite search has no remaining premise in these theorems. Every
three-dimensional convex polytope with the stated number of vertices has
one of the literal complete polygon boundaries, after a permutation of
its actual vertices. The ambient Euclidean dimension is unrestricted.
-/

noncomputable section
namespace Papers.RationalityTen.ActualSmallFacetClassification

open Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting ActualPolygonBoundary

variable {d : ℕ}

theorem four_vertex_classification (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = 4) :
    ∃ (lab : P.vertices ≃ Fin 4) (i : Fin 1),
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) =
        FiniteCycleCandidates.N4.templates i := by
  apply actual_classification_of_finite P hP hn (by decide) (by decide)
    FiniteCycleCandidates.N4.cells 0 FiniteCycleCandidates.N4.neighbors
    FiniteCycleCandidates.N4.templates
    FiniteCycleCandidates.N4.cells_injective FiniteCycleCandidates.N4.root_exact
    FiniteCycleCandidates.N4.covers_rooted_cycles FiniteCycleCandidates.N4.normalizes_root_neighbor
  intro S _ _ hv _ _ _
  exact FiniteCycleCandidates.N4.normalized_classification S hv

theorem five_vertex_classification (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = 5) :
    ∃ (lab : P.vertices ≃ Fin 5) (i : Fin 2),
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) =
        FiniteCycleCandidates.N5.templates i :=
  actual_classification_of_finite P hP hn (by decide) (by decide)
    FiniteCycleCandidates.N5.cells 0 FiniteCycleCandidates.N5.neighbors
    FiniteCycleCandidates.N5.templates
    FiniteCycleCandidates.N5.cells_injective FiniteCycleCandidates.N5.root_exact
    FiniteCycleCandidates.N5.covers_rooted_cycles FiniteCycleCandidates.N5.normalizes_root_neighbor
    ConcretePolygonClassification.N5.normalized_classification

end Papers.RationalityTen.ActualSmallFacetClassification

end
end
end BundlePart10

section BundlePart11
/- Source: ActualFacetCatalogueTransport.lean -/






@[expose] public section

/-!
# From local polygon templates to complete four-polytope facet cells

The local three-dimensional classification must preserve the complete
polygon boundary. This file proves that its polygons determine the exact
edge and ridge families needed by the four-dimensional finite search,
and transports them along the actual inclusion of facet vertices.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFacetCatalogueTransport

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeBoundaryIncidence
open ActualFaceTransport ActualPolygonBoundary PolygonBoundaryCatalogue
open MatroidChecked.FacetBoundaryEncoding

variable {d m n c : ℕ}

/-- The full literal polygon boundary of an actual three-polytope. -/
def polygonBoundary (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) :
    Finset (Polygon n) :=
  (Finset.univ : Finset (Face P 2)).image (polygon P lab)

/-- Every polygon edge is a genuine edge, and every genuine edge belongs
to a polygon. Thus the reconstructed edge family is exact. -/
theorem boundary_edges_eq (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (hP : P.dim = 3) :
    (cellOfBoundary (polygonBoundary P lab)).edges = ActualFaceTransport.family P lab 1 := by
  ext S
  constructor
  · intro hS
    obtain ⟨C, hC, hSC⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨F, _, hFC⟩ := Finset.mem_image.mp hC
    obtain ⟨r, hr, hrS⟩ := Finset.mem_image.mp hSC
    rw [← hFC] at hr
    obtain ⟨A, _, hAr⟩ := (polygon_edge_iff P lab F r).mp hr
    apply Finset.mem_image.mpr
    refine ⟨A, Finset.mem_univ _, ?_⟩
    rw [← edgePair_labels, hAr]
    exact hrS
  · intro hS
    obtain ⟨A, _, hAS⟩ := Finset.mem_image.mp hS
    obtain ⟨F, hAF⟩ := edge_in_polygon P hP A
    apply Finset.mem_biUnion.mpr
    refine ⟨polygon P lab F, Finset.mem_image.mpr ⟨F, Finset.mem_univ _, rfl⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨edgePair P lab A, (polygon_edge_iff P lab F _).mpr ⟨A, hAF, rfl⟩, ?_⟩
    rw [edgePair_labels]
    exact hAS

/-- The reconstructed ridges are exactly the polygonal facets. -/
theorem boundary_ridges_eq (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) :
    (cellOfBoundary (polygonBoundary P lab)).ridges = ActualFaceTransport.family P lab 2 := by
  change ((Finset.univ : Finset (Face P 2)).image (polygon P lab)).image Polygon.vertices = _
  rw [Finset.image_image]
  rfl

/-- Exact complete cell of a facet, recovered from its local boundary. -/
theorem actualCell_of_local_boundary (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 3) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m) :
    actualCell P lab F = mapCell (labelEmbedding P lab F loc)
      (cellOfBoundary (polygonBoundary (facePolytope P F.val.isFace) loc)) := by
  have hQ : (facePolytope P F.val.isFace).dim = 3 := by
    change faceDim (facePolytope P F.val.isFace).toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  apply cell_ext
  · exact (vertices_image P lab F loc).symm
  · change lowerFamily P lab F 1 =
      ((cellOfBoundary (polygonBoundary _ loc)).edges).image
        (fun S => S.image (labelEmbedding P lab F loc))
    rw [boundary_edges_eq _ loc hQ]
    exact (family_image P lab F loc 1).symm
  · change lowerFamily P lab F 2 =
      ((cellOfBoundary (polygonBoundary _ loc)).ridges).image
        (fun S => S.image (labelEmbedding P lab F loc))
    rw [boundary_ridges_eq]
    exact (family_image P lab F loc 2).symm

/-- A literal local template classification yields the exact ambient cell. -/
theorem actualCell_of_template (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 3) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m)
    (B : Finset (Polygon m))
    (hB : polygonBoundary (facePolytope P F.val.isFace) loc = B) :
    actualCell P lab F = mapCell (labelEmbedding P lab F loc) (cellOfBoundary B) := by
  rw [actualCell_of_local_boundary, hB]

/-- Supply an explicit literal cell universe with the complete actual
facet encoding. The first premise is provided by the local 3-polytope
classification; the second is a pure finite template-embedding check.
The optional eligibility predicate can express a normalized root or the
already proved facet-size restrictions of the residual branch. -/
theorem actual_encoding_of_local_templates {T : Type*}
    (size : T → ℕ) (templates : (t : T) → Finset (Polygon (size t)))
    (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) (cells : Fin c → Cell n)
    (eligible : Cell n → Prop)
    (hlocal : ∀ F : Face P 3, ∃ t : T,
      ∃ loc : (facePolytope P F.val.isFace).vertices ≃ Fin (size t),
        polygonBoundary (facePolytope P F.val.isFace) loc = templates t)
    (heligible : ∀ F : Face P 3, eligible (actualCell P lab F))
    (hfinite : ∀ t : T, ∀ f : Fin (size t) ↪ Fin n,
      eligible (mapCell f (cellOfBoundary (templates t))) →
        ∃ i : Fin c, cells i = mapCell f (cellOfBoundary (templates t))) :
    Nonempty (MatroidChecked.FacetBoundaryEncoding.Encoding P lab cells) := by
  apply MatroidChecked.FacetBoundaryEncoding.encoding_of_coverage P lab cells
  intro F
  obtain ⟨t, loc, hloc⟩ := hlocal F
  have heq := actualCell_of_template P lab F loc (templates t) hloc
  obtain ⟨i, hi⟩ := hfinite t (labelEmbedding P lab F loc) (by
    rw [← heq]
    exact heligible F)
  exact ⟨i, hi.trans heq.symm⟩

end Papers.RationalityTen.ActualFacetCatalogueTransport

end
end
end BundlePart11
