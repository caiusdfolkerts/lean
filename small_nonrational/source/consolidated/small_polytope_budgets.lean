module
public import Papers.PolytopeEulerFour
public import Papers.ActualNeighborBound
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Papers.PolytopeBoundaryIncidence
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Papers.ActualHomogeneousFaceRanks
public import Papers.FiniteRelationSpaceExtensions
public import Mathlib.Data.Fintype.Sigma
public import Papers.RationalityTenFacetRelationSpace
public import Papers.RationalityTenFacetExtension
public import Papers.ActualCoordinateRealizations
public import Papers.SparseRelationGenerators
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Logic.Equiv.Fintype
public import Lean.Elab.Tactic.Omega

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/PolytopeSmallFacetBounds.lean -/





@[expose] public section

/-!
# Geometric bounds needed by the small-facet catalogue

The triangle required to root the finite search is
derived for every actual three-dimensional polytope on at most seven
vertices. The facet bound and incidence counts also refer to actual
faces. No catalogue-completeness hypothesis is introduced.
-/

noncomputable section

namespace Papers.PolytopeSmallFacetBounds

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerThree Papers.PolytopeEulerFour
open Papers.FaceIncidenceEuler
open scoped Classical BigOperators

variable {n : ℕ}

local instance faceFintype (P : ConvexPolytope n) (k : ℕ) : Fintype (Face P k) :=
  Fintype.ofFinite _

def graphNeighborEquiv (P : ConvexPolytope n) (v : P.vertices) :
    (vertexGraph P).neighborSet v ≃
      Papers.PolytopeVertexCone.actualNeighbors P v.val where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨w.val.property,w.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).1⟩,
    (Finset.mem_filter.mp w.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_eq_actual_neighbors (P : ConvexPolytope n) (v : P.vertices) :
    (vertexGraph P).degree v =
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (graphNeighborEquiv P v)).trans (Fintype.card_coe _)

theorem degree_ge_dim (P : ConvexPolytope n) (v : P.vertices) :
    P.dim ≤ (vertexGraph P).degree v := by
  rw [degree_eq_actual_neighbors]
  exact actual_neighbor_card_ge_dim P v.property

theorem vertices_card_ge_dim_add_one (P : ConvexPolytope n) :
    P.dim + 1 ≤ P.vertices.card := by
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  have hcard := actual_neighbor_card_ge_dim P hv
  have hsub : Papers.PolytopeVertexCone.actualNeighbors P v ⊂ P.vertices := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
    intro heq
    have hvN : v ∈ Papers.PolytopeVertexCone.actualNeighbors P v := by
      rw [heq]
      exact hv
    exact (Finset.mem_filter.mp hvN).2.2.1 rfl
  have hlt := Finset.card_lt_card hsub
  omega

theorem face_vertices_card_ge_dim_add_one
    (P : ConvexPolytope n) (k : ℕ) (F : Face P k) :
    k + 1 ≤ Nat.card (VerticesOn P F.val.carrier) := by
  let Q := facePolytope P F.val.isFace
  have hd : Q.dim = k := by
    change faceDim Q.toSet = k
    rw [facePolytope_toSet]
    exact F.property
  have hc := vertices_card_ge_dim_add_one Q
  rw [hd] at hc
  rw [Nat.card_congr (faceVerticesEquiv P F.val.isFace)]
  simpa using hc

theorem vertex_edge_bound (P : ConvexPolytope n) (hdim : P.dim = 3) :
    3 * P.vertices.card ≤ 2 * Nat.card (Face P 1) := by
  have hdeg : ∀ v : P.vertices, 3 ≤ (vertexGraph P).degree v := by
    intro v
    simpa only [hdim] using degree_ge_dim P v
  have hs : 3 * P.vertices.card ≤ ∑ v : P.vertices, (vertexGraph P).degree v := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
    simpa [mul_comm] using hh
  have hhand := (vertexGraph P).sum_degrees_eq_twice_card_edges
  have hcard : (vertexGraph P).edgeFinset.card = Nat.card (Face P 1) := by
    rw [← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card]
    exact graph_edge_card_eq_one_face_card P
  rw [hhand,hcard] at hs
  exact hs

theorem face_edge_sum (P : ConvexPolytope n) (hdim : P.dim = 3) :
    (∑ F : Face P 2, (Nat.card (FaceBelow P F.val.carrier 1) : ℤ)) =
      2 * Nat.card (Face P 1) := by
  letI : Fintype (Face P 1) := Fintype.ofFinite _
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  let inc : Face P 1 → Face P 2 → Prop :=
    fun e F => e.val.carrier ⊆ F.val.carrier
  have h := total_rows_eq_columns inc
  have hr : ∀ e, rowCount inc e = 2 := by
    intro e
    rw [rowCount_card]
    change (Nat.card (Coface P e.val.carrier 2) : ℤ) = 2
    rw [ridge_coface_card P 1 hdim e]
    norm_num
  have hc : ∀ F, colCount inc F =
      (Nat.card (FaceBelow P F.val.carrier 1) : ℤ) := fun F =>
    colCount_card inc F
  simp only [hr,hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  simpa only [Nat.card_eq_fintype_card,mul_comm] using h.symm

theorem face_edge_bound (P : ConvexPolytope n) (hdim : P.dim = 3) :
    3 * Nat.card (Face P 2) ≤ 2 * Nat.card (Face P 1) := by
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  have hmin : ∀ F : Face P 2,
      (3 : ℤ) ≤ Nat.card (FaceBelow P F.val.carrier 1) := by
    intro F
    have h := face_vertices_card_ge_dim_add_one P 2 F
    rw [two_face_vertices_eq_edges] at h
    exact_mod_cast h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun F _ => hmin F)
  rw [face_edge_sum P hdim] at hs
  have hh : (3 : ℤ) * Nat.card (Face P 2) ≤
      2 * Nat.card (Face P 1) := by
    simpa [Nat.card_eq_fintype_card,mul_comm] using hs
  exact_mod_cast hh

theorem three_dimensional_face_bound (P : ConvexPolytope n)
    (hdim : P.dim = 3) :
    Nat.card (Face P 2) ≤ 2 * P.vertices.card - 4 := by
  have he := euler_three P hdim
  have hi := face_edge_bound P hdim
  have hv := vertices_card_ge_dim_add_one P
  rw [hdim] at hv
  omega

/-- Every actual three-dimensional convex polytope with at most seven
vertices has a triangular facet. This justifies fixing a triangular root
before running the complete finite boundary search. -/
theorem exists_triangular_face_of_card_le_seven
    (P : ConvexPolytope n) (hdim : P.dim = 3) (hn : P.vertices.card ≤ 7) :
    ∃ F : Face P 2, Nat.card (VerticesOn P F.val.carrier) = 3 := by
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  by_contra hnone
  push_neg at hnone
  have hfour : ∀ F : Face P 2,
      (4 : ℤ) ≤ Nat.card (FaceBelow P F.val.carrier 1) := by
    intro F
    have hmin := face_vertices_card_ge_dim_add_one P 2 F
    have hne := hnone F
    have hc := two_face_vertices_eq_edges P F
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun F _ => hfour F)
  rw [face_edge_sum P hdim] at hs
  have hfaces : (4 : ℤ) * Nat.card (Face P 2) ≤
      2 * Nat.card (Face P 1) := by
    simpa [Nat.card_eq_fintype_card,mul_comm] using hs
  have hvertices := vertex_edge_bound P hdim
  have he := euler_three P hdim
  omega

end Papers.PolytopeSmallFacetBounds

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/PolytopePolygonCycle.lean -/





@[expose] public section

/-!
# Actual polygon boundaries are simple cyclic graphs

Connectedness and degree two imply the existence of a
Hamiltonian cycle whose edge set is the entire graph. Applying this to a
genuine two-dimensional face gives the cyclic boundary data required by
the finite polygon catalogue.
-/

noncomputable section

namespace Papers.PolytopePolygonCycle

open SimpleGraph
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeBalinski Papers.PolytopeEulerLocal
open Papers.FiniteGraphHeightCount
open Papers.RationalityTen.PolygonMorseGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_hamiltonian_cycle_of_degree_two
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsHamiltonianCycle := by
  have hnot : ¬ G.IsAcyclic := by
    intro hac
    have ht : G.IsTree := ⟨hconn,hac⟩
    have htree := ht.card_edgeFinset
    have htwo := two_regular_edge_card G hdeg
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at htwo
    rw [Nat.card_eq_fintype_card] at htwo
    omega
  simp only [SimpleGraph.IsAcyclic,not_forall,not_not] at hnot
  obtain ⟨v,c,hc⟩ := hnot
  refine ⟨v,c,?_⟩
  exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support.mpr
    ⟨hc,cycle_support_all G hconn (fun v => (hdeg v).le) c hc⟩

theorem hamiltonian_cycle_edges_eq
    (hdeg : ∀ v, G.degree v = 2)
    {v : V} (c : G.Walk v v) (hc : c.IsHamiltonianCycle) :
    c.edges.toFinset = G.edgeFinset := by
  have hsub : c.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    exact G.mem_edgeFinset.mpr
      (c.edges_subset_edgeSet (List.mem_toFinset.mp he))
  apply Finset.eq_of_subset_of_card_le hsub
  have hcycle : c.edges.toFinset.card = Fintype.card V := by
    rw [List.toFinset_card_of_nodup hc.isCycle.isTrail.edges_nodup,
      SimpleGraph.Walk.length_edges,hc.length_eq]
  have hgraph := two_regular_edge_card G hdeg
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at hgraph
  rw [Nat.card_eq_fintype_card] at hgraph
  omega

variable {n : ℕ}

/-- A genuine convex polygon has a cyclic listing of all actual vertices,
and the cycle uses precisely its actual edges. -/
theorem actual_polygon_cycle (P : ConvexPolytope n) (hdim : P.dim = 2) :
    ∃ (v : P.vertices) (c : (vertexGraph P).Walk v v),
      c.IsHamiltonianCycle ∧ c.edges.toFinset = (vertexGraph P).edgeFinset := by
  obtain ⟨v,c,hc⟩ := exists_hamiltonian_cycle_of_degree_two (vertexGraph P)
    (vertexGraph_connected P) (polygon_vertex_degree_two P hdim)
  exact ⟨v,c,hc,hamiltonian_cycle_edges_eq (vertexGraph P)
    (polygon_vertex_degree_two P hdim) c hc⟩

end Papers.PolytopePolygonCycle

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/PolytopeBoundaryIntersections.lean -/





@[expose] public section

/-!
# Actual intersections in a labelled polygon boundary

Two distinct genuine two-faces meet in at most one
vertex or in exactly a common genuine edge. This is the geometric
compatibility condition used by the finite boundary catalogue.
-/

noncomputable section

namespace Papers.PolytopeBoundaryIntersections

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.Polytopes
open scoped Classical

variable {n : ℕ}

theorem two_face_intersection
    (P : ConvexPolytope n) (A B : Face P 2) (hne : A ≠ B) :
    (faceCode P 2 A ∩ faceCode P 2 B).card ≤ 1 ∨
      ∃ e : Face P 1,
        e.val.carrier ⊆ A.val.carrier ∧
        e.val.carrier ⊆ B.val.carrier ∧
        faceCode P 2 A ∩ faceCode P 2 B = faceCode P 1 e := by
  by_cases hsmall : (faceCode P 2 A ∩ faceCode P 2 B).card ≤ 1
  · exact Or.inl hsmall
  right
  have hnonempty : (faceCode P 2 A ∩ faceCode P 2 B).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v,hv⟩ := hnonempty
  have hvAB : v.val ∈ A.val.carrier ∩ B.val.carrier := by
    simpa [faceCode] using hv
  have hI : P.IsFace (A.val.carrier ∩ B.val.carrier) :=
    ⟨A.val.isFace.1.inter B.val.isFace.1,⟨v.val,hvAB⟩⟩
  have hproper : A.val.carrier ∩ B.val.carrier ⊂ A.val.carrier := by
    refine ⟨Set.inter_subset_left,?_⟩
    intro hback
    have hAB : A.val.carrier ⊆ B.val.carrier := fun x hx => (hback hx).2
    have hABproper : A.val.carrier ⊂ B.val.carrier := by
      refine ⟨hAB,?_⟩
      intro hBA
      apply hne
      apply Subtype.ext
      exact PolytopeFace.ext (Set.Subset.antisymm hAB hBA)
    have hlt := faceDim_lt_of_ssubset P A.val.isFace B.val.isFace hABproper
    rw [A.property,B.property] at hlt
    omega
  have hlt := faceDim_lt_of_ssubset P hI A.val.isFace hproper
  rw [A.property] at hlt
  have hnotzero : faceDim (A.val.carrier ∩ B.val.carrier) ≠ 0 := by
    intro hzero
    obtain ⟨x,hx,hIx⟩ := actual_zeroFace_is_vertex P
      (A.val.carrier ∩ B.val.carrier) hI hzero
    let xx : P.vertices := ⟨x,hx⟩
    have hsub : faceCode P 2 A ∩ faceCode P 2 B ⊆ {xx} := by
      intro w hw
      have hwI : w.val ∈ A.val.carrier ∩ B.val.carrier := by
        simpa [faceCode] using hw
      rw [hIx] at hwI
      have hweq : w = xx := Subtype.ext (Set.mem_singleton_iff.mp hwI)
      simp only [Finset.mem_singleton]
      exact hweq
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    exact hsmall hc
  have hdim : faceDim (A.val.carrier ∩ B.val.carrier) = 1 := by omega
  refine ⟨⟨⟨A.val.carrier ∩ B.val.carrier,hI⟩,hdim⟩,
    Set.inter_subset_left,Set.inter_subset_right,?_⟩
  ext w
  simp [faceCode]

end Papers.PolytopeBoundaryIntersections

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/PolytopeNonedgeAllocation.lean -/





@[expose] public section

/-!
# Actual nonedges and their facet allocation

A nonedge is an actual pair of distinct extreme
vertices not joined by a one-face. Such a pair belongs to at most one
two-face and to at most two facets of a four-polytope. It belongs to two
facets exactly when it is a polygon diagonal.

The allocated facet weights are defined on these actual pairs. Their
total is bounded by the actual number of nonedges; no incidence
multiplicity hypothesis is added to the polytope input.
-/

noncomputable section

namespace Papers.PolytopeNonedgeAllocation

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def CommonFacets (P : ConvexPolytope d) (x y : P.vertices) :
    Finset (Face P 3) :=
  Finset.univ.filter fun F => x.val ∈ F.val.carrier ∧ y.val ∈ F.val.carrier

def IsPolygonDiagonal (P : ConvexPolytope d) (x y : P.vertices) : Prop :=
  ∃ R : Face P 2, x.val ∈ R.val.carrier ∧ y.val ∈ R.val.carrier

theorem face_eq_of_subset_equal_dimension (P : ConvexPolytope d)
    {A B : Set (E d)} (hA : P.IsFace A) (hB : P.IsFace B)
    (hAB : A ⊆ B) (hdim : faceDim A = faceDim B) : A = B := by
  by_contra hne
  have hp : A ⊂ B := hAB.ssubset_of_ne hne
  have hlt := faceDim_lt_of_ssubset P hA hB hp
  omega

theorem nonedge_face_dimension (P : ConvexPolytope d) (x y : P.vertices)
    (hne : x ≠ y) (hnon : ¬ GeneralVertexStep P x.val y.val)
    {F : Set (E d)} (hF : P.IsFace F)
    (hx : x.val ∈ F) (hy : y.val ∈ F) : 2 ≤ faceDim F := by
  by_contra h
  have hdim : faceDim F = 0 ∨ faceDim F = 1 := by omega
  rcases hdim with hzero | hone
  · obtain ⟨v,hv,hFv⟩ := actual_zeroFace_is_vertex P F hF hzero
    rw [hFv] at hx hy
    exact hne (Subtype.ext ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm))
  · apply hnon
    exact ⟨y.property,fun hxy => hne (Subtype.ext hxy),F,hF,hone,hx,hy⟩

theorem polygon_diagonal_unique (P : ConvexPolytope d)
    (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val)
    (R S : Face P 2) (hxR : x.val ∈ R.val.carrier)
    (hyR : y.val ∈ R.val.carrier) (hxS : x.val ∈ S.val.carrier)
    (hyS : y.val ∈ S.val.carrier) : R = S := by
  have hI : P.IsFace (R.val.carrier ∩ S.val.carrier) :=
    ⟨R.val.isFace.1.inter S.val.isFace.1,⟨x.val,hxR,hxS⟩⟩
  have hlo := nonedge_face_dimension P x y hne hnon hI ⟨hxR,hxS⟩ ⟨hyR,hyS⟩
  have hIR : R.val.carrier ∩ S.val.carrier = R.val.carrier := by
    by_contra hneI
    have hlt := faceDim_lt_of_ssubset P hI R.val.isFace
      (Set.inter_subset_left.ssubset_of_ne hneI)
    rw [R.property] at hlt
    omega
  have hRS : R.val.carrier ⊆ S.val.carrier := by
    intro v hv
    exact (hIR.symm ▸ hv).2
  apply Subtype.ext
  apply PolytopeFace.ext
  exact face_eq_of_subset_equal_dimension P R.val.isFace S.val.isFace hRS
    (R.property.trans S.property.symm)

theorem diagonal_face_subset (P : ConvexPolytope d)
    (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val)
    (R : Face P 2) (hxR : x.val ∈ R.val.carrier) (hyR : y.val ∈ R.val.carrier)
    {F : Set (E d)} (hF : P.IsFace F) (hxF : x.val ∈ F) (hyF : y.val ∈ F) :
    R.val.carrier ⊆ F := by
  have hI : P.IsFace (R.val.carrier ∩ F) :=
    ⟨R.val.isFace.1.inter hF.1,⟨x.val,hxR,hxF⟩⟩
  have hlo := nonedge_face_dimension P x y hne hnon hI ⟨hxR,hxF⟩ ⟨hyR,hyF⟩
  have hIR : R.val.carrier ∩ F = R.val.carrier := by
    by_contra hneI
    have hlt := faceDim_lt_of_ssubset P hI R.val.isFace
      (Set.inter_subset_left.ssubset_of_ne hneI)
    rw [R.property] at hlt
    omega
  intro z hz
  exact (hIR.symm ▸ hz).2

theorem distinct_common_facets_intersection (P : ConvexPolytope d)
    (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val)
    (A B : Face P 3) (hAB : A ≠ B)
    (hxA : x.val ∈ A.val.carrier) (hyA : y.val ∈ A.val.carrier)
    (hxB : x.val ∈ B.val.carrier) (hyB : y.val ∈ B.val.carrier) :
    ∃ R : Face P 2, R.val.carrier = A.val.carrier ∩ B.val.carrier := by
  have hI : P.IsFace (A.val.carrier ∩ B.val.carrier) :=
    ⟨A.val.isFace.1.inter B.val.isFace.1,⟨x.val,hxA,hxB⟩⟩
  have hlo := nonedge_face_dimension P x y hne hnon hI ⟨hxA,hxB⟩ ⟨hyA,hyB⟩
  have hproper : A.val.carrier ∩ B.val.carrier ⊂ A.val.carrier := by
    refine ⟨Set.inter_subset_left,?_⟩
    intro hback
    have hsub : A.val.carrier ⊆ B.val.carrier := fun z hz => (hback hz).2
    have heq := face_eq_of_subset_equal_dimension P A.val.isFace B.val.isFace
      hsub (A.property.trans B.property.symm)
    exact hAB (Subtype.ext (PolytopeFace.ext heq))
  have hhi := faceDim_lt_of_ssubset P hI A.val.isFace hproper
  rw [A.property] at hhi
  have hd : faceDim (A.val.carrier ∩ B.val.carrier) = 2 := by omega
  exact ⟨⟨⟨_,hI⟩,hd⟩,rfl⟩

theorem diagonal_common_facets_card (P : ConvexPolytope d)
    (hdim : P.dim = 4) (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val)
    (hdiag : IsPolygonDiagonal P x y) : (CommonFacets P x y).card = 2 := by
  obtain ⟨R,hxR,hyR⟩ := hdiag
  have heq : CommonFacets P x y =
      Finset.univ.filter fun F : Face P 3 => R.val.carrier ⊆ F.val.carrier := by
    ext F
    simp only [CommonFacets,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hxF,hyF⟩
      exact diagonal_face_subset P x y hne hnon R hxR hyR F.val.isFace hxF hyF
    · intro hRF
      exact ⟨hRF hxR,hRF hyR⟩
  rw [heq]
  have h := ridge_coface_card P 2 hdim R
  simpa only [Coface,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

theorem two_common_facets_iff_diagonal (P : ConvexPolytope d)
    (hdim : P.dim = 4) (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val) :
    (CommonFacets P x y).card = 2 ↔ IsPolygonDiagonal P x y := by
  constructor
  · intro htwo
    obtain ⟨A,hA,B,hB,hAB⟩ := Finset.one_lt_card.mp (show 1 < (CommonFacets P x y).card by omega)
    obtain ⟨hxA,hyA⟩ := (Finset.mem_filter.mp hA).2
    obtain ⟨hxB,hyB⟩ := (Finset.mem_filter.mp hB).2
    obtain ⟨R,hR⟩ := distinct_common_facets_intersection P x y hne hnon
      A B hAB hxA hyA hxB hyB
    exact ⟨R,by simpa only [hR,Set.mem_inter_iff] using And.intro hxA hxB,
      by simpa only [hR,Set.mem_inter_iff] using And.intro hyA hyB⟩
  · exact diagonal_common_facets_card P hdim x y hne hnon

theorem nonedge_common_facets_le_two (P : ConvexPolytope d)
    (hdim : P.dim = 4) (x y : P.vertices) (hne : x ≠ y)
    (hnon : ¬ GeneralVertexStep P x.val y.val) :
    (CommonFacets P x y).card ≤ 2 := by
  by_cases hsmall : (CommonFacets P x y).card ≤ 1
  · omega
  obtain ⟨A,hA,B,hB,hAB⟩ := Finset.one_lt_card.mp
    (show 1 < (CommonFacets P x y).card by omega)
  obtain ⟨hxA,hyA⟩ := (Finset.mem_filter.mp hA).2
  obtain ⟨hxB,hyB⟩ := (Finset.mem_filter.mp hB).2
  obtain ⟨R,hR⟩ := distinct_common_facets_intersection P x y hne hnon
    A B hAB hxA hyA hxB hyB
  have hd : IsPolygonDiagonal P x y := ⟨R,
    by simpa only [hR,Set.mem_inter_iff] using And.intro hxA hxB,
    by simpa only [hR,Set.mem_inter_iff] using And.intro hyA hyB⟩
  exact le_of_eq (diagonal_common_facets_card P hdim x y hne hnon hd)

abbrev Nonedge (P : ConvexPolytope d) := (vertexGraph P)ᶜ.edgeSet

theorem nonedge_out (P : ConvexPolytope d) (e : Nonedge P) :
    e.val.out.1 ≠ e.val.out.2 ∧
      ¬ GeneralVertexStep P e.val.out.1.val e.val.out.2.val := by
  have h : (vertexGraph P)ᶜ.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1,e.val.out.2) ∈ (vertexGraph P)ᶜ.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  exact (SimpleGraph.compl_adj _ _ _).mp h


theorem nonedge_card_add_edge_card (P : ConvexPolytope d) :
    Nat.card (Nonedge P) + Nat.card (Face P 1) = P.vertices.card.choose 2 := by
  let G := vertexGraph P
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have he := graph_edge_card_eq_one_face_card P
  calc
    Nat.card (Nonedge P) + Nat.card (Face P 1) =
        Gᶜ.edgeFinset.card + G.edgeFinset.card := by
      rw [← he]
      simp only [Nonedge,G,Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet]
    _ = (G.edgeFinset ∪ Gᶜ.edgeFinset).card := by
      rw [Finset.card_union_of_disjoint hd]
      omega
    _ = (Fintype.card P.vertices).choose 2 := by
      have hs : G.edgeFinset ∪ Gᶜ.edgeFinset =
          (⊤ : SimpleGraph P.vertices).edgeFinset := by
        ext e
        simp only [Finset.mem_union,SimpleGraph.mem_edgeFinset]
        change e ∈ G.edgeSet ∪ Gᶜ.edgeSet ↔ e ∈ (⊤ : SimpleGraph P.vertices).edgeSet
        rw [← SimpleGraph.edgeSet_sup,sup_compl_eq_top]
      rw [hs]
      exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = P.vertices.card.choose 2 := by rw [Fintype.card_coe]

theorem nonedge_card_eq (P : ConvexPolytope d) :
    Nat.card (Nonedge P) = P.vertices.card.choose 2 - Nat.card (Face P 1) := by
  have h := nonedge_card_add_edge_card P
  omega

def pairFacetWeight (P : ConvexPolytope d) (e : Nonedge P)
    (F : Face P 3) : ℚ :=
  if F ∈ CommonFacets P e.val.out.1 e.val.out.2 then
    if IsPolygonDiagonal P e.val.out.1 e.val.out.2 then 1/2 else 1
  else 0

def allocatedFacetWeight (P : ConvexPolytope d) (F : Face P 3) : ℚ :=
  ∑ e : Nonedge P, pairFacetWeight P e F

theorem pairFacetWeight_sum (P : ConvexPolytope d) (e : Nonedge P) :
    (∑ F : Face P 3, pairFacetWeight P e F) =
      (CommonFacets P e.val.out.1 e.val.out.2).card *
        (if IsPolygonDiagonal P e.val.out.1 e.val.out.2 then (1/2 : ℚ) else 1) := by
  unfold pairFacetWeight
  have hc : (Finset.univ : Finset (Face P 3)).filter
      (fun F => F ∈ CommonFacets P e.val.out.1 e.val.out.2) =
      CommonFacets P e.val.out.1 e.val.out.2 := by
    ext F
    simp
  rw [← Finset.sum_filter,hc]
  simp only [Finset.sum_const,nsmul_eq_mul]

theorem pairFacetWeight_sum_le_one (P : ConvexPolytope d)
    (hdim : P.dim = 4) (e : Nonedge P) :
    (∑ F : Face P 3, pairFacetWeight P e F) ≤ 1 := by
  rw [pairFacetWeight_sum]
  obtain ⟨hne,hnon⟩ := nonedge_out P e
  by_cases hdiag : IsPolygonDiagonal P e.val.out.1 e.val.out.2
  · rw [if_pos hdiag,diagonal_common_facets_card P hdim _ _ hne hnon hdiag]
    norm_num
  · rw [if_neg hdiag,mul_one]
    have hle := nonedge_common_facets_le_two P hdim _ _ hne hnon
    have hne2 : (CommonFacets P e.val.out.1 e.val.out.2).card ≠ 2 := by
      intro htwo
      exact hdiag ((two_common_facets_iff_diagonal P hdim _ _ hne hnon).mp htwo)
    have hle1 : (CommonFacets P e.val.out.1 e.val.out.2).card ≤ 1 := by omega
    exact_mod_cast hle1

theorem allocated_weights_le_nonedge_card (P : ConvexPolytope d)
    (hdim : P.dim = 4) :
    (∑ F : Face P 3, allocatedFacetWeight P F) ≤ Nat.card (Nonedge P) := by
  unfold allocatedFacetWeight
  rw [Finset.sum_comm]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => pairFacetWeight_sum_le_one P hdim e)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Nat.card_eq_fintype_card] using h

end Papers.PolytopeNonedgeAllocation

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/PolytopeFaceGraph.lean -/



@[expose] public section
noncomputable section
namespace Papers.PolytopeLabelledBoundary
open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerLowerFaces Papers.PolytopeBoundaryIntersections
open scoped Classical
variable {d : ℕ}

def faceVertexInclusion (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : (facePolytope P hF).vertices ↪ P.vertices where
  toFun q := ⟨q.val,(Finset.mem_filter.mp q.property).1⟩
  inj' q r h := by
    apply Subtype.ext
    exact congrArg (fun z : P.vertices => z.val) h

theorem originalStep_to_facePolytope (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F)
    (x y : (facePolytope P hF).vertices)
    (hxy : GeneralVertexStep P x.val y.val) :
    GeneralVertexStep (facePolytope P hF) x.val y.val := by
  have hxP := (Finset.mem_filter.mp x.property).1
  have hxF := (Finset.mem_filter.mp x.property).2
  have hyF := (Finset.mem_filter.mp y.property).2
  have hs := segment_isFace_of_generalVertexStep P hxP hxy
  have hd := segment_faceDim_of_generalVertexStep P hxP hxy
  have hconv : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hsub : segment ℝ x.val y.val ⊆ F := hconv.segment_subset hxF hyF
  exact ⟨y.property,hxy.2.1,segment ℝ x.val y.val,
    facePolytope_isFace_of P hF hs hsub,hd,
    left_mem_segment ℝ _ _,right_mem_segment ℝ _ _⟩

end Papers.PolytopeLabelledBoundary

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/PolytopeFaceNonedges.lean -/





@[expose] public section

/-!
# Nonedge counts inside genuine faces

The complement graph of a face polytope embeds in the
complement graph of the original polytope, and its edges are exactly the
original nonedges whose endpoints lie on the face. This identifies the
allocated weights with genuine local combinatorial counts.
-/

noncomputable section

namespace Papers.PolytopeFaceNonedges

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeLabelledBoundary Papers.PolytopeEulerLowerFaces
open Papers.PolytopeNonedgeAllocation Papers.PolytopeBalinski
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def faceNonedgeEmbedding (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) :
    (vertexGraph (facePolytope P hF))ᶜ ↪g (vertexGraph P)ᶜ where
  toEmbedding := faceVertexInclusion P hF
  map_rel_iff' := by
    intro x y
    rw [SimpleGraph.compl_adj,SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hne,hnon⟩
      refine ⟨fun h => hne (congrArg (faceVertexInclusion P hF) h),?_⟩
      intro hxy
      exact hnon (step_facePolytope_to_original P hF hxy)
    · rintro ⟨hne,hnon⟩
      refine ⟨fun h => hne ((faceVertexInclusion P hF).injective h),?_⟩
      intro hxy
      exact hnon (originalStep_to_facePolytope P hF x y hxy)

def Within (P : ConvexPolytope d) (F : Set (E d)) (e : Nonedge P) : Prop :=
  e.val.out.1.val ∈ F ∧ e.val.out.2.val ∈ F

abbrev NonedgesOn (P : ConvexPolytope d) (F : Set (E d)) :=
  {e : Nonedge P // Within P F e}

def DiagonalOn (P : ConvexPolytope d) (F : Set (E d)) (e : Nonedge P) : Prop :=
  Within P F e ∧ IsPolygonDiagonal P e.val.out.1 e.val.out.2

abbrev DiagonalsOn (P : ConvexPolytope d) (F : Set (E d)) :=
  {e : Nonedge P // DiagonalOn P F e}

theorem within_iff (P : ConvexPolytope d) (F : Set (E d)) (e : Nonedge P) :
    Within P F e ↔ ∀ v ∈ e.val, v.val ∈ F := by
  constructor
  · rintro ⟨hx,hy⟩ v hv
    rw [← Sym2.mk_fst_out_snd_out e.val,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl <;> assumption
  · intro h
    exact ⟨h _ (Sym2.out_fst_mem _),h _ (Sym2.out_snd_mem _)⟩

def liftFaceNonedge (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) (e : Nonedge (facePolytope P hF)) : NonedgesOn P F :=
  ⟨(faceNonedgeEmbedding P hF).mapEdgeSet e,by
    apply (within_iff P F _).mpr
    intro v hv
    change v ∈ Sym2.map (faceVertexInclusion P hF) e.val at hv
    obtain ⟨w,hw,hwv⟩ := Sym2.mem_map.mp hv
    rw [← hwv]
    exact (Finset.mem_filter.mp w.property).2⟩

theorem liftFaceNonedge_injective (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : Function.Injective (liftFaceNonedge P hF) := by
  intro e f h
  apply (faceNonedgeEmbedding P hF).mapEdgeSet.injective
  exact congrArg Subtype.val h

theorem liftFaceNonedge_surjective (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : Function.Surjective (liftFaceNonedge P hF) := by
  intro e
  let x : (facePolytope P hF).vertices :=
    ⟨e.val.val.out.1.val,Finset.mem_filter.mpr
      ⟨e.val.val.out.1.property,e.property.1⟩⟩
  let y : (facePolytope P hF).vertices :=
    ⟨e.val.val.out.2.val,Finset.mem_filter.mpr
      ⟨e.val.val.out.2.property,e.property.2⟩⟩
  obtain ⟨hne,hnon⟩ := nonedge_out P e.val
  have hxy : (vertexGraph (facePolytope P hF))ᶜ.Adj x y := by
    rw [SimpleGraph.compl_adj]
    refine ⟨?_,?_⟩
    · intro h
      apply hne
      apply Subtype.ext
      exact congrArg (fun z : (facePolytope P hF).vertices => z.val) h
    · intro h
      exact hnon (step_facePolytope_to_original P hF h)
  let f : Nonedge (facePolytope P hF) := ⟨s(x,y),hxy⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Sym2.map (faceVertexInclusion P hF) s(x,y) = e.val.val
  rw [Sym2.map_mk]
  exact Sym2.mk_fst_out_snd_out e.val.val

def faceNonedgeEquiv (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : Nonedge (facePolytope P hF) ≃ NonedgesOn P F :=
  Equiv.ofBijective (liftFaceNonedge P hF)
    ⟨liftFaceNonedge_injective P hF,liftFaceNonedge_surjective P hF⟩

theorem face_nonedge_count (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) :
    Nat.card (NonedgesOn P F) + Nat.card (FaceBelow P F 1) =
      (Nat.card (VerticesOn P F)).choose 2 := by
  let Q := facePolytope P hF
  have hn := Nat.card_congr (faceNonedgeEquiv P hF)
  have he := Nat.card_congr (faceBelowEquiv P hF 1)
  have hv := Nat.card_congr (faceVerticesEquiv P hF)
  have h := nonedge_card_add_edge_card Q
  rw [hn,← he] at h
  have hq : Q.vertices.card = Nat.card (VerticesOn P F) := by
    rw [hv]
    simp [Q]
  rw [hq] at h
  exact h

theorem sum_indicator_card {α : Type*} [Fintype α] (p : α → Prop) :
    (∑ x : α, if p x then (1 : ℚ) else 0) = Nat.card {x : α // p x} := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem facet_weight_count (P : ConvexPolytope d) (F : Face P 3) :
    allocatedFacetWeight P F =
      (Nat.card (NonedgesOn P F.val.carrier) : ℚ) -
        (1/2 : ℚ) * Nat.card (DiagonalsOn P F.val.carrier) := by
  have hpoint (e : Nonedge P) : pairFacetWeight P e F =
      (if Within P F.val.carrier e then (1 : ℚ) else 0) -
        (1/2 : ℚ) * (if DiagonalOn P F.val.carrier e then 1 else 0) := by
    simp only [pairFacetWeight,CommonFacets,Finset.mem_filter,
      Finset.mem_univ,true_and]
    unfold Within DiagonalOn
    by_cases hw : e.val.out.1.val ∈ F.val.carrier ∧ e.val.out.2.val ∈ F.val.carrier <;>
      by_cases hd : IsPolygonDiagonal P e.val.out.1 e.val.out.2 <;>
      simp [hw,hd,Within] <;> norm_num
  unfold allocatedFacetWeight
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,sum_indicator_card,sum_indicator_card]

theorem polygon_nonedge_count (P : ConvexPolytope d) (R : Face P 2) :
    Nat.card (NonedgesOn P R.val.carrier) +
        Nat.card (VerticesOn P R.val.carrier) =
      (Nat.card (VerticesOn P R.val.carrier)).choose 2 := by
  have h := face_nonedge_count P R.val.isFace
  rw [← two_face_vertices_eq_edges] at h
  exact h

end Papers.PolytopeFaceNonedges

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/PolytopeRelationBudget.lean -/








@[expose] public section

/-!
# The actual Euler and polygon-diagonal budget

These are the first two identities/inequalities of
Section 5.2 on genuine polytopes. Counts use all actual exposed faces and
actual nonedges. The rank-based surplus and selected-row count are
separate additions; they are not assumed proved here.
-/

noncomputable section

namespace Papers.PolytopeRelationBudget

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerFour Papers.PolytopeSmallFacetBounds
open Papers.PolytopeNonedgeAllocation Papers.PolytopeFaceNonedges
open Papers.FaceIncidenceEuler
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def facetExcess (P : ConvexPolytope d) : ℤ :=
  ∑ F : Face P 3, ((Nat.card (VerticesOn P F.val.carrier) : ℤ) - 4)

def polygonExcess (P : ConvexPolytope d) : ℤ :=
  ∑ R : Face P 2, ((Nat.card (VerticesOn P R.val.carrier) : ℤ) - 3)

theorem facetExcess_nonnegative (P : ConvexPolytope d) : 0 ≤ facetExcess P := by
  apply Finset.sum_nonneg
  intro F hF
  have h :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  omega

theorem polygonExcess_nonnegative (P : ConvexPolytope d) : 0 ≤ polygonExcess P := by
  apply Finset.sum_nonneg
  intro R hR
  have h := face_vertices_card_ge_dim_add_one P 2 R
  omega

theorem sum_vertex_incident_faces (P : ConvexPolytope d) (k : ℕ) :
    (∑ v : P.vertices, (Nat.card (IncidentFace P v.val k) : ℤ)) =
      ∑ F : Face P k, (Nat.card (VerticesOn P F.val.carrier) : ℤ) := by
  let inc : P.vertices → Face P k → Prop := fun v F => v.val ∈ F.val.carrier
  have h := total_rows_eq_columns inc
  simpa only [rowCount_card,colCount_card,inc,IncidentFace,VerticesOn] using h

theorem sum_one_face_vertices (P : ConvexPolytope d) :
    (∑ e : Face P 1, (Nat.card (VerticesOn P e.val.carrier) : ℤ)) =
      2 * Nat.card (Face P 1) := by
  simp_rw [one_face_vertex_card]
  simp [mul_comm]

theorem vertex_figure_incidence_budget (P : ConvexPolytope d)
    (hdim : P.dim = 4) :
    (∑ F : Face P 3, (Nat.card (VerticesOn P F.val.carrier) : ℤ)) -
      (∑ R : Face P 2, (Nat.card (VerticesOn P R.val.carrier) : ℤ)) =
      2 * P.vertices.card - 2 * Nat.card (Face P 1) := by
  have hs :
      (∑ v : P.vertices, (Nat.card (IncidentFace P v.val 1) : ℤ)) -
        (∑ v : P.vertices, (Nat.card (IncidentFace P v.val 2) : ℤ)) +
        (∑ v : P.vertices, (Nat.card (IncidentFace P v.val 3) : ℤ)) =
        2 * P.vertices.card := by
    calc
      _ = ∑ v : P.vertices,
          ((Nat.card (IncidentFace P v.val 1) : ℤ) -
            Nat.card (IncidentFace P v.val 2) +
            Nat.card (IncidentFace P v.val 3)) := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
      _ = ∑ _v : P.vertices, (2 : ℤ) :=
        Finset.sum_congr rfl (fun v _ => vertex_local_euler P hdim v)
      _ = _ := by simp [mul_comm]
  rw [sum_vertex_incident_faces,sum_vertex_incident_faces,
    sum_vertex_incident_faces,sum_one_face_vertices] at hs
  omega

theorem actual_excess_identity (P : ConvexPolytope d) (hdim : P.dim = 4) :
    facetExcess P =
      (P.vertices.card.choose 2 : ℤ) - P.vertices.card -
        Nat.card (Face P 3) - Nat.card (Nonedge P) + polygonExcess P := by
  have hlocal := vertex_figure_incidence_budget P hdim
  have heuler := euler_four P hdim
  have hn := nonedge_card_add_edge_card P
  have hnz : (Nat.card (Nonedge P) : ℤ) + Nat.card (Face P 1) =
      P.vertices.card.choose 2 := by exact_mod_cast hn
  unfold facetExcess polygonExcess
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  omega

theorem sum_polygon_nonedge_counts (P : ConvexPolytope d) :
    (∑ R : Face P 2, (Nat.card (NonedgesOn P R.val.carrier) : ℤ)) ≤
      Nat.card (Nonedge P) := by
  let inc : Nonedge P → Face P 2 → Prop := fun e R => Within P R.val.carrier e
  have hrow : ∀ e : Nonedge P, rowCount inc e ≤ 1 := by
    intro e
    rw [rowCount_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
    have hc : (Finset.univ.filter fun R : Face P 2 => inc e R).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro R hR S hS
      obtain ⟨hne,hnon⟩ := nonedge_out P e
      have hr := (Finset.mem_filter.mp hR).2
      have hs := (Finset.mem_filter.mp hS).2
      exact polygon_diagonal_unique P _ _ hne hnon R S hr.1 hr.2 hs.1 hs.2
    exact_mod_cast hc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hrow e)
  rw [total_rows_eq_columns] at hs
  simp only [colCount_card,inc,NonedgesOn,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,← Nat.card_eq_fintype_card] at hs
  exact hs

theorem choose_two_ge_three_mul_sub_six (r : ℕ) (hr : 3 ≤ r) :
    (3 : ℤ) * r - 6 ≤ r.choose 2 := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hrec : (k+1).choose 2 = k.choose 2 + k := by
        simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ k 1
      rw [hrec]
      push_cast
      omega

theorem polygon_diagonal_excess_bound (P : ConvexPolytope d) (R : Face P 2) :
    2 * ((Nat.card (VerticesOn P R.val.carrier) : ℤ) - 3) ≤
      Nat.card (NonedgesOn P R.val.carrier) := by
  have hr := face_vertices_card_ge_dim_add_one P 2 R
  have hchoose := choose_two_ge_three_mul_sub_six _ hr
  have hcount := polygon_nonedge_count P R
  have hcountz :
      (Nat.card (NonedgesOn P R.val.carrier) : ℤ) +
        Nat.card (VerticesOn P R.val.carrier) =
        (Nat.card (VerticesOn P R.val.carrier)).choose 2 := by exact_mod_cast hcount
  omega

theorem two_polygon_excess_le_nonedge_count (P : ConvexPolytope d) :
    2 * polygonExcess P ≤ Nat.card (Nonedge P) := by
  have hlocal := Finset.sum_le_sum (s := Finset.univ)
    (fun R _ => polygon_diagonal_excess_bound P R)
  rw [← Finset.mul_sum] at hlocal
  exact hlocal.trans (sum_polygon_nonedge_counts P)


theorem polygon_excess_of_dimension_three (P : ConvexPolytope d)
    (hdim : P.dim = 3) :
    polygonExcess P = 3 * P.vertices.card - Nat.card (Face P 1) - 6 := by
  have hcorners :
      (∑ R : Face P 2, (Nat.card (VerticesOn P R.val.carrier) : ℤ)) =
        2 * Nat.card (Face P 1) := by
    calc
      _ = ∑ R : Face P 2, (Nat.card (FaceBelow P R.val.carrier 1) : ℤ) := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [two_face_vertices_eq_edges]
      _ = _ := face_edge_sum P hdim
  have he := Papers.PolytopeEulerThree.euler_three P hdim
  unfold polygonExcess
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  omega

theorem twice_choose_two (r : ℕ) :
    2 * (r.choose 2 : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hrec : (r+1).choose 2 = r.choose 2 + r := by
        simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ r 1
      rw [hrec]
      push_cast
      nlinarith only [ih]

theorem ten_vertex_excess_identity (P : ConvexPolytope d)
    (hdim : P.dim = 4) (hn : P.vertices.card = 10) :
    facetExcess P =
      35 - Nat.card (Face P 3) - Nat.card (Nonedge P) + polygonExcess P := by
  have h := actual_excess_identity P hdim
  rw [hn] at h
  norm_num only [show Nat.choose 10 2 = 45 by decide,Nat.cast_ofNat] at h
  exact h

end Papers.PolytopeRelationBudget

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/PolytopeFacetSurplus.lean -/




@[expose] public section

/-!
# The geometric weight formula and local rank surplus

The weight identity and upper bound on polygon
diagonals are unconditional facts about actual facets. The last
nonnegativity theorem exposes precisely the two rank-zero/rank-one
relation-space facts still needed from the shared-polygon relation
construction; it does not treat them as established geometry.
-/

noncomputable section

namespace Papers.PolytopeFacetSurplus

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation Papers.PolytopeRelationBudget
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def facetVertexCount (P : ConvexPolytope d) (F : Face P 3) : ℕ :=
  Nat.card (VerticesOn P F.val.carrier)

def facetDiagonalCount (P : ConvexPolytope d) (F : Face P 3) : ℕ :=
  Nat.card (DiagonalsOn P F.val.carrier)

def facetPolygonExcess (P : ConvexPolytope d) (F : Face P 3) : ℤ :=
  polygonExcess (facePolytope P F.val.isFace)

def rankSurplus (P : ConvexPolytope d) (F : Face P 3) (h : ℕ) : ℚ :=
  ((facetVertexCount P F : ℚ) - 4) * ((facetVertexCount P F : ℚ) - 5) / 2 +
    h - (facetDiagonalCount P F : ℚ) / 2

theorem facet_polygon_excess_formula (P : ConvexPolytope d) (F : Face P 3) :
    facetPolygonExcess P F =
      3 * facetVertexCount P F - Nat.card (FaceBelow P F.val.carrier 1) - 6 := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have h := polygon_excess_of_dimension_three Q hQ
  have hv := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
  have he := Nat.card_congr (faceBelowEquiv P F.val.isFace 1)
  have hvc : Q.vertices.card = facetVertexCount P F := by
    unfold facetVertexCount
    rw [hv]
    simp [Q]
  rw [hvc,← he] at h
  exact h

theorem facet_diagonal_bound (P : ConvexPolytope d) (F : Face P 3) :
    2 * (facetDiagonalCount P F : ℤ) ≤
      (facetVertexCount P F : ℤ) * ((facetVertexCount P F : ℤ) - 4) := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  let forget : DiagonalsOn P F.val.carrier → NonedgesOn P F.val.carrier :=
    fun e => ⟨e.val,e.property.1⟩
  have hforget : Function.Injective forget := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun z : NonedgesOn P F.val.carrier => z.val) hef
  have hd : facetDiagonalCount P F ≤ Nat.card (NonedgesOn P F.val.carrier) := by
    have h := Fintype.card_le_of_injective forget hforget
    simpa only [facetDiagonalCount,Nat.card_eq_fintype_card] using h
  have hc := face_nonedge_count P F.val.isFace
  have hdegree := vertex_edge_bound Q hQ
  have hv := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
  have he := Nat.card_congr (faceBelowEquiv P F.val.isFace 1)
  have hvc : Q.vertices.card = facetVertexCount P F := by
    unfold facetVertexCount
    rw [hv]
    simp [Q]
  rw [hvc,← he] at hdegree
  have hcZ :
      (Nat.card (NonedgesOn P F.val.carrier) : ℤ) +
        Nat.card (FaceBelow P F.val.carrier 1) =
        (facetVertexCount P F).choose 2 := by exact_mod_cast hc
  have hdZ : (facetDiagonalCount P F : ℤ) ≤
      Nat.card (NonedgesOn P F.val.carrier) := by exact_mod_cast hd
  have hdegZ : 3 * (facetVertexCount P F : ℤ) ≤
      2 * Nat.card (FaceBelow P F.val.carrier 1) := by exact_mod_cast hdegree
  have hchoose := twice_choose_two (facetVertexCount P F)
  nlinarith only [hcZ,hdZ,hdegZ,hchoose]

theorem facet_weight_surplus_identity (P : ConvexPolytope d) (F : Face P 3) (h : ℕ) :
    allocatedFacetWeight P F -
        ((facetVertexCount P F : ℚ) - 4) -
        ((facetPolygonExcess P F : ℚ) - h) = rankSurplus P F h := by
  have hc := face_nonedge_count P F.val.isFace
  have hcQ :
      (Nat.card (NonedgesOn P F.val.carrier) : ℚ) +
        Nat.card (FaceBelow P F.val.carrier 1) =
        (facetVertexCount P F).choose 2 := by exact_mod_cast hc
  have hg := facet_polygon_excess_formula P F
  have hgQ : (facetPolygonExcess P F : ℚ) =
      3 * (facetVertexCount P F : ℚ) -
        Nat.card (FaceBelow P F.val.carrier 1) - 6 := by exact_mod_cast hg
  have hchoose := twice_choose_two (facetVertexCount P F)
  have hchooseQ : 2 * ((facetVertexCount P F).choose 2 : ℚ) =
      (facetVertexCount P F : ℚ) * ((facetVertexCount P F : ℚ) - 1) := by
    exact_mod_cast hchoose
  rw [facet_weight_count]
  unfold rankSurplus facetDiagonalCount
  nlinarith only [hcQ,hgQ,hchooseQ]

theorem integral_diagonal_bound (r d : ℕ) (hr : 4 ≤ r)
    (hd : 2 * (d : ℤ) ≤ (r : ℤ) * ((r : ℤ) - 4)) :
    (d : ℤ) ≤ ((r : ℤ) - 4) * ((r : ℤ) - 5) + 4 := by
  by_cases hsmall : r ≤ 7
  · have hc : r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num at * <;> omega
  · have hp : 0 ≤ ((r : ℤ) - 8) * ((r : ℤ) - 6) :=
      mul_nonneg (by omega) (by omega)
    nlinarith only [hd,hp]

theorem numeric_surplus_nonnegative (r d h : ℕ) (hr : 4 ≤ r)
    (hd : 2 * (d : ℤ) ≤ (r : ℤ) * ((r : ℤ) - 4))
    (hzero : h = 0 → d = 0) (hone : h = 1 → d = 2) :
    0 ≤ ((r : ℚ) - 4) * ((r : ℚ) - 5) / 2 + h - (d : ℚ) / 2 := by
  have hp : 0 ≤ ((r : ℚ) - 4) * ((r : ℚ) - 5) := by
    by_cases h4 : r = 4
    · norm_num [h4]
    · have hr5 : 5 ≤ r := by omega
      exact mul_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ (r : ℤ)-4 by omega))
        (by exact_mod_cast (show (0 : ℤ) ≤ (r : ℤ)-5 by omega))
  by_cases h0 : h = 0
  · have hd0 := hzero h0
    norm_num [h0,hd0]
    exact div_nonneg hp (by norm_num)
  by_cases h1 : h = 1
  · have hd2 := hone h1
    norm_num [h1,hd2]
    exact div_nonneg hp (by norm_num)
  have hh : (2 : ℚ) ≤ h := by exact_mod_cast (show 2 ≤ h by omega)
  have hb := integral_diagonal_bound r d hr hd
  have hbQ : (d : ℚ) ≤ ((r : ℚ) - 4) * ((r : ℚ) - 5) + 4 := by
    exact_mod_cast hb
  nlinarith only [hh,hbQ]

theorem actual_rank_surplus_nonnegative (P : ConvexPolytope d)
    (F : Face P 3) (h : ℕ)
    (hzero : h = 0 → facetDiagonalCount P F = 0)
    (hone : h = 1 → facetDiagonalCount P F = 2) :
    0 ≤ rankSurplus P F h := by
  have hr : 4 ≤ facetVertexCount P F :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  exact numeric_surplus_nonnegative _ _ h hr (facet_diagonal_bound P F) hzero hone

end Papers.PolytopeFacetSurplus

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/PolytopeMasterBudget.lean -/




@[expose] public section

/-!
# Global shared-relation count and allocated-weight budget

All face and nonedge counts are those of an actual
four-polytope. For an arbitrary assignment of local polygon-span ranks
h_F, the exact weighted identity is proved. To deduce E≤D and a
nonnegative surplus, the final theorem exposes precisely the local rank
bounds and rank-zero/rank-one facts required from the actual relation
space construction. These premises are auxiliary joins, not silently
assumed parts of the universal rationality theorem.
-/

noncomputable section

namespace Papers.PolytopeMasterBudget

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerFour Papers.PolytopeSmallFacetBounds
open Papers.PolytopeNonedgeAllocation Papers.PolytopeFaceNonedges
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open Papers.FaceIncidenceEuler
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def sharedRelationCount (P : ConvexPolytope d) (h : Face P 3 → ℕ) : ℤ :=
  polygonExcess P + facetExcess P - ∑ F : Face P 3, (h F : ℤ)

theorem facet_edge_incidence_eq_polygon_vertices (P : ConvexPolytope d)
    (hdim : P.dim = 4) :
    (∑ F : Face P 3, (Nat.card (FaceBelow P F.val.carrier 1) : ℤ)) =
      ∑ R : Face P 2, (Nat.card (VerticesOn P R.val.carrier) : ℤ) := by
  let ef : Face P 1 → Face P 3 → Prop := fun e F => e.val.carrier ⊆ F.val.carrier
  let er : Face P 1 → Face P 2 → Prop := fun e R => e.val.carrier ⊆ R.val.carrier
  calc
    _ = ∑ e : Face P 1, (Nat.card (Coface P e.val.carrier 3) : ℤ) := by
      have h := (total_rows_eq_columns ef).symm
      simpa only [rowCount_card,colCount_card,ef,Coface,FaceBelow] using h
    _ = ∑ e : Face P 1, (Nat.card (Coface P e.val.carrier 2) : ℤ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [edge_figure_counts P hdim]
    _ = ∑ R : Face P 2, (Nat.card (FaceBelow P R.val.carrier 1) : ℤ) := by
      have h := total_rows_eq_columns er
      simpa only [rowCount_card,colCount_card,er,Coface,FaceBelow] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [two_face_vertices_eq_edges]

theorem sum_facet_polygon_excess (P : ConvexPolytope d) (hdim : P.dim = 4) :
    (∑ F : Face P 3, facetPolygonExcess P F) = 2 * polygonExcess P := by
  have hlocal := vertex_figure_incidence_budget P hdim
  have heuler := euler_four P hdim
  have hsum :
      (∑ F : Face P 3, facetPolygonExcess P F) =
        3 * (∑ F : Face P 3, (Nat.card (VerticesOn P F.val.carrier) : ℤ)) -
          (∑ R : Face P 2, (Nat.card (VerticesOn P R.val.carrier) : ℤ)) -
          6 * Nat.card (Face P 3) := by
    simp_rw [facet_polygon_excess_formula]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      facet_edge_incidence_eq_polygon_vertices P hdim]
    simp only [facetVertexCount,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
    ring
  unfold polygonExcess
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  omega

theorem shared_count_weight_identity (P : ConvexPolytope d)
    (hdim : P.dim = 4) (h : Face P 3 → ℕ) :
    (sharedRelationCount P h : ℚ) +
        (∑ F : Face P 3, rankSurplus P F (h F)) =
      (∑ F : Face P 3, allocatedFacetWeight P F) - (polygonExcess P : ℚ) := by
  have hsum :
      (∑ F : Face P 3, allocatedFacetWeight P F) -
        (∑ F : Face P 3, ((facetVertexCount P F : ℚ) - 4)) -
        (∑ F : Face P 3, ((facetPolygonExcess P F : ℚ) - h F)) =
        ∑ F : Face P 3, rankSurplus P F (h F) := by
    calc
      _ = ∑ F : Face P 3,
          (allocatedFacetWeight P F - ((facetVertexCount P F : ℚ)-4) -
            ((facetPolygonExcess P F : ℚ)-h F)) := by
        simp only [Finset.sum_sub_distrib]
      _ = _ := Finset.sum_congr rfl (fun F _ => facet_weight_surplus_identity P F (h F))
  have hE : (∑ F : Face P 3, ((facetVertexCount P F : ℚ)-4)) =
      (facetExcess P : ℚ) := by
    unfold facetExcess facetVertexCount
    push_cast
    rfl
  have hgZ := sum_facet_polygon_excess P hdim
  have hgQ : (∑ F : Face P 3, (facetPolygonExcess P F : ℚ)) =
      2 * (polygonExcess P : ℚ) := by exact_mod_cast hgZ
  rw [hE,Finset.sum_sub_distrib,hgQ] at hsum
  unfold sharedRelationCount
  push_cast
  linarith only [hsum]

theorem actual_shared_count_master_bound (P : ConvexPolytope d)
    (hdim : P.dim = 4) (h : Face P 3 → ℕ) :
    (sharedRelationCount P h : ℚ) +
        (∑ F : Face P 3, rankSurplus P F (h F)) ≤
      (P.vertices.card.choose 2 : ℚ) - P.vertices.card -
        Nat.card (Face P 3) - (facetExcess P : ℚ) := by
  rw [shared_count_weight_identity P hdim h]
  have hw := allocated_weights_le_nonedge_card P hdim
  have he := actual_excess_identity P hdim
  have heQ : (facetExcess P : ℚ) =
      (P.vertices.card.choose 2 : ℚ) - P.vertices.card -
        Nat.card (Face P 3) - Nat.card (Nonedge P) + (polygonExcess P : ℚ) := by
    exact_mod_cast he
  linarith only [hw,heQ]

theorem actual_budget_of_local_relation_ranks (P : ConvexPolytope d)
    (hdim : P.dim = 4) (h : Face P 3 → ℕ)
    (hbelow : ∀ F, (h F : ℤ) ≤ facetPolygonExcess P F)
    (hzero : ∀ F, h F = 0 → facetDiagonalCount P F = 0)
    (hone : ∀ F, h F = 1 → facetDiagonalCount P F = 2) :
    facetExcess P ≤ Nat.card (Nonedge P) ∧
      (∀ F, 0 ≤ rankSurplus P F (h F)) ∧
      (sharedRelationCount P h : ℚ) +
          (∑ F : Face P 3, rankSurplus P F (h F)) ≤
        (P.vertices.card.choose 2 : ℚ) - P.vertices.card -
          Nat.card (Face P 3) - (facetExcess P : ℚ) := by
  have heta : ∀ F, 0 ≤ rankSurplus P F (h F) := fun F =>
    actual_rank_surplus_nonnegative P F (h F) (hzero F) (hone F)
  have hlocal : ∀ F : Face P 3,
      ((facetVertexCount P F : ℚ)-4) ≤ allocatedFacetWeight P F := by
    intro F
    have hw := facet_weight_surplus_identity P F (h F)
    have he := heta F
    have hb : (h F : ℚ) ≤ (facetPolygonExcess P F : ℚ) := by
      exact_mod_cast hbelow F
    linarith only [hw,he,hb]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun F _ => hlocal F)
  have hE : (∑ F : Face P 3, ((facetVertexCount P F : ℚ)-4)) =
      (facetExcess P : ℚ) := by
    unfold facetExcess facetVertexCount
    push_cast
    rfl
  rw [hE] at hsum
  have hD := hsum.trans (allocated_weights_le_nonedge_card P hdim)
  refine ⟨?_,heta,actual_shared_count_master_bound P hdim h⟩
  exact_mod_cast hD

theorem ten_vertex_shared_count_bound (P : ConvexPolytope d)
    (hdim : P.dim = 4) (hn : P.vertices.card = 10) (h : Face P 3 → ℕ) :
    (sharedRelationCount P h : ℚ) +
        (∑ F : Face P 3, rankSurplus P F (h F)) ≤
      35 - Nat.card (Face P 3) - (facetExcess P : ℚ) := by
  have hbound := actual_shared_count_master_bound P hdim h
  rw [hn] at hbound
  norm_num only [show Nat.choose 10 2 = 45 by decide,Nat.cast_ofNat] at hbound
  exact hbound

end Papers.PolytopeMasterBudget

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/PolytopeDiagonalShapes.lean -/




@[expose] public section

/-!
# Diagonal counts from the actual polygon shapes in a facet

If every polygon of a genuine facet is triangular,
its diagonal count is zero. If exactly one polygon is a quadrilateral
and all others are triangles, the count is two. These are the geometric
cardinality adapters for the relation-rank zero/one lemmas.
-/

noncomputable section

namespace Papers.PolytopeDiagonalShapes

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeNonedgeAllocation
open Papers.PolytopeFaceNonedges Papers.PolytopeFacetSurplus
open scoped Classical

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem polygon_with_nonedge_has_four_vertices (P : ConvexPolytope d)
    (R : Face P 2) (e : Nonedge P) (he : Within P R.val.carrier e) :
    4 ≤ Nat.card (VerticesOn P R.val.carrier) := by
  have hr := face_vertices_card_ge_dim_add_one P 2 R
  have hc := polygon_nonedge_count P R
  letI : Nonempty (NonedgesOn P R.val.carrier) := ⟨⟨e,he⟩⟩
  have hp : 0 < Nat.card (NonedgesOn P R.val.carrier) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  by_contra h
  have hr3 : Nat.card (VerticesOn P R.val.carrier) = 3 := by omega
  rw [hr3] at hc
  norm_num only [show Nat.choose 3 2 = 3 by decide] at hc
  omega

theorem facet_diagonals_zero_of_triangles (P : ConvexPolytope d)
    (F : Face P 3)
    (htri : ∀ R : Face P 2, R.val.carrier ⊆ F.val.carrier →
      Nat.card (VerticesOn P R.val.carrier) = 3) :
    facetDiagonalCount P F = 0 := by
  have hnone : ∀ e : Nonedge P, ¬ DiagonalOn P F.val.carrier e := by
    intro e he
    obtain ⟨R,hxR,hyR⟩ := he.2
    obtain ⟨hne,hnon⟩ := nonedge_out P e
    have hRF := diagonal_face_subset P _ _ hne hnon R hxR hyR
      F.val.isFace he.1.1 he.1.2
    have h3 := htri R hRF
    have h4 := polygon_with_nonedge_has_four_vertices P R e ⟨hxR,hyR⟩
    omega
  unfold facetDiagonalCount DiagonalsOn
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact hnone e (Finset.mem_filter.mp he).2

theorem facet_diagonals_two_of_unique_quadrilateral (P : ConvexPolytope d)
    (F : Face P 3) (R : Face P 2)
    (hRF : R.val.carrier ⊆ F.val.carrier)
    (hR4 : Nat.card (VerticesOn P R.val.carrier) = 4)
    (hother : ∀ S : Face P 2, S.val.carrier ⊆ F.val.carrier → S ≠ R →
      Nat.card (VerticesOn P S.val.carrier) = 3) :
    facetDiagonalCount P F = 2 := by
  have heq (e : Nonedge P) :
      DiagonalOn P F.val.carrier e ↔ Within P R.val.carrier e := by
    constructor
    · intro he
      obtain ⟨S,hxS,hyS⟩ := he.2
      obtain ⟨hne,hnon⟩ := nonedge_out P e
      have hSF := diagonal_face_subset P _ _ hne hnon S hxS hyS
        F.val.isFace he.1.1 he.1.2
      have hSR : S = R := by
        by_contra hneSR
        have h3 := hother S hSF hneSR
        have h4 := polygon_with_nonedge_has_four_vertices P S e ⟨hxS,hyS⟩
        omega
      subst S
      exact ⟨hxS,hyS⟩
    · rintro ⟨hxR,hyR⟩
      exact ⟨⟨hRF hxR,hRF hyR⟩,R,hxR,hyR⟩
  let eqv : DiagonalsOn P F.val.carrier ≃ NonedgesOn P R.val.carrier :=
    { toFun := fun e => ⟨e.val,(heq e.val).mp e.property⟩
      invFun := fun e => ⟨e.val,(heq e.val).mpr e.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hd := Nat.card_congr eqv
  have hc := polygon_nonedge_count P R
  rw [hR4] at hc
  norm_num only [show Nat.choose 4 2 = 6 by decide] at hc
  unfold facetDiagonalCount
  omega

end Papers.PolytopeDiagonalShapes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/PolytopeFaceRestriction.lean -/




@[expose] public section

/-!
# Restricting actual vertex counts to a face polytope

The coordinate of every vertex is unchanged. The
equivalence uses the literal filtered vertex set of facePolytope, and
the face correspondence preserves its carrier definitionally.
-/

noncomputable section

namespace Papers.PolytopeFaceRestriction

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open scoped Classical BigOperators

variable {d : ℕ}

local instance faceFintype (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _


def verticesOn_facePolytope_equiv (P : ConvexPolytope d)
    {A B : Set (E d)} (hA : P.IsFace A) (hBA : B ⊆ A) :
    VerticesOn (facePolytope P hA) B ≃ VerticesOn P B where
  toFun v := ⟨⟨v.val.val,(Finset.mem_filter.mp v.val.property).1⟩,v.property⟩
  invFun v := ⟨⟨v.val.val,Finset.mem_filter.mpr
    ⟨v.val.property,hBA v.property⟩⟩,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem verticesOn_facePolytope_card (P : ConvexPolytope d)
    {A B : Set (E d)} (hA : P.IsFace A) (hBA : B ⊆ A) :
    Nat.card (VerticesOn (facePolytope P hA) B) =
      Nat.card (VerticesOn P B) :=
  Nat.card_congr (verticesOn_facePolytope_equiv P hA hBA)

@[simp] theorem faceBelowEquiv_carrier (P : ConvexPolytope d)
    {A : Set (E d)} (hA : P.IsFace A) (k : ℕ)
    (F : FaceBelow P A k) :
    ((faceBelowEquiv P hA k) F).val.carrier = F.val.val.carrier := rfl

theorem faceBelowEquiv_vertex_card (P : ConvexPolytope d)
    {A : Set (E d)} (hA : P.IsFace A) (k : ℕ)
    (F : FaceBelow P A k) :
    Nat.card (VerticesOn (facePolytope P hA)
        ((faceBelowEquiv P hA k) F).val.carrier) =
      Nat.card (VerticesOn P F.val.val.carrier) := by
  rw [faceBelowEquiv_carrier]
  exact verticesOn_facePolytope_card P hA F.property

theorem facetPolygonExcess_eq_sum_faceBelow (P : ConvexPolytope d)
    (F : Face P 3) :
    facetPolygonExcess P F =
      ∑ R : FaceBelow P F.val.carrier 2,
        ((Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3) := by
  unfold facetPolygonExcess polygonExcess
  let e := faceBelowEquiv P F.val.isFace 2
  calc
    _ = ∑ R : FaceBelow P F.val.carrier 2,
        ((Nat.card (VerticesOn (facePolytope P F.val.isFace)
          (e R).val.carrier) : ℤ) - 3) := by
      exact (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [faceBelowEquiv_vertex_card]

end Papers.PolytopeFaceRestriction

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/ActualPolygonRelationBudget.lean -/






@[expose] public section
noncomputable section
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget
open Papers.PolytopeRelationBudget
open Papers.PolytopeDiagonalShapes Papers.PolytopeFaceRestriction

namespace Papers.RationalityTen.ChirotopeDensity

def polygonLabelsBelow {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun R : FaceBelow P F.val.carrier 2 =>
    actualFaceLabels P e R.val.val)

def actualPolygonRelationRank {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) : ℕ :=
  finrank ℝ (polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F))

theorem polygonLabelsBelow_injective {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    Function.Injective (fun R : FaceBelow P F.val.carrier 2 =>
      actualFaceLabels P e R.val.val) := by
  intro R S h
  apply Subtype.ext
  apply Subtype.ext
  exact actualFaceLabels_injective P e h

theorem polygonLabelsBelow_rank {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    ∀ S∈polygonLabelsBelow P e F,subsetRank (vertexCoordinates P e) S=3 := by
  intro S hS
  obtain ⟨R,_,rfl⟩ := Finset.mem_image.mp hS
  rw [actualFaceLabels_rank,R.val.property]

theorem actualPolygonRelationRank_le {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    (actualPolygonRelationRank P e F : ℤ)≤facetPolygonExcess P F := by
  have hle := polygonRelationSpan_finrank_le (vertexCoordinates P e) (polygonLabelsBelow P e F)
  rw [polygonLabelsBelow,Finset.sum_image] at hle
  · have hdim : ∀ R : FaceBelow P F.val.carrier 2,
        (finrank ℝ (globalRelationSpace (vertexCoordinates P e)
          (actualFaceLabels P e R.val.val)) : ℤ)=
          (Nat.card (VerticesOn P R.val.val.carrier) : ℤ)-3 := by
      intro R
      have h := globalRelationSpace_finrank (vertexCoordinates P e)
        (actualFaceLabels P e R.val.val)
      rw [actualFaceLabels_rank,R.val.property,actualFaceLabels_card] at h
      omega
    rw [facetPolygonExcess_eq_sum_faceBelow]
    have hcast : (actualPolygonRelationRank P e F : ℤ)≤
        (∑ R : FaceBelow P F.val.carrier 2,
          finrank ℝ (globalRelationSpace (vertexCoordinates P e)
            (actualFaceLabels P e R.val.val)) : ℕ) := by exact_mod_cast hle
    simp only [Nat.cast_sum, hdim] at hcast
    exact hcast
  · intro R _ S _ h
    exact polygonLabelsBelow_injective P e F h

theorem actualPolygonRelationRank_zero {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hzero : actualPolygonRelationRank P e F=0) : facetDiagonalCount P F=0 := by
  apply facet_diagonals_zero_of_triangles P F
  intro R hRF
  have hR : actualFaceLabels P e R.val∈polygonLabelsBelow P e F :=
    Finset.mem_image.mpr ⟨⟨R,hRF⟩,Finset.mem_univ _,rfl⟩
  have h := polygonRelationSpan_zero_shapes (vertexCoordinates P e)
    (polygonLabelsBelow P e F) (polygonLabelsBelow_rank P e F) hzero _ hR
  simpa only [actualFaceLabels_card] using h

theorem actualPolygonRelationRank_one {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (hP : 3≤P.vertices.card) (F : Face P 3)
    (hone : actualPolygonRelationRank P e F=1) : facetDiagonalCount P F=2 := by
  obtain ⟨S,hS,hS4,hother⟩ := polygonRelationSpan_one_shapes (vertexCoordinates P e)
    (polygonLabelsBelow P e F) (polygonLabelsBelow_rank P e F)
    (vertexCoordinates_small_independent P e hP) hone
  obtain ⟨R,_,rfl⟩ := Finset.mem_image.mp hS
  apply facet_diagonals_two_of_unique_quadrilateral P F R.val R.property
  · simpa only [actualFaceLabels_card] using hS4
  · intro T hTF hTR
    have hT : actualFaceLabels P e T.val∈polygonLabelsBelow P e F :=
      Finset.mem_image.mpr ⟨⟨T,hTF⟩,Finset.mem_univ _,rfl⟩
    have hne : actualFaceLabels P e T.val≠actualFaceLabels P e R.val.val := by
      intro heq
      exact hTR (Subtype.ext (actualFaceLabels_injective P e heq))
    simpa only [actualFaceLabels_card] using hother _ hT hne

/-- Section 5.2 with the local ranks constructed from the actual polygon
relation spaces of the given polytope. There are no rank or incidence
certificates among its hypotheses. -/
theorem actual_polygon_relation_budget {d n : ℕ} (P : ConvexPolytope d)
    (hdim : P.dim=4) (e : Fin n ≃ P.vertices) :
    facetExcess P≤Nat.card (Papers.PolytopeNonedgeAllocation.Nonedge P) ∧
    (∀F,0≤rankSurplus P F (actualPolygonRelationRank P e F)) ∧
    (sharedRelationCount P (actualPolygonRelationRank P e) : ℚ)+
      (∑ F : Face P 3,rankSurplus P F (actualPolygonRelationRank P e F))≤
      (P.vertices.card.choose 2 : ℚ)-P.vertices.card-Nat.card (Face P 3)-
        (facetExcess P : ℚ) := by
  have hcard : 3≤P.vertices.card := by
    obtain ⟨v,hv⟩ := P.vertices_nonempty
    have hne : P.toSet.Nonempty := ⟨v,subset_convexHull ℝ _ hv⟩
    have h := Papers.FaceVertexCardinality.dimension_add_one_le_card_of_subset_hull
      hne P.vertices (Set.Subset.refl P.toSet)
    change P.dim+1≤P.vertices.card at h
    omega
  exact actual_budget_of_local_relation_ranks P hdim (actualPolygonRelationRank P e)
    (actualPolygonRelationRank_le P e) (actualPolygonRelationRank_zero P e)
    (actualPolygonRelationRank_one P e hcard)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/ActualSharedFacetRelations.lean -/





@[expose] public section
noncomputable section
open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget

namespace Papers.RationalityTen.ChirotopeDensity

theorem actualPolygonRelationSpan_le {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F)≤
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  apply Finset.sup_le
  intro S hS
  obtain ⟨R,_,rfl⟩ := Finset.mem_image.mp hS
  exact globalRelationSpace_mono _ (actualFaceLabels_mono P e R.property)

def actualFacetSupplement {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    FiniteSpaceSupplement
      (polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F))
      (globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val)) :=
  Classical.choice (exists_finiteSpaceSupplement _ _ (actualPolygonRelationSpan_le P e F))

def ActualSharedRowIndex {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :=
  (ΣR : Face P 2,Fin (finrank ℝ
    (globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val)))) ⊕
  (ΣF : Face P 3,Fin (actualFacetSupplement P e F).count)

instance {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    Fintype (ActualSharedRowIndex P e) := by
  unfold ActualSharedRowIndex
  infer_instance

def actualSharedRow {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    ActualSharedRowIndex P e → Fin n → ℝ
  | Sum.inl ⟨R,i⟩ => (Module.finBasis ℝ
      (globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val)) i).val
  | Sum.inr ⟨F,i⟩ => (actualFacetSupplement P e F).rows i

theorem actualSharedRow_relation {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (i : ActualSharedRowIndex P e) :
    (Matrix.of (vertexCoordinates P e)).transpose.mulVec (actualSharedRow P e i)=0 := by
  rcases i with ⟨R,i⟩ | ⟨F,i⟩
  · exact ((mem_globalRelationSpace_iff _ _ _).mp
      (Module.finBasis ℝ (globalRelationSpace (vertexCoordinates P e)
        (actualFaceLabels P e R.val)) i).property).2
  · exact ((mem_globalRelationSpace_iff _ _ _).mp
      ((actualFacetSupplement P e F).mem i)).2

def supportedRowSpan {I : Type*} {n : ℕ} (C : I → Fin n → ℝ)
    (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {v | ∃i,C i=v ∧ ∀j,j∉S → C i j=0}

theorem actualSharedRows_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    supportedRowSpan (actualSharedRow P e) (actualFaceLabels P e F.val)=
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  let p := vertexCoordinates P e
  let S := actualFaceLabels P e F.val
  let T := supportedRowSpan (actualSharedRow P e) S
  have hle : T≤globalRelationSpace p S := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl,hi⟩
    exact (mem_globalRelationSpace_iff p S _).mpr
      ⟨hi,actualSharedRow_relation P e i⟩
  have hpoly : polygonRelationSpan p (polygonLabelsBelow P e F)≤T := by
    apply Finset.sup_le
    intro U hU
    obtain ⟨R,_,rfl⟩ := Finset.mem_image.mp hU
    rw [←span_basis_coe (globalRelationSpace p (actualFaceLabels P e R.val.val))]
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    apply Submodule.subset_span
    let k : ActualSharedRowIndex P e := Sum.inl ⟨R.val,i⟩
    refine ⟨k,rfl,?_⟩
    have hm : actualSharedRow P e k∈globalRelationSpace p S :=
      globalRelationSpace_mono p (actualFaceLabels_mono P e R.property)
        (Module.finBasis ℝ (globalRelationSpace p
          (actualFaceLabels P e R.val.val)) i).property
    exact ((mem_globalRelationSpace_iff p S _).mp hm).1
  have hsupp : Submodule.span ℝ (Set.range (actualFacetSupplement P e F).rows)≤T := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.inr ⟨F,i⟩,rfl,?_⟩
    exact ((mem_globalRelationSpace_iff p S _).mp
      ((actualFacetSupplement P e F).mem i)).1
  apply le_antisymm hle
  rw [←(actualFacetSupplement P e F).spans]
  exact sup_le hpoly hsupp

theorem actualSharedRowIndex_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    (Fintype.card (ActualSharedRowIndex P e) : ℤ)=
      sharedRelationCount P (actualPolygonRelationRank P e) := by
  have hR : ∀R : Face P 2,
      (finrank ℝ (globalRelationSpace (vertexCoordinates P e)
        (actualFaceLabels P e R.val)) : ℤ)=
        (Nat.card (VerticesOn P R.val.carrier) : ℤ)-3 := by
    intro R
    have h := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e R.val)
    rw [actualFaceLabels_rank,R.property,actualFaceLabels_card] at h
    omega
  have hF : ∀F : Face P 3,
      ((actualFacetSupplement P e F).count : ℤ)=
        (Nat.card (VerticesOn P F.val.carrier) : ℤ)-4-actualPolygonRelationRank P e F := by
    intro F
    have h := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e F.val)
    rw [actualFaceLabels_rank,F.property,actualFaceLabels_card] at h
    have hs := (actualFacetSupplement P e F).dimension
    change (actualFacetSupplement P e F).count+actualPolygonRelationRank P e F=_ at hs
    omega
  simp only [ActualSharedRowIndex,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,
    Nat.cast_add,Nat.cast_sum,hR,hF,sharedRelationCount,polygonExcess,facetExcess,
    Finset.sum_sub_distrib] <;> ring

def actualSharedMatrix {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    Matrix (Fin (Fintype.card (ActualSharedRowIndex P e))) (Fin n) ℝ :=
  fun i => actualSharedRow P e ((Fintype.equivFin (ActualSharedRowIndex P e)).symm i)

theorem actualSharedMatrix_mul_zero {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) : actualSharedMatrix P e*Matrix.of (vertexCoordinates P e)=0 := by
  ext i j
  have h := congrFun (actualSharedRow_relation P e
    ((Fintype.equivFin (ActualSharedRowIndex P e)).symm i)) j
  simpa [actualSharedMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using h

theorem actualSharedMatrix_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    supportedRowSpan (actualSharedMatrix P e) (actualFaceLabels P e F.val)=
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  rw [←actualSharedRows_span_facet P e F]
  apply congrArg (Submodule.span ℝ)
  ext v
  constructor
  · rintro ⟨i,hi,hs⟩
    exact ⟨(Fintype.equivFin (ActualSharedRowIndex P e)).symm i,hi,hs⟩
  · rintro ⟨i,hi,hs⟩
    refine ⟨Fintype.equivFin (ActualSharedRowIndex P e) i,?_,?_⟩
    · simpa only [actualSharedMatrix,Equiv.symm_apply_apply] using hi
    · simpa only [actualSharedMatrix,Equiv.symm_apply_apply] using hs

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/ActualSharedRelationInterface.lean -/





@[expose] public section

/-!
# The ordinary polytope supplies the relation-density hypotheses

The shared row construction uses ambient coefficient vectors. The density
criterion uses their restrictions to each facet. Restriction identifies these
spaces exactly. A supporting mask of homogeneous vertex coordinates is then
identified with an actual exposed three-face, so the criterion applies to every
facet rather than only a supplied list of facial constraints.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration Papers.ActualThreeVertexIndependence
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget
open Papers.PolytopeFacetSurplus

def relationRestriction {n : ℕ} (S : Finset (Fin n)) :
    (Fin n → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun v i := v i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem relationRestriction_globalRelationMap {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (v : facetRelationSpace p S) :
    relationRestriction S (globalRelationMap p S v) = v.val := by
  ext i
  simp [relationRestriction, globalRelationMap, insideInjection, i.property]

theorem relationRestriction_globalRelationSpace {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    (globalRelationSpace p S).map (relationRestriction S) = facetRelationSpace p S := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
    simpa only [relationRestriction_globalRelationMap] using u.property
  · intro hv
    refine ⟨globalRelationMap p S ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
    exact relationRestriction_globalRelationMap p S ⟨v, hv⟩

theorem relationRestriction_supportedRowSpan {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin n)) :
    (supportedRowSpan C S).map (relationRestriction S) =
      Submodule.span ℝ (Set.range (restrictedSupportedRows C S)) := by
  unfold supportedRowSpan
  rw [Submodule.map_span]
  apply congrArg (Submodule.span ℝ)
  ext v
  constructor
  · rintro ⟨w, ⟨i, rfl, hi⟩, rfl⟩
    have hmem : i ∈ supportedRelationRows C S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    exact ⟨⟨i, hmem⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨C i.val, ⟨i.val, rfl, (Finset.mem_filter.mp i.property).2⟩, rfl⟩

theorem spansFacetRelations_of_supportedRowSpan {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n))
    (h : supportedRowSpan C S = globalRelationSpace p S) :
    SpansFacetRelations C p S := by
  have hm := congrArg (fun U : Submodule ℝ (Fin n → ℝ) =>
    U.map (relationRestriction S)) h
  rw [relationRestriction_supportedRowSpan, relationRestriction_globalRelationSpace] at hm
  exact hm

/-- Every supporting homogeneous mask of rank four is the full vertex set
of an actual exposed three-face. No combinatorial coverage is assumed. -/
theorem facetMask_actual_three_face {n : ℕ} (P : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) (S : Finset (Fin n))
    (hS : FacetMask (vertexCoordinates P e) S) :
    ∃ F : Face P 3, actualFaceLabels P e F.val = S := by
  obtain ⟨a, ha⟩ := hS.2.1
  let f := formOfVector a
  have hvalue (i : Fin n) : f (e i).val = a ⬝ᵥ vertexCoordinates P e i :=
    (vector_dot_homogeneous a (e i).val).symm
  have hnonneg : ∀ x ∈ P.toSet, 0 ≤ f x := by
    apply affine_nonneg_on_hull
    intro x hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hxi : (e i).val = x := congrArg Subtype.val hi
    rw [← hxi, hvalue]
    by_cases hiS : i ∈ S
    · exact (ha.1 i hiS).ge
    · exact (ha.2 i hiS).le
  have hnonempty : (affineZeroFace P f).Nonempty := by
    obtain ⟨i, hi⟩ := hS.1
    refine ⟨(e i).val, subset_convexHull ℝ _ (e i).property, ?_⟩
    rw [hvalue]
    exact ha.1 i hi
  let F : PolytopeFace P :=
    ⟨affineZeroFace P f, affineZeroFace_isFace P f hnonneg hnonempty⟩
  have hlabels : actualFaceLabels P e F = S := by
    ext i
    rw [mem_actualFaceLabels]
    change ((e i).val ∈ P.toSet ∧ f (e i).val = 0) ↔ i ∈ S
    constructor
    · intro hi
      by_contra hiS
      have hpos := ha.2 i hiS
      rw [← hvalue] at hpos
      exact (ne_of_gt hpos) hi.2
    · intro hi
      refine ⟨subset_convexHull ℝ _ (e i).property, ?_⟩
      rw [hvalue]
      exact ha.1 i hi
  have hrank := actualFaceLabels_rank P e F
  rw [hlabels] at hrank
  have hcodim := hS.2.2
  have hdim : faceDim F.carrier = 3 := by omega
  exact ⟨⟨F, hdim⟩, hlabels⟩

theorem actualSharedMatrix_spans_facetMasks {n : ℕ} (P : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) (S : Finset (Fin n))
    (hS : FacetMask (vertexCoordinates P e) S) :
    SpansFacetRelations (actualSharedMatrix P e) (vertexCoordinates P e) S := by
  obtain ⟨F, hF⟩ := facetMask_actual_three_face P e S hS
  rw [← hF]
  exact spansFacetRelations_of_supportedRowSpan _ _ _
    (actualSharedMatrix_span_facet P e F)

/-- All structural hypotheses required by the relation-matrix density
criterion are supplied by the ordinary full-dimensional polytope. -/
theorem actualSharedMatrix_density_input {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    Spans (vertexCoordinates P e) ∧
    (∀ i, vertexCoordinates P e i 0 = 1) ∧
    actualSharedMatrix P e * Matrix.of (vertexCoordinates P e) = 0 ∧
    ∀ S, FacetMask (vertexCoordinates P e) S →
      SpansFacetRelations (actualSharedMatrix P e) (vertexCoordinates P e) S := by
  exact ⟨vertexCoordinates_spans P e hP, (fun _ => rfl),
    actualSharedMatrix_mul_zero P e, actualSharedMatrix_spans_facetMasks P e⟩

theorem actualSharedRowIndex_budget {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    (Fintype.card (ActualSharedRowIndex P e) : ℚ) +
      (∑ F : Face P 3, rankSurplus P F (actualPolygonRelationRank P e F)) ≤
      (P.vertices.card.choose 2 : ℚ) - P.vertices.card - Nat.card (Face P 3) -
        (facetExcess P : ℚ) := by
  have h := (actual_polygon_relation_budget P hP e).2.2
  have hc : (Fintype.card (ActualSharedRowIndex P e) : ℚ) =
      (sharedRelationCount P (actualPolygonRelationRank P e) : ℚ) := by
    exact_mod_cast actualSharedRowIndex_card P e
  rw [hc]
  exact h

theorem actualSharedRowIndex_count_bound {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    (Fintype.card (ActualSharedRowIndex P e) : ℤ) ≤
      (P.vertices.card.choose 2 : ℤ) - P.vertices.card - Nat.card (Face P 3) -
        facetExcess P := by
  have hb := actualSharedRowIndex_budget P hP e
  have hnonneg : 0 ≤ ∑ F : Face P 3,
      rankSurplus P F (actualPolygonRelationRank P e F) :=
    Finset.sum_nonneg (fun F _ => (actual_polygon_relation_budget P hP e).2.1 F)
  have hq : (Fintype.card (ActualSharedRowIndex P e) : ℚ) ≤
      (P.vertices.card.choose 2 : ℚ) - P.vertices.card - Nat.card (Face P 3) -
        (facetExcess P : ℚ) := by linarith only [hb, hnonneg]
  exact_mod_cast hq

/-- The high-facet reduction in Section 6, expressed using the constructed
relation matrix rather than an abstract count with unproved provenance. -/
theorem actualSharedRowIndex_le_eight_of_high_facet_count {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hE : 10 ≤ facetExcess P)
    (hm : 17 ≤ Nat.card (Face P 3)) :
    Fintype.card (ActualSharedRowIndex P e) ≤ 8 := by
  have h := actualSharedRowIndex_count_bound P hP e
  rw [hn] at h
  norm_num only [show Nat.choose 10 2 = 45 by decide, Nat.cast_ofNat] at h
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/ActualRelationMatrixDensity.lean -/




@[expose] public section

/-!
# The relation-matrix criterion for genuine convex polytopes

The first theorem composes coordinate reconstruction with the separately
proved bridge to actual extreme vertices and face-order vertex labels.
The small-row consequences use proved matrix-density results directly.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeRelationBudget

theorem rationallyApproximable_of_relation_matrix_density {c n d : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (C : Matrix (Fin c) (Fin n) ℝ)
    (hCp : C * Matrix.of (vertexCoordinates P e) = 0)
    (hrelations : ∀ S, FacetMask (vertexCoordinates P e) S →
      SpansFacetRelations C (vertexCoordinates P e) S)
    (hC : C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank = C.rank ∧ PreservesZeroEntries C C'}) :
    Papers.Polytopes.RationallyApproximable P := by
  have hh := rational_polytope_density_from_relation_matrix_density C
    (vertexCoordinates P e) (vertexCoordinates_spans P e hP)
    (fun _ => rfl) hCp hrelations hC
  have ho := ordinary_density_of_homogeneous_density (ordinaryVertexCoordinates P e)
    (by simpa only [ordinaryVertexCoordinates_homogeneous] using hh)
  apply rationallyApproximable_of_coordinate_density P e
  apply closure_mono ?_ ho
  intro q hq
  exact ⟨hq.1, hq.2.2⟩

theorem actualSharedMatrix_rank_bound {d n : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    (actualSharedMatrix P e).rank + (d + 1) ≤ n := by
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero (actualSharedMatrix_mul_zero P e)
  have hp := (spans_iff_matrix_rank (vertexCoordinates P e)).mp
    (vertexCoordinates_spans P e hP)
  rw [hp] at h
  simpa only [Fintype.card_fin] using h

theorem rationallyApproximable_of_actualSharedMatrix_density {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hC : actualSharedMatrix P e ∈ closure
      {C' : Matrix (Fin (Fintype.card (ActualSharedRowIndex P e))) (Fin n) ℝ |
        RationalCoordinates C' ∧ C'.rank = (actualSharedMatrix P e).rank ∧
        PreservesZeroEntries (actualSharedMatrix P e) C'}) :
    Papers.Polytopes.RationallyApproximable P :=
  rationallyApproximable_of_relation_matrix_density P hP e (actualSharedMatrix P e)
    (actualSharedMatrix_mul_zero P e) (actualSharedMatrix_spans_facetMasks P e) hC

theorem actual_polytope_seven_shared_relations {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (ActualSharedRowIndex P e) ≤ 7) :
    Papers.Polytopes.RationallyApproximable P :=
  rationallyApproximable_of_actualSharedMatrix_density P hP e
    (rational_matrix_zero_pattern_rank_density_seven hc (actualSharedMatrix P e))

theorem actual_polytope_eight_nonfour_shared_relations {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (ActualSharedRowIndex P e) ≤ 8)
    (hr : (actualSharedMatrix P e).rank ≠ 4) :
    Papers.Polytopes.RationallyApproximable P :=
  rationallyApproximable_of_actualSharedMatrix_density P hP e
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hc (actualSharedMatrix P e) hr)

theorem actual_high_facet_count_nonfour_density {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hE : 10 ≤ facetExcess P)
    (hm : 17 ≤ Nat.card (Face P 3))
    (hr : (actualSharedMatrix P e).rank ≠ 4) :
    Papers.Polytopes.RationallyApproximable P :=
  actual_polytope_eight_nonfour_shared_relations P hP e
    (actualSharedRowIndex_le_eight_of_high_facet_count P hP e hn hE hm) hr

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/SparseSharedFacetRelations.lean -/




@[expose] public section

/-!
# A circuit-sparse shared facet-relation matrix

Polygon bases have support at most four; facet supplements have support at
most five. Supplements are selected in the quotient by the full polygon
relation span, so the exact shared-row count is preserved. This is the
sparsity needed by the golden-exception argument in Appendix A.4.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget

structure SparseSpaceSupplement {n : ℕ}
    (U V : Submodule ℝ (Fin n → ℝ)) (bound : ℕ)
    extends FiniteSpaceSupplement U V where
  sparse : ∀ i, (vectorSupport (rows i)).card ≤ bound

theorem exists_sparseSpaceSupplement {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (U : Submodule ℝ (Fin n → ℝ)) (hU : U ≤ globalRelationSpace p S) :
    Nonempty (SparseSpaceSupplement U (globalRelationSpace p S) (subsetRank p S + 1)) := by
  obtain ⟨g, hg, hgs⟩ := exists_sparse_global_relation_generators p S
  obtain ⟨D, hD⟩ := exists_finiteSpaceSupplement_from_generators U _ hU g hg
  refine ⟨{ toFiniteSpaceSupplement := D, sparse := ?_ }⟩
  intro i
  obtain ⟨j, hj⟩ := hD i
  rw [← hj]
  exact hgs j

def actualPolygonSparseBasis {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (R : Face P 2) :
    SparseSpaceSupplement ⊥
      (globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val)) 4 := by
  have h := exists_sparseSpaceSupplement (vertexCoordinates P e)
    (actualFaceLabels P e R.val) ⊥ bot_le
  rw [actualFaceLabels_rank, R.property] at h
  exact Classical.choice h

def actualFacetSparseSupplement {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    SparseSpaceSupplement
      (polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F))
      (globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val)) 5 := by
  have h := exists_sparseSpaceSupplement (vertexCoordinates P e)
    (actualFaceLabels P e F.val) _ (actualPolygonRelationSpan_le P e F)
  rw [actualFaceLabels_rank, F.property] at h
  exact Classical.choice h

def SparseSharedRowIndex {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :=
  (Σ R : Face P 2, Fin (actualPolygonSparseBasis P e R).count) ⊕
  (Σ F : Face P 3, Fin (actualFacetSparseSupplement P e F).count)

instance {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    Fintype (SparseSharedRowIndex P e) := by
  unfold SparseSharedRowIndex
  infer_instance

def actualSparseSharedRow {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    SparseSharedRowIndex P e → Fin n → ℝ
  | Sum.inl ⟨R, i⟩ => (actualPolygonSparseBasis P e R).rows i
  | Sum.inr ⟨F, i⟩ => (actualFacetSparseSupplement P e F).rows i

theorem actualSparseSharedRow_relation {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (i : SparseSharedRowIndex P e) :
    (Matrix.of (vertexCoordinates P e)).transpose.mulVec (actualSparseSharedRow P e i) = 0 := by
  rcases i with ⟨R, i⟩ | ⟨F, i⟩
  · exact ((mem_globalRelationSpace_iff _ _ _).mp
      ((actualPolygonSparseBasis P e R).mem i)).2
  · exact ((mem_globalRelationSpace_iff _ _ _).mp
      ((actualFacetSparseSupplement P e F).mem i)).2

theorem actualPolygonSparseBasis_span {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (R : Face P 2) :
    Submodule.span ℝ (Set.range (actualPolygonSparseBasis P e R).rows) =
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val) := by
  simpa only [bot_sup_eq] using (actualPolygonSparseBasis P e R).spans

theorem actualSparseSharedRows_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    supportedRowSpan (actualSparseSharedRow P e) (actualFaceLabels P e F.val) =
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  let p := vertexCoordinates P e
  let S := actualFaceLabels P e F.val
  let T := supportedRowSpan (actualSparseSharedRow P e) S
  have hle : T ≤ globalRelationSpace p S := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl, hi⟩
    exact (mem_globalRelationSpace_iff p S _).mpr
      ⟨hi, actualSparseSharedRow_relation P e i⟩
  have hpoly : polygonRelationSpan p (polygonLabelsBelow P e F) ≤ T := by
    apply Finset.sup_le
    intro U hU
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hU
    rw [← actualPolygonSparseBasis_span P e R.val]
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.inl ⟨R.val, i⟩, rfl, ?_⟩
    have hm := globalRelationSpace_mono p (actualFaceLabels_mono P e R.property)
      ((actualPolygonSparseBasis P e R.val).mem i)
    exact ((mem_globalRelationSpace_iff p S _).mp hm).1
  have hsupp : Submodule.span ℝ (Set.range (actualFacetSparseSupplement P e F).rows) ≤ T := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.inr ⟨F, i⟩, rfl, ?_⟩
    exact ((mem_globalRelationSpace_iff p S _).mp
      ((actualFacetSparseSupplement P e F).mem i)).1
  apply le_antisymm hle
  rw [← (actualFacetSparseSupplement P e F).spans]
  exact sup_le hpoly hsupp

theorem actualPolygonSparseBasis_count {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (R : Face P 2) :
    ((actualPolygonSparseBasis P e R).count : ℤ) =
      (Nat.card (VerticesOn P R.val.carrier) : ℤ) - 3 := by
  have h := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e R.val)
  rw [actualFaceLabels_rank, R.property, actualFaceLabels_card] at h
  have hd := (actualPolygonSparseBasis P e R).dimension
  simp only [finrank_bot, add_zero] at hd
  omega

theorem actualFacetSparseSupplement_count {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    ((actualFacetSparseSupplement P e F).count : ℤ) =
      (Nat.card (VerticesOn P F.val.carrier) : ℤ) - 4 - actualPolygonRelationRank P e F := by
  have h := globalRelationSpace_finrank (vertexCoordinates P e) (actualFaceLabels P e F.val)
  rw [actualFaceLabels_rank, F.property, actualFaceLabels_card] at h
  have hd := (actualFacetSparseSupplement P e F).dimension
  change (actualFacetSparseSupplement P e F).count + actualPolygonRelationRank P e F = _ at hd
  omega

theorem sparseSharedRowIndex_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    (Fintype.card (SparseSharedRowIndex P e) : ℤ) =
      sharedRelationCount P (actualPolygonRelationRank P e) := by
  simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Nat.cast_add, Nat.cast_sum, actualPolygonSparseBasis_count,
    actualFacetSparseSupplement_count, sharedRelationCount, polygonExcess, facetExcess,
    Finset.sum_sub_distrib] <;> ring

theorem sparseSharedRowIndex_card_eq {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    Fintype.card (SparseSharedRowIndex P e) = Fintype.card (ActualSharedRowIndex P e) := by
  have h₁ := sparseSharedRowIndex_card P e
  have h₂ := actualSharedRowIndex_card P e
  omega

def actualSparseSharedMatrix {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    Matrix (Fin (Fintype.card (SparseSharedRowIndex P e))) (Fin n) ℝ :=
  fun i => actualSparseSharedRow P e ((Fintype.equivFin (SparseSharedRowIndex P e)).symm i)

theorem actualSparseSharedMatrix_mul_zero {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    actualSparseSharedMatrix P e * Matrix.of (vertexCoordinates P e) = 0 := by
  ext i j
  have h := congrFun (actualSparseSharedRow_relation P e
    ((Fintype.equivFin (SparseSharedRowIndex P e)).symm i)) j
  simpa [actualSparseSharedMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h

theorem actualSparseSharedMatrix_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    supportedRowSpan (actualSparseSharedMatrix P e) (actualFaceLabels P e F.val) =
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  rw [← actualSparseSharedRows_span_facet P e F]
  apply congrArg (Submodule.span ℝ)
  ext v
  constructor
  · rintro ⟨i, hi, hs⟩
    exact ⟨(Fintype.equivFin (SparseSharedRowIndex P e)).symm i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    refine ⟨Fintype.equivFin (SparseSharedRowIndex P e) i, ?_, ?_⟩
    · simpa only [actualSparseSharedMatrix, Equiv.symm_apply_apply] using hi
    · simpa only [actualSparseSharedMatrix, Equiv.symm_apply_apply] using hs

theorem actualSparseSharedMatrix_spans_facetMasks {n : ℕ} (P : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) (S : Finset (Fin n))
    (hS : FacetMask (vertexCoordinates P e) S) :
    SpansFacetRelations (actualSparseSharedMatrix P e) (vertexCoordinates P e) S := by
  obtain ⟨F, hF⟩ := facetMask_actual_three_face P e S hS
  rw [← hF]
  exact spansFacetRelations_of_supportedRowSpan _ _ _
    (actualSparseSharedMatrix_span_facet P e F)

theorem actualSparseSharedRowIndex_le_eight_of_high_facet_count {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hE : 10 ≤ facetExcess P)
    (hm : 17 ≤ Nat.card (Face P 3)) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 8 := by
  rw [sparseSharedRowIndex_card_eq]
  exact actualSharedRowIndex_le_eight_of_high_facet_count P hP e hn hE hm

theorem rationallyApproximable_of_actualSparseSharedMatrix_density {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hC : actualSparseSharedMatrix P e ∈ closure
      {C' : Matrix (Fin (Fintype.card (SparseSharedRowIndex P e))) (Fin n) ℝ |
        RationalCoordinates C' ∧ C'.rank = (actualSparseSharedMatrix P e).rank ∧
        PreservesZeroEntries (actualSparseSharedMatrix P e) C'}) :
    Papers.Polytopes.RationallyApproximable P :=
  rationallyApproximable_of_relation_matrix_density P hP e (actualSparseSharedMatrix P e)
    (actualSparseSharedMatrix_mul_zero P e) (actualSparseSharedMatrix_spans_facetMasks P e) hC

theorem actualSparseSharedRow_nonzeros {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    totalNonzeros (actualSparseSharedRow P e) ≤
      4 * (∑ R : Face P 2, (actualPolygonSparseBasis P e R).count) +
      5 * (∑ F : Face P 3, (actualFacetSparseSupplement P e F).count) := by
  unfold totalNonzeros
  change (∑ i : (Σ R : Face P 2, Fin (actualPolygonSparseBasis P e R).count) ⊕
    (Σ F : Face P 3, Fin (actualFacetSparseSupplement P e F).count),
    (vectorSupport (actualSparseSharedRow P e i)).card) ≤ _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma, actualSparseSharedRow]
  apply add_le_add
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro R _
    calc
      _ ≤ ∑ _i : Fin (actualPolygonSparseBasis P e R).count, 4 :=
        Finset.sum_le_sum (fun i _ => (actualPolygonSparseBasis P e R).sparse i)
      _ = _ := by simp [mul_comm]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro F _
    calc
      _ ≤ ∑ _i : Fin (actualFacetSparseSupplement P e F).count, 5 :=
        Finset.sum_le_sum (fun i _ => (actualFacetSparseSupplement P e F).sparse i)
      _ = _ := by simp [mul_comm]

theorem actualSparseSharedMatrix_nonzeros {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) :
    (totalNonzeros (actualSparseSharedMatrix P e) : ℤ) ≤
      5 * Fintype.card (SparseSharedRowIndex P e) - polygonExcess P := by
  have heq : totalNonzeros (actualSparseSharedMatrix P e) =
      totalNonzeros (actualSparseSharedRow P e) := by
    exact Fintype.sum_equiv ((Fintype.equivFin (SparseSharedRowIndex P e)).symm)
      _ _ (fun _ => rfl)
  have h := actualSparseSharedRow_nonzeros P e
  have hZ : (totalNonzeros (actualSparseSharedRow P e) : ℤ) ≤
      4 * (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) +
      5 * (∑ F : Face P 3, ((actualFacetSparseSupplement P e F).count : ℤ)) := by
    exact_mod_cast h
  have hg : (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) =
      polygonExcess P := by
    simp only [actualPolygonSparseBasis_count, polygonExcess]
  have hc : (Fintype.card (SparseSharedRowIndex P e) : ℤ) =
      (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) +
      (∑ F : Face P 3, ((actualFacetSparseSupplement P e F).count : ℤ)) := by
    simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma,
      Fintype.card_fin, Nat.cast_add, Nat.cast_sum]
  rw [heq]
  linarith only [hZ, hg, hc]

/-- The support-count step of Appendix A.4. The last hypothesis is the
specific support property supplied by identification of the golden kernel. -/
theorem actualSparseSharedMatrix_at_most_nine_active_columns {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hg : 0 < polygonExcess P)
    (hfour : ∀ j ∈ activeColumns (actualSparseSharedMatrix P e),
      4 ≤ (columnSupport (actualSparseSharedMatrix P e) j).card) :
    (activeColumns (actualSparseSharedMatrix P e)).card ≤ 9 := by
  have hnnz := actualSparseSharedMatrix_nonzeros P e
  have hcol := four_mul_activeColumns_le (actualSparseSharedMatrix P e) hfour
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/ActualEightVertexDensity.lean -/



@[expose] public section

/-!
# The complete at-most-eight-vertex base case

Transposition applies the proved eight-row, non-rank-four matrix-density
theorem to the vertex columns. The actual relation matrix has rank at most
three because it annihilates five independent homogeneous coordinates.
The conclusion controls all extreme vertices of every realization.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem zero_pattern_rank_density_transpose {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (hC : C.transpose ∈ closure
      {D : Matrix (Fin n) (Fin c) ℝ |
        RationalCoordinates D ∧ D.rank = C.transpose.rank ∧
        PreservesZeroEntries C.transpose D}) :
    C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D} := by
  have hi := mem_closure_image continuous_id.matrix_transpose.continuousAt hC
  have he : C.transpose.transpose = C := Matrix.transpose_transpose C
  dsimp only [id] at hi
  rw [he] at hi
  apply closure_mono (s := Matrix.transpose '' _) ?_ hi
  rintro _ ⟨D, hD, rfl⟩
  refine ⟨rationalCoordinates_transpose hD.1, ?_, ?_⟩
  · simpa only [Matrix.rank_transpose] using hD.2.1
  · intro i j hij
    exact hD.2.2 j i hij

theorem actual_polytope_at_most_eight_vertices_approximable
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 8) : RationallyApproximable P := by
  let e : Fin (Fintype.card P.vertices) ≃ P.vertices := (Fintype.equivFin _).symm
  have hn' : Fintype.card P.vertices ≤ 8 := by
    simpa only [Fintype.card_coe] using hn
  have hr := actualSharedMatrix_rank_bound P hP e
  have hr4 : (actualSharedMatrix P e).transpose.rank ≠ 4 := by
    rw [Matrix.rank_transpose]
    omega
  apply rationallyApproximable_of_actualSharedMatrix_density P hP e
  exact zero_pattern_rank_density_transpose _
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hn' _ hr4)

/-- The density statement quantifies over every realization of the face lattice,
not only the supplied coordinates. -/
theorem actual_polytope_at_most_eight_vertices_rationallyDense
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 8) : Papers.Polytopes.RationallyDense P := by
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hQn : Q.vertices.card ≤ 8 := by
    rw [← faceOrderIso_vertex_card φ]
    exact hn
  exact actual_polytope_at_most_eight_vertices_approximable Q hQ hQn

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/NineVertexBudget.lean -/




@[expose] public section

/-!
# The exact numerical reduction for nine vertices

These statements use the selected matrix of the actual polytope. They
isolate the three Appendix A.3 count cases after the polar-core reduction.
No exceptional chart or boundary-enumeration hypothesis is concealed in
the conclusions.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFaceNonedges

local instance faceFintype (P : ConvexPolytope 4) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem actual_nine_vertex_shared_count_bound {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 9) :
    (Fintype.card (ActualSharedRowIndex P e) : ℤ) ≤
      27 - Nat.card (Face P 3) - facetExcess P := by
  have h := actualSharedRowIndex_count_bound P hP e
  rw [hn] at h
  norm_num only [show Nat.choose 9 2 = 36 by decide, Nat.cast_ofNat] at h
  omega

theorem actual_nine_vertex_budget_trichotomy {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 9) (hm : 9 ≤ Nat.card (Face P 3))
    (hE : 9 ≤ facetExcess P) (hc : 8 ≤ Fintype.card (ActualSharedRowIndex P e)) :
    (Nat.card (Face P 3) = 9 ∧ facetExcess P = 9) ∨
      (Nat.card (Face P 3) = 9 ∧ facetExcess P = 10) ∨
      (Nat.card (Face P 3) = 10 ∧ facetExcess P = 9) := by
  have h := actual_nine_vertex_shared_count_bound P hP e hn
  omega

theorem actual_nine_vertex_nine_excess_positive_polygons
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 10)
    (hE : facetExcess P = 9) : 1 ≤ polygonExcess P := by
  let e : Fin (Fintype.card P.vertices) ≃ P.vertices := (Fintype.equivFin _).symm
  have hD := (actual_polygon_relation_budget P hP e).1
  have he := actual_excess_identity P hP
  rw [hn, hm, hE] at he
  norm_num only [show Nat.choose 9 2 = 36 by decide, Nat.cast_ofNat] at he
  omega

/-- Outside the three explicit count pairs the proved seven-row theorem
already gives actual labelled rational approximation. -/
theorem actual_nine_vertex_density_outside_budget_cases {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 9) (hm : 9 ≤ Nat.card (Face P 3))
    (hE : 9 ≤ facetExcess P)
    (hexcluded : ¬((Nat.card (Face P 3) = 9 ∧ facetExcess P = 9) ∨
      (Nat.card (Face P 3) = 9 ∧ facetExcess P = 10) ∨
      (Nat.card (Face P 3) = 10 ∧ facetExcess P = 9))) :
    RationallyApproximable P := by
  apply actual_polytope_seven_shared_relations P hP e
  by_contra hc
  exact hexcluded (actual_nine_vertex_budget_trichotomy P hP e hn hm hE (by omega))

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/NineBipyramidIncidence.lean -/



@[expose] public section

/-!
# Actual incidence counts in the nine-bipyramid obstruction

The minimum five incident facets is derived from nonsimplicity using an
actual vertex figure. Exact totals then force five facets and six edges at
every vertex. These are geometric inputs to either the finite boundary
refutation or the nonedge-cycle argument of Appendix A.3.


-/

noncomputable section
namespace Papers.RationalityTen.NineBipyramidIncidence

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeSmallFacetBounds
open Papers.PolytopeEulerThree Papers.PolytopeEulerFour
open Papers.PolytopeRelationBudget Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation

local instance faceFintype {d : ℕ} (P : ConvexPolytope d) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem vertexGraph_eq_polytopeGraph {d : ℕ} (P : ConvexPolytope d) :
    vertexGraph P = polytopeGraph P := by
  ext u v
  constructor
  · rintro ⟨hv, huv, F, hF, hdF, huF, hvF⟩
    exact ⟨fun h => huv (congrArg Subtype.val h), F, hF, hdF, huF, hvF⟩
  · rintro ⟨huv, F, hF, hdF, huF, hvF⟩
    exact ⟨v.property, fun h => huv (Subtype.ext h), F, hF, hdF, huF, hvF⟩

theorem three_dimensional_vertex_bound {d : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 3) : P.vertices.card + 4 ≤ 2 * Nat.card (Face P 2) := by
  have he := euler_three P hP
  have hi := vertex_edge_bound P hP
  omega

theorem vertex_degree_facet_incidence_bound {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (v : P.vertices) :
    (vertexGraph P).degree v + 4 ≤ 2 * Nat.card (IncidentFace P v.val 3) := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have hD : D.figure.dim = 3 := figure_dim D v.property 3 hP
  have hb := three_dimensional_vertex_bound D.figure hD
  have hfaces := Nat.card_congr (incidentFigureEquiv D 2)
  have hvertices := Nat.card_congr (neighborEquiv D v.property)
  have hdegree := degree_eq_actual_neighbors P v
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hvertices
  rw [← hfaces, ← hvertices, ← hdegree] at hb
  exact hb

theorem nonsimple_vertex_incident_facet_count {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (v : P.vertices)
    (hv : ¬IsSimpleVertex P v) :
    5 ≤ Nat.card (IncidentFace P v.val 3) := by
  have hdegree := degree_ge_dim P v
  have hbound := vertex_degree_facet_incidence_bound P hP v
  have hne : (vertexGraph P).degree v ≠ 4 := by
    intro h
    apply hv
    change (polytopeGraph P).degree v = P.dim
    rw [← vertexGraph_eq_polytopeGraph P, h, hP]
  rw [hP] at hdegree
  omega

theorem nine_five_vertex_facets_force_five_incident {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v) :
    ∀ v : P.vertices, Nat.card (IncidentFace P v.val 3) = 5 := by
  have hsum := sum_vertex_incident_faces P 3
  simp_rw [hfacet] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have hright : (∑ _F : Face P 3, (5 : ℤ)) = 45 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hm]
    norm_num
  rw [hright] at hsum
  have hleft : (∑ _v : P.vertices, (5 : ℤ)) = 45 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, hn]
    norm_num
  have hmin : ∀ v : P.vertices, (5 : ℤ) ≤ Nat.card (IncidentFace P v.val 3) := by
    intro v
    exact_mod_cast nonsimple_vertex_incident_facet_count P hP v (hnonsimple v)
  have heq := (Finset.sum_eq_sum_iff_of_le (fun v _ => hmin v)).mp
    (hleft.trans hsum.symm)
  intro v
  have h := heq v (Finset.mem_univ _)
  exact_mod_cast h.symm

theorem nine_bipyramid_edge_and_degree_counts {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (hg : polygonExcess P = 0)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v) :
    Nat.card (Face P 1) = 27 ∧
      (∀ v : P.vertices, Nat.card (IncidentFace P v.val 3) = 5) ∧
      (∀ v : P.vertices, (vertexGraph P).degree v = 6) := by
  have hinc := nine_five_vertex_facets_force_five_incident P hP hn hm hfacet hnonsimple
  have hE : facetExcess P = 9 := by
    simp only [facetExcess, hfacet, Nat.cast_ofNat]
    norm_num only [show (5 : ℤ) - 4 = 1 by norm_num]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hm]
    norm_num
  have he := actual_excess_identity P hP
  rw [hn, hm, hE, hg] at he
  norm_num only [show Nat.choose 9 2 = 36 by decide, Nat.cast_ofNat] at he
  have hnonedge : Nat.card (Nonedge P) = 9 := by omega
  have hpairs := nonedge_card_add_edge_card P
  rw [hn, hnonedge] at hpairs
  have hedges : Nat.card (Face P 1) = 27 := by
    norm_num only [show Nat.choose 9 2 = 36 by decide] at hpairs
    omega
  have hle : ∀ v : P.vertices, (vertexGraph P).degree v ≤ 6 := by
    intro v
    have h := vertex_degree_facet_incidence_bound P hP v
    rw [hinc v] at h
    omega
  have hsum := (vertexGraph P).sum_degrees_eq_twice_card_edges
  have hecard : (vertexGraph P).edgeFinset.card = 27 := by
    rw [← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card,
      graph_edge_card_eq_one_face_card, hedges]
  rw [hecard] at hsum
  have hconst : (∑ _v : P.vertices, 6) = 2 * 27 := by simp [hn]
  have hdegrees := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp
    (hsum.trans hconst.symm)
  exact ⟨hedges, hinc, fun v => hdegrees v (Finset.mem_univ _)⟩

theorem nine_bipyramid_nonedge_degree_two {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (hg : polygonExcess P = 0)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v) :
    ∀ v : P.vertices, (vertexGraph P)ᶜ.degree v = 2 := by
  have hdegree := (nine_bipyramid_edge_and_degree_counts P hP hn hm hfacet hg hnonsimple).2.2
  intro v
  rw [SimpleGraph.degree_compl, hdegree v]
  simp only [Fintype.card_coe, hn]

end Papers.RationalityTen.NineBipyramidIncidence

end
end
end BundlePart18

section BundlePart19
/- Source: Papers/PolytopeCyclicLabeling.lean -/





@[expose] public section

/-!
# Cyclic labellings of actual convex polygons

A finite connected graph of degree two is isomorphic to
the ordinary cycle graph on all its vertices. The injective Hamiltonian
copy is proved to reflect edges by a bijection of the two-element
neighbor sets. Thus the cycle records every edge, without chords.
-/

noncomputable section

namespace Papers.PolytopeCyclicLabeling

open SimpleGraph
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeBalinski Papers.PolytopeEulerLocal
open Papers.PolytopePolygonCycle
open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

theorem surjective_of_injective_equal_card
    (f : V → W) (hf : Function.Injective f)
    (hcard : Fintype.card V = Fintype.card W) : Function.Surjective f := by
  by_contra hn
  have hlt := Fintype.card_lt_of_injective_not_surjective f hf hn
  omega

def isoOfCopyDegrees (f : Copy G H) (hsurj : Function.Surjective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v)) : G ≃g H where
  toEquiv := Equiv.ofBijective f ⟨f.injective,hsurj⟩
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy
      let g := f.mapNeighborSet x
      have hgcard : Fintype.card (G.neighborSet x) =
          Fintype.card (H.neighborSet (f x)) := by
        rw [SimpleGraph.card_neighborSet_eq_degree,
          SimpleGraph.card_neighborSet_eq_degree,hdegree]
      have hgsurj := surjective_of_injective_equal_card g g.injective hgcard
      obtain ⟨z,hz⟩ := hgsurj ⟨f y,hxy⟩
      have hzy : z.val = y := f.injective (congrArg Subtype.val hz)
      exact hzy ▸ z.property
    · exact f.toHom.map_adj

theorem cycleGraph_degree_eq_two (N : ℕ) (hN : 3 ≤ N) (i : Fin N) :
    (cycleGraph N).degree i = 2 := by
  obtain ⟨k,rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3,by omega⟩
  exact cycleGraph_degree_three_le

theorem exists_cycleGraph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2) :
    Nonempty (cycleGraph (Fintype.card V) ≃g G) := by
  obtain ⟨v,c,hc⟩ := exists_hamiltonian_cycle_of_degree_two G hconn hdeg
  have hcard : 3 ≤ Fintype.card V := by
    have h := hc.isCycle.three_le_length
    rw [hc.length_eq] at h
    exact h
  obtain ⟨f⟩ := (cycleGraph_isContained_iff hcard).mpr
    ⟨v,c,hc.isCycle,hc.length_eq⟩
  have hf := surjective_of_injective_equal_card f f.injective (by simp)
  exact ⟨isoOfCopyDegrees f hf (fun i => by
    rw [cycleGraph_degree_eq_two _ hcard,hdeg])⟩

variable {n : ℕ}

/-- All actual vertices of a genuine convex polygon have an exact cyclic
labelling preserving and reflecting ordinary polytope edge adjacency. -/
theorem actual_polygon_cyclic_labeling (P : ConvexPolytope n)
    (hdim : P.dim = 2) :
    Nonempty (cycleGraph P.vertices.card ≃g vertexGraph P) := by
  have h := exists_cycleGraph_iso (vertexGraph P)
    (vertexGraph_connected P) (polygon_vertex_degree_two P hdim)
  have hc : Fintype.card P.vertices = P.vertices.card := Fintype.card_coe _
  rw [hc] at h
  exact h

end Papers.PolytopeCyclicLabeling

end
end
end BundlePart19

section BundlePart20
/- Source: Papers/NineBipyramidCycle.lean -/




@[expose] public section

/-!
# The parity and cyclic parts of the nine-bipyramid contradiction

The connectedness argument sums a family of selected-edge degrees over a
union of components. A label inside the union gives an odd total, whereas
a label outside gives an even total. After cyclic relabeling, nine linear
equations force four labels into the intersection of two distinct facets.


-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Papers.RationalityTen.NineBipyramidCycle

open Set SimpleGraph
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A closed vertex subset has an even sum of degrees in every subgraph. -/
theorem degree_sum_on_closed_subset_even (G H : SimpleGraph V)
    (hHG : H ≤ G) (S : Finset V)
    (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S) :
    ∃ a : ℕ, (∑ v : S, H.degree v.val) = 2 * a := by
  let J : SimpleGraph S := H.induce (↑S : Set V)
  have hdegree (v : S) : J.degree v = H.degree v.val := by
    let e : J.neighborSet v ≃ H.neighborSet v.val := {
      toFun w := ⟨w.val.val, w.property⟩
      invFun w := ⟨⟨w.val, hclosed v.val v.property w.val (hHG w.property)⟩, w.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e
  refine ⟨J.edgeFinset.card, ?_⟩
  calc
    (∑ v : S, H.degree v.val) = ∑ v : S, J.degree v :=
      Finset.sum_congr rfl (fun v _ => (hdegree v).symm)
    _ = 2 * J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges

theorem sum_single_label (S : Finset V) (k : V) :
    (∑ v : S, if v.val = k then (1 : ℕ) else 0) = if k ∈ S then 1 else 0 := by
  by_cases hk : k ∈ S
  · let x : S := ⟨k, hk⟩
    have heq (v : S) : (v.val = k) ↔ v = x := by
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [heq, if_pos hk]
    simp
  · have hne (v : S) : v.val ≠ k := by
      intro h
      exact hk (h ▸ v.property)
    simp only [hne, if_false, Finset.sum_const_zero, if_neg hk]

/-- The local prism partition makes the nonedge graph connected. This
lemma does not enumerate possible cycle-length partitions. -/
theorem connected_of_label_degree_family [Nonempty V]
    (G : SimpleGraph V) (H : V → SimpleGraph V)
    (hsub : ∀ k, H k ≤ G)
    (hdegree : ∀ k v, (H k).degree v = 1 + if v = k then 1 else 0) :
    G.Connected := by
  refine { preconnected := ?_ }
  intro u w
  by_contra hn
  let S := Finset.univ.filter (fun v => G.Reachable u v)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Reachable.refl u⟩
  have hwS : w ∉ S := fun h => hn (Finset.mem_filter.mp h).2
  have hclosed : ∀ v ∈ S, ∀ z, G.Adj v z → z ∈ S := by
    intro v hv z hvz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hvz.reachable⟩
  have hsum (k : V) : (∑ v : S, (H k).degree v.val) =
      S.card + if k ∈ S then 1 else 0 := by
    simp_rw [hdegree]
    rw [Finset.sum_add_distrib, sum_single_label]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_id]
  obtain ⟨a, ha⟩ := degree_sum_on_closed_subset_even G (H u) (hsub u) S hclosed
  obtain ⟨b, hb⟩ := degree_sum_on_closed_subset_even G (H w) (hsub w) S hclosed
  rw [hsum u, if_pos huS] at ha
  rw [hsum w, if_neg hwS] at hb
  omega

def memberIndicator (F : Finset (Fin 9)) (k : Fin 9) : ℤ := if k ∈ F then 1 else 0

private theorem cyclic_intersection_forced (F : Fin 9 → Finset (Fin 9))
    (hlocal : ∀ v k : Fin 9,
      memberIndicator (F (v - 1)) k + memberIndicator (F v) k =
        if k = v then 2 else 1)
    (k : Fin 9) (hk : k = 0 ∨ k = 3 ∨ k = 5 ∨ k = 7) :
    k ∈ F 0 ∧ k ∈ F 2 := by
  have hpred : (0 : Fin 9) - 1 = 8 := by decide
  have h0 := hlocal 0 k
  rw [hpred] at h0
  have h1 := hlocal 1 k
  have h2 := hlocal 2 k
  have h3 := hlocal 3 k
  have h4 := hlocal 4 k
  have h5 := hlocal 5 k
  have h6 := hlocal 6 k
  have h7 := hlocal 7 k
  have h8 := hlocal 8 k
  have hforced : memberIndicator (F 0) k = 1 ∧ memberIndicator (F 2) k = 1 := by
    rcases hk with rfl | rfl | rfl | rfl <;>
      norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 <;> omega
  constructor
  · by_contra hh
    simp only [memberIndicator, if_neg hh] at hforced
    omega
  · by_contra hh
    simp only [memberIndicator, if_neg hh] at hforced
    omega

theorem no_nine_cycle_facet_family (F : Fin 9 → Finset (Fin 9))
    (hlocal : ∀ v k : Fin 9,
      memberIndicator (F (v - 1)) k + memberIndicator (F v) k =
        if k = v then 2 else 1)
    (hinter : ∀ i j : Fin 9, i ≠ j → (F i ∩ F j).card ≤ 3) : False := by
  have hsub : ({0, 3, 5, 7} : Finset (Fin 9)) ⊆ F 0 ∩ F 2 := by
    intro k hk
    have hk' : k = 0 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by simpa using hk
    exact Finset.mem_inter.mpr (cyclic_intersection_forced F hlocal k hk')
  have hlarge := Finset.card_le_card hsub
  have hsmall := hinter 0 2 (by decide)
  norm_num at hlarge
  omega

end Papers.RationalityTen.NineBipyramidCycle

end
end
end BundlePart20

section BundlePart21
/- Source: Papers/CubicSixTriangles.lean -/





@[expose] public section

/-!
# Disjoint triangular faces in a cubic six-vertex graph

The graph lemma is stronger than the prism application: connectedness is
not needed. If two triangles share an edge, its endpoints have all three
neighbors already. The remaining two vertices then force a fourth neighbor
at another triangle vertex.


-/

noncomputable section
namespace Papers.RationalityTen.CubicSixTriangles

open Set SimpleGraph
open scoped Classical

private theorem neighbor_triple (G : SimpleGraph (Fin 6)) (v : Fin 6)
    (hdeg : G.degree v = 3) (T : Finset (Fin 6)) (hT : T.card = 3)
    (hsub : T ⊆ G.neighborFinset v) : G.neighborFinset v = T := by
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hT]

theorem no_two_triangles_shared_edge_fin_six (G : SimpleGraph (Fin 6))
    (hdegree : ∀ v, G.degree v = 3)
    (h01 : G.Adj 0 1) (h02 : G.Adj 0 2) (h12 : G.Adj 1 2)
    (h03 : G.Adj 0 3) (h13 : G.Adj 1 3) : False := by
  have hN0 : G.neighborFinset 0 = {1, 2, 3} := by
    apply neighbor_triple G 0 (hdegree 0) _ (by decide)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr h01
    · exact (G.mem_neighborFinset _ _).mpr h02
    · exact (G.mem_neighborFinset _ _).mpr h03
  have hN1 : G.neighborFinset 1 = {0, 2, 3} := by
    apply neighbor_triple G 1 (hdegree 1) _ (by decide)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr h01.symm
    · exact (G.mem_neighborFinset _ _).mpr h12
    · exact (G.mem_neighborFinset _ _).mpr h13
  have h04 : ¬G.Adj 0 4 := by
    intro h
    have hh := (G.mem_neighborFinset _ _).mpr h
    rw [hN0] at hh
    norm_num at hh
  have h05 : ¬G.Adj 0 5 := by
    intro h
    have hh := (G.mem_neighborFinset _ _).mpr h
    rw [hN0] at hh
    norm_num at hh
  have h14 : ¬G.Adj 1 4 := by
    intro h
    have hh := (G.mem_neighborFinset _ _).mpr h
    rw [hN1] at hh
    norm_num at hh
  have h15 : ¬G.Adj 1 5 := by
    intro h
    have hh := (G.mem_neighborFinset _ _).mpr h
    rw [hN1] at hh
    norm_num at hh
  have hN4 : G.neighborFinset 4 = {2, 3, 5} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have h := (G.mem_neighborFinset _ _).mp hx
      fin_cases x
      · exact (h04 h.symm).elim
      · exact (h14 h.symm).elim
      · decide
      · decide
      · exact (G.irrefl h).elim
      · decide
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree]
      decide
  have hN5 : G.neighborFinset 5 = {2, 3, 4} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have h := (G.mem_neighborFinset _ _).mp hx
      fin_cases x
      · exact (h05 h.symm).elim
      · exact (h15 h.symm).elim
      · decide
      · decide
      · decide
      · exact (G.irrefl h).elim
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree]
      decide
  have h24 : G.Adj 2 4 := ((G.mem_neighborFinset _ _).mp (by rw [hN4]; decide)).symm
  have h25 : G.Adj 2 5 := ((G.mem_neighborFinset _ _).mp (by rw [hN5]; decide)).symm
  have hsub : ({0, 1, 4, 5} : Finset (Fin 6)) ⊆ G.neighborFinset 2 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr h02.symm
    · exact (G.mem_neighborFinset _ _).mpr h12.symm
    · exact (G.mem_neighborFinset _ _).mpr h24
    · exact (G.mem_neighborFinset _ _).mpr h25
  have hc := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree] at hc
  norm_num at hc

theorem no_two_triangles_shared_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : Fintype.card V = 6)
    (hdegree : ∀ v, G.degree v = 3)
    (f : Fin 4 → V) (hf : Function.Injective f)
    (h01 : G.Adj (f 0) (f 1)) (h02 : G.Adj (f 0) (f 2))
    (h12 : G.Adj (f 1) (f 2)) (h03 : G.Adj (f 0) (f 3))
    (h13 : G.Adj (f 1) (f 3)) : False := by
  let lab0 : V ≃ Fin 6 := (Fintype.equivFin V).trans (finCongr hcard)
  let inc : Fin 4 → Fin 6 := Fin.castLE (by decide)
  have hinc : Function.Injective inc := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 6 => x.val) h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (lab0 ∘ f) inc
    (lab0.injective.comp hf) hinc
  let lab := lab0.trans σ
  have hpre (i : Fin 4) : lab.symm (inc i) = f i := by
    have h : lab (f i) = inc i := hσ i
    rw [← h, lab.symm_apply_apply]
  have h0 : lab.symm 0 = f 0 := hpre 0
  have h1 : lab.symm 1 = f 1 := hpre 1
  have h2 : lab.symm 2 = f 2 := hpre 2
  have h3 : lab.symm 3 = f 3 := hpre 3
  let H := G.comap lab.symm
  have hH (i : Fin 6) : H.degree i = 3 := by
    rw [← (SimpleGraph.Iso.comap lab.symm G).degree_eq]
    exact hdegree _
  apply no_two_triangles_shared_edge_fin_six H hH
  · change G.Adj (lab.symm 0) (lab.symm 1)
    simpa only [h0, h1] using h01
  · change G.Adj (lab.symm 0) (lab.symm 2)
    simpa only [h0, h2] using h02
  · change G.Adj (lab.symm 1) (lab.symm 2)
    simpa only [h1, h2] using h12
  · change G.Adj (lab.symm 0) (lab.symm 3)
    simpa only [h0, h3] using h03
  · change G.Adj (lab.symm 1) (lab.symm 3)
    simpa only [h1, h3] using h13

/-- Distinct triangular cliques in a cubic graph on six vertices are
disjoint. In the vertex-figure application the cliques are the two
triangular facets, but this statement does not require a planar embedding. -/
theorem triangular_cliques_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : Fintype.card V = 6)
    (hdegree : ∀ v, G.degree v = 3)
    (A B : Finset V) (hA : A.card = 3) (hB : B.card = 3)
    (hclA : G.IsClique (↑A : Set V)) (hclB : G.IsClique (↑B : Set V))
    (hne : A ≠ B) : Disjoint A B := by
  by_contra hdis
  obtain ⟨u, hu⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hdis
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  have hnotAB : ¬A ⊆ B := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h (by omega))
  have hnotBA : ¬B ⊆ A := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
  obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr hnotAB
  obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hnotBA
  obtain ⟨haA, haB⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hbB, hbA⟩ := Finset.mem_sdiff.mp hb
  have hcardA : (A.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem huA, hA]
  have hcardB : (B.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem huB, hB]
  have hsub : A.erase u ∪ B.erase u ⊆ G.neighborFinset u := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxu, hxA⟩ := Finset.mem_erase.mp hx
      exact (G.mem_neighborFinset _ _).mpr (hclA huA hxA hxu.symm)
    · obtain ⟨hxu, hxB⟩ := Finset.mem_erase.mp hx
      exact (G.mem_neighborFinset _ _).mpr (hclB huB hxB hxu.symm)
  have hbound := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree u] at hbound
  have hsum := Finset.card_union_add_card_inter (A.erase u) (B.erase u)
  rw [hcardA, hcardB] at hsum
  have hpos : 0 < (A.erase u ∩ B.erase u).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvu, hvA⟩ := Finset.mem_erase.mp hvA
  have hvB := (Finset.mem_erase.mp hvB).2
  have hua : u ≠ a := by rintro rfl; exact haB huB
  have hub : u ≠ b := by rintro rfl; exact hbA huA
  have hva : v ≠ a := by rintro rfl; exact haB hvB
  have hvb : v ≠ b := by rintro rfl; exact hbA hvA
  have hab : a ≠ b := by rintro rfl; exact haB hbB
  let f : Fin 4 → V := ![u, v, a, b]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  apply no_two_triangles_shared_edge G hcard hdegree f hf
  · exact hclA huA hvA hvu.symm
  · exact hclA huA haA hua
  · exact hclA hvA haA hva
  · exact hclB huB hbB hub
  · exact hclB hvB hbB hvb

end Papers.RationalityTen.CubicSixTriangles

end
end
end BundlePart21

section BundlePart22
/- Source: Papers/SimplicialFiveFacetGeometry.lean -/



@[expose] public section

/-!
# Five-vertex simplicial facets and their unique nonedge

This part of the nine-vertex argument uses Euler counting directly. A
three-dimensional simplicial polytope with five vertices has nine edges
and exactly one nonedge. Thus its two apices are defined intrinsically,
without an assumed boundary catalogue.


-/

noncomputable section
namespace Papers.RationalityTen.SimplicialFiveFacetGeometry

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeEulerThree
open Papers.PolytopeRelationBudget Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation Papers.PolytopeLabelledBoundary

variable {d : ℕ}

theorem faceCode_card (P : ConvexPolytope d) (k : ℕ) (F : Face P k) :
    (faceCode P k F).card = Nat.card (VerticesOn P F.val.carrier) := by
  simp only [faceCode, VerticesOn, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem polygonExcess_zero_iff (P : ConvexPolytope d) :
    polygonExcess P = 0 ↔
      ∀ R : Face P 2, Nat.card (VerticesOn P R.val.carrier) = 3 := by
  have hnonneg (R : Face P 2) :
      (0 : ℤ) ≤ Nat.card (VerticesOn P R.val.carrier) - 3 := by
    have h := face_vertices_card_ge_dim_add_one P 2 R
    omega
  constructor
  · intro h R
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun R _ => hnonneg R)).mp h R (Finset.mem_univ _)
    omega
  · intro h
    unfold polygonExcess
    simp_rw [h]
    norm_num

def verticesOnFaceEquiv (P : ConvexPolytope d) {F A : Set (E d)}
    (hF : P.IsFace F) (hAF : A ⊆ F) :
    VerticesOn (facePolytope P hF) A ≃ VerticesOn P A where
  toFun v := ⟨⟨v.val.val, (Finset.mem_filter.mp v.val.property).1⟩, v.property⟩
  invFun v := ⟨⟨v.val.val, Finset.mem_filter.mpr
    ⟨v.val.property, hAF v.property⟩⟩, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem facePolytope_polygonExcess_zero (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) {F : Set (E d)} (hF : P.IsFace F) :
    polygonExcess (facePolytope P hF) = 0 := by
  apply (polygonExcess_zero_iff _).mpr
  intro R
  let R' : Face P 2 :=
    ⟨⟨R.val.carrier, isFace_of_facePolytope P hF R.val.isFace⟩, R.property⟩
  have hRF : R.val.carrier ⊆ F := by
    have h := face_subset_toSet (facePolytope P hF) R.val.isFace
    simpa only [facePolytope_toSet] using h
  rw [Nat.card_congr (verticesOnFaceEquiv P hF hRF)]
  exact (polygonExcess_zero_iff P).mp hg R'

theorem triangular_face_clique (P : ConvexPolytope d)
    (R : Face P 2) (hR : Nat.card (VerticesOn P R.val.carrier) = 3) :
    (vertexGraph P).IsClique (↑(faceCode P 2 R) : Set P.vertices) := by
  intro x hx y hy hxy
  by_contra hn
  have hc := polygon_nonedge_count P R
  rw [hR] at hc
  have hzero : Nat.card (NonedgesOn P R.val.carrier) = 0 := by
    norm_num only [Nat.choose] at hc
    omega
  let e : Nonedge P := ⟨s(x, y), (SimpleGraph.compl_adj _ _ _).mpr ⟨hxy, hn⟩⟩
  have he : Within P R.val.carrier e := by
    apply (within_iff P R.val.carrier e).mpr
    intro v hv
    change v ∈ s(x, y) at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
  letI : Nonempty (NonedgesOn P R.val.carrier) := ⟨⟨e, he⟩⟩
  have hp := Nat.card_pos (α := NonedgesOn P R.val.carrier)
  omega

theorem no_polygon_diagonal_of_excess_zero (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) (x y : P.vertices)
    (hne : x ≠ y) (hnon : ¬GeneralVertexStep P x.val y.val) :
    ¬IsPolygonDiagonal P x y := by
  rintro ⟨R, hx, hy⟩
  have hcl := triangular_face_clique P R ((polygonExcess_zero_iff P).mp hg R)
  apply hnon
  apply hcl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  · exact hne

theorem five_vertex_simplicial_unique_nonedge (P : ConvexPolytope d)
    (hP : P.dim = 3) (hn : P.vertices.card = 5)
    (hg : polygonExcess P = 0) : Nat.card (Nonedge P) = 1 := by
  have he := polygon_excess_of_dimension_three P hP
  rw [hg, hn] at he
  have hp := nonedge_card_add_edge_card P
  rw [hn] at hp
  norm_num only [Nat.choose] at hp
  omega

theorem five_vertex_facet_unique_nonedge (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) (F : Face P 3)
    (hF : Nat.card (VerticesOn P F.val.carrier) = 5) :
    Nat.card (NonedgesOn P F.val.carrier) = 1 := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have hn : Q.vertices.card = 5 := by
    have h := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h.symm.trans hF
  rw [← Nat.card_congr (faceNonedgeEquiv P F.val.isFace)]
  exact five_vertex_simplicial_unique_nonedge Q hQ hn
    (facePolytope_polygonExcess_zero P hg F.val.isFace)

theorem nonedge_common_facet_unique_of_excess_zero
    (P : ConvexPolytope d) (hg : polygonExcess P = 0)
    (e : Nonedge P) (A B : Face P 3)
    (hA : Within P A.val.carrier e) (hB : Within P B.val.carrier e) : A = B := by
  by_contra hAB
  obtain ⟨hne, hnon⟩ := nonedge_out P e
  obtain ⟨R, hR⟩ := distinct_common_facets_intersection P _ _ hne hnon
    A B hAB hA.1 hA.2 hB.1 hB.2
  apply no_polygon_diagonal_of_excess_zero P hg _ _ hne hnon
  refine ⟨R, ?_, ?_⟩
  · simpa only [hR, Set.mem_inter_iff] using And.intro hA.1 hB.1
  · simpa only [hR, Set.mem_inter_iff] using And.intro hA.2 hB.2

def facetApexPair (P : ConvexPolytope d) (hg : polygonExcess P = 0)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (F : Face P 3) : NonedgesOn P F.val.carrier :=
  Classical.choose (Nat.card_eq_one_iff_exists.mp
    (five_vertex_facet_unique_nonedge P hg F (hfacet F)))

theorem facetApexPair_unique (P : ConvexPolytope d) (hg : polygonExcess P = 0)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (F : Face P 3) (e : NonedgesOn P F.val.carrier) :
    e = facetApexPair P hg hfacet F :=
  Classical.choose_spec (Nat.card_eq_one_iff_exists.mp
    (five_vertex_facet_unique_nonedge P hg F (hfacet F))) e

theorem facetApexPair_injective (P : ConvexPolytope d) (hg : polygonExcess P = 0)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5) :
    Function.Injective (fun F => (facetApexPair P hg hfacet F).val) := by
  intro A B hab
  apply nonedge_common_facet_unique_of_excess_zero P hg
    (facetApexPair P hg hfacet A).val A B (facetApexPair P hg hfacet A).property
  change (facetApexPair P hg hfacet A).val = (facetApexPair P hg hfacet B).val at hab
  rw [hab]
  exact (facetApexPair P hg hfacet B).property

/-- With nine such facets and nine nonedges, every nonedge is the apex
pair of exactly one actual facet. -/
def facetApexEquiv (P : ConvexPolytope d) (hg : polygonExcess P = 0)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (hcard : Nat.card (Face P 3) = Nat.card (Nonedge P)) :
    Face P 3 ≃ Nonedge P := by
  let f := fun F => (facetApexPair P hg hfacet F).val
  have hf := facetApexPair_injective P hg hfacet
  have hc : Fintype.card (Face P 3) = Fintype.card (Nonedge P) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact Equiv.ofBijective f ⟨hf,
    Papers.PolytopeCyclicLabeling.surjective_of_injective_equal_card f hf hc⟩

theorem face_vertices_le_three_of_dim_le_two (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) {A : Set (E d)} (hA : P.IsFace A)
    (hdim : faceDim A ≤ 2) : Nat.card (VerticesOn P A) ≤ 3 := by
  have hd : faceDim A = 0 ∨ faceDim A = 1 ∨ faceDim A = 2 := by omega
  rcases hd with hd | hd | hd
  · obtain ⟨v, hv, hAv⟩ := actual_zeroFace_is_vertex P A hA hd
    have hc : Nat.card (VerticesOn P A) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨⟨v, hv⟩, by rw [hAv]; exact Set.mem_singleton _⟩, ?_⟩
      intro w
      apply Subtype.ext
      apply Subtype.ext
      have hw := w.property
      have hs : (w.val : E d) ∈ ({v} : Set (E d)) := hAv ▸ hw
      clear hw
      exact Set.mem_singleton_iff.mp hs
    omega
  · have hc := one_face_vertex_card P (⟨⟨A, hA⟩, hd⟩ : Face P 1)
    exact le_of_eq hc |>.trans (by decide)
  · exact le_of_eq ((polygonExcess_zero_iff P).mp hg
      (⟨⟨A, hA⟩, hd⟩ : Face P 2))

theorem distinct_facets_intersection_card_le_three (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) (F G : Face P 3) (hFG : F ≠ G) :
    (faceCode P 3 F ∩ faceCode P 3 G).card ≤ 3 := by
  by_cases hn : (faceCode P 3 F ∩ faceCode P 3 G).Nonempty
  · obtain ⟨v, hv⟩ := hn
    have hvF := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
    have hvG := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    have hI : P.IsFace (F.val.carrier ∩ G.val.carrier) :=
      ⟨F.val.isFace.1.inter G.val.isFace.1, ⟨v.val, hvF, hvG⟩⟩
    have hproper : F.val.carrier ∩ G.val.carrier ⊂ F.val.carrier := by
      refine ⟨Set.inter_subset_left, ?_⟩
      intro hback
      have hsub : F.val.carrier ⊆ G.val.carrier := fun z hz => (hback hz).2
      apply hFG
      exact Subtype.ext (PolytopeFace.ext
        (face_eq_of_subset_equal_dimension P F.val.isFace G.val.isFace
          hsub (F.property.trans G.property.symm)))
    have hdim := faceDim_lt_of_ssubset P hI F.val.isFace hproper
    rw [F.property] at hdim
    let I : Face P (faceDim (F.val.carrier ∩ G.val.carrier)) := ⟨⟨_, hI⟩, rfl⟩
    have hcode : faceCode P _ I = faceCode P 3 F ∩ faceCode P 3 G := by
      ext z
      simp [faceCode, I]
    rw [← hcode, faceCode_card]
    exact face_vertices_le_three_of_dim_le_two P hg hI (by omega)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hempty]
    simp

end Papers.RationalityTen.SimplicialFiveFacetGeometry

end
end
end BundlePart22

section BundlePart23
/- Source: Papers/NineBipyramidLocalPartition.lean -/



@[expose] public section

/-!
# The local partition at an apex of two bipyramidal facets

The two relevant facets in the actual vertex figure are triangular.
Its graph has six vertices and is cubic, so those triangles are disjoint.
Transferring this fact back through the vertex-figure correspondence shows
that the two original five-vertex facets meet only at the chosen vertex.


-/

noncomputable section
namespace Papers.RationalityTen.NineBipyramidLocalPartition

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeEulerThree Papers.PolytopeEulerFour
open Papers.PolytopeRelationBudget Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation
open Papers.RationalityTen.SimplicialFiveFacetGeometry
open Papers.RationalityTen.CubicSixTriangles

variable {d : ℕ}

theorem unique_apex_pair_gives_three_neighbors (P : ConvexPolytope d)
    (hg : polygonExcess P = 0) (F : Face P 3)
    (hF : Nat.card (VerticesOn P F.val.carrier) = 5)
    (x y : P.vertices) (hxy : (vertexGraph P)ᶜ.Adj x y)
    (hxF : x.val ∈ F.val.carrier) (hyF : y.val ∈ F.val.carrier) :
    ((faceCode P 3 F).filter fun z => (vertexGraph P).Adj x z).card = 3 := by
  obtain ⟨hxyne, hxynon⟩ := (SimpleGraph.compl_adj _ _ _).mp hxy
  let e : Nonedge P := ⟨s(x, y), hxy⟩
  have he : Within P F.val.carrier e := by
    apply (within_iff P F.val.carrier e).mpr
    intro v hv
    change v ∈ s(x, y) at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  have hss : Subsingleton (NonedgesOn P F.val.carrier) :=
    (Nat.card_eq_one_iff_unique.mp (five_vertex_facet_unique_nonedge P hg F hF)).1
  have hother (z : P.vertices) (hzF : z.val ∈ F.val.carrier)
      (hzx : z ≠ x) (hzy : z ≠ y) : (vertexGraph P).Adj x z := by
    by_contra hn
    let e' : Nonedge P :=
      ⟨s(x, z), (SimpleGraph.compl_adj _ _ _).mpr ⟨hzx.symm, hn⟩⟩
    have he' : Within P F.val.carrier e' := by
      apply (within_iff P F.val.carrier e').mpr
      intro v hv
      change v ∈ s(x, z) at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
    have h := hss.elim (⟨e', he'⟩ : NonedgesOn P F.val.carrier) ⟨e, he⟩
    have hs : s(x, z) = s(x, y) := congrArg (fun a => a.val.val) h
    rcases Sym2.eq_iff.mp hs with ⟨_, hzy'⟩ | ⟨hxy', _⟩
    · exact hzy hzy'
    · exact hxyne hxy'
  have hfilter : (faceCode P 3 F).filter (fun z => (vertexGraph P).Adj x z) =
      ((faceCode P 3 F).erase x).erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hzF, hxz⟩
      refine ⟨?_, ?_, hzF⟩
      · intro h
        subst z
        exact hxynon hxz
      · exact fun h => (vertexGraph P).irrefl (h ▸ hxz)
    · rintro ⟨hzy, hzx, hzF⟩
      exact ⟨hzF, hother z (Finset.mem_filter.mp hzF).2 hzx hzy⟩
  have hx : x ∈ faceCode P 3 F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxF⟩
  have hy : y ∈ (faceCode P 3 F).erase x := Finset.mem_erase.mpr
    ⟨hxyne.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyF⟩⟩
  rw [hfilter, Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx,
    faceCode_card, hF]

theorem neighborImage_mem_incidentFigure_iff {P : ConvexPolytope d} {x : E d}
    (D : VertexFigureGaloisData P P.toSet x) (hx : x ∈ P.vertices)
    (k : ℕ) (F : IncidentFace P x (k + 1)) (y : actualNeighbors P x) :
    (neighborImage D hx y).val ∈ ((incidentFigureEquiv D k) F).val.carrier ↔
      y.val ∈ F.val.val.carrier := by
  constructor
  · intro h
    have hsub : (D.faceEquiv (neighborStarFace P hx y)).carrier ⊆
        (D.faceEquiv (incidentStar P x k F)).carrier := by
      rw [neighborImage_face]
      exact Set.singleton_subset_iff.mpr h
    have hpre := (D.map_subset_iff (neighborStarFace P hx y)
      (incidentStar P x k F)).mpr hsub
    exact hpre (right_mem_segment ℝ _ _)
  · intro h
    have hconv : Convex ℝ F.val.val.carrier :=
      F.val.val.isFace.1.convex (convex_convexHull ℝ _)
    have hsub : (neighborStarFace P hx y).carrier ⊆ (incidentStar P x k F).carrier :=
      hconv.segment_subset F.property h
    have himage := (D.map_subset_iff (neighborStarFace P hx y)
      (incidentStar P x k F)).mp hsub
    apply himage
    rw [neighborImage_face]
    exact Set.mem_singleton _

def faceNeighborFigureEquiv {P : ConvexPolytope d} (x : P.vertices)
    (D : VertexFigureGaloisData P P.toSet x.val) (k : ℕ)
    (F : IncidentFace P x.val (k + 1)) :
    ((faceCode P (k + 1) F.val).filter fun z => (vertexGraph P).Adj x z) ≃
      VerticesOn D.figure ((incidentFigureEquiv D k) F).val.carrier where
  toFun z := by
    have hz := Finset.mem_filter.mp z.property
    let y := asNeighbor P z.val hz.2
    refine ⟨neighborImage D x.property y, ?_⟩
    exact (neighborImage_mem_incidentFigure_iff D x.property k F y).mpr
      (Finset.mem_filter.mp hz.1).2
  invFun q := by
    let y := (neighborEquiv D x.property).symm q.val
    have hy : y.val ∈ F.val.val.carrier := by
      apply (neighborImage_mem_incidentFigure_iff D x.property k F y).mp
      have h : neighborImage D x.property y = q.val :=
        (neighborEquiv D x.property).apply_symm_apply q.val
      rw [h]
      exact q.property
    exact ⟨neighborVertex P x.val y, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, neighbor_step P x.val y⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : Papers.PolytopeVertexCone.actualNeighbors P x.val => y.val) ((neighborEquiv D x.property).symm_apply_apply
      (asNeighbor P z.val (Finset.mem_filter.mp z.property).2))
  right_inv q := by
    apply Subtype.ext
    exact (neighborEquiv D x.property).apply_symm_apply q.val

theorem cubic_of_six_vertices_five_facets (P : ConvexPolytope d)
    (hP : P.dim = 3) (hn : P.vertices.card = 6)
    (hf : Nat.card (Face P 2) = 5) :
    ∀ v : P.vertices, (vertexGraph P).degree v = 3 := by
  have heuler := euler_three P hP
  rw [hn, hf] at heuler
  have he : Nat.card (Face P 1) = 9 := by omega
  have hmin (v : P.vertices) : 3 ≤ (vertexGraph P).degree v := by
    simpa only [hP] using degree_ge_dim P v
  have hsum := (vertexGraph P).sum_degrees_eq_twice_card_edges
  have hecard : (vertexGraph P).edgeFinset.card = 9 := by
    rw [← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card,
      graph_edge_card_eq_one_face_card, he]
  rw [hecard] at hsum
  have hconst : (∑ _v : P.vertices, 3) = 2 * 9 := by simp [hn]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun v _ => hmin v)).mp
    (hconst.trans hsum.symm)
  exact fun v => (heq v (Finset.mem_univ _)).symm

theorem figure_of_degree_six_five_facets {P : ConvexPolytope d}
    (hP : P.dim = 4) (x : P.vertices)
    (D : VertexFigureGaloisData P P.toSet x.val)
    (hdeg : (vertexGraph P).degree x = 6)
    (hinc : Nat.card (IncidentFace P x.val 3) = 5) :
    D.figure.vertices.card = 6 ∧
      (∀ q : D.figure.vertices, (vertexGraph D.figure).degree q = 3) := by
  have hvertices := Nat.card_congr (neighborEquiv D x.property)
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hvertices
  have hdegree := degree_eq_actual_neighbors P x
  have hn : D.figure.vertices.card = 6 := by omega
  have hf : Nat.card (Face D.figure 2) = 5 :=
    (Nat.card_congr (incidentFigureEquiv D 2)).symm.trans hinc
  exact ⟨hn, cubic_of_six_vertices_five_facets D.figure
    (figure_dim D x.property 3 hP) hn hf⟩

theorem apex_figure_facet_has_three_vertices {P : ConvexPolytope d}
    (hg : polygonExcess P = 0) (x y : P.vertices)
    (D : VertexFigureGaloisData P P.toSet x.val)
    (F : IncidentFace P x.val 3)
    (hF : Nat.card (VerticesOn P F.val.val.carrier) = 5)
    (hxy : (vertexGraph P)ᶜ.Adj x y) (hyF : y.val ∈ F.val.val.carrier) :
    Nat.card (VerticesOn D.figure ((incidentFigureEquiv D 2) F).val.carrier) = 3 := by
  rw [← Nat.card_congr (faceNeighborFigureEquiv x D 2 F)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact unique_apex_pair_gives_three_neighbors P hg F.val hF x y hxy F.property hyF

theorem two_apex_facets_intersect_only_at_vertex (P : ConvexPolytope d)
    (hP : P.dim = 4) (hg : polygonExcess P = 0)
    (x a b : P.vertices) (F G : IncidentFace P x.val 3) (hFG : F ≠ G)
    (hF : Nat.card (VerticesOn P F.val.val.carrier) = 5)
    (hG : Nat.card (VerticesOn P G.val.val.carrier) = 5)
    (hxa : (vertexGraph P)ᶜ.Adj x a) (hxb : (vertexGraph P)ᶜ.Adj x b)
    (haF : a.val ∈ F.val.val.carrier) (hbG : b.val ∈ G.val.val.carrier)
    (hdeg : (vertexGraph P).degree x = 6)
    (hinc : Nat.card (IncidentFace P x.val 3) = 5) :
    faceCode P 3 F.val ∩ faceCode P 3 G.val = {x} := by
  obtain ⟨D⟩ := exists_figure P x.property (by omega)
  obtain ⟨hn, hdegree⟩ := figure_of_degree_six_five_facets hP x D hdeg hinc
  let f := (incidentFigureEquiv D 2) F
  let g := (incidentFigureEquiv D 2) G
  have hf := apex_figure_facet_has_three_vertices hg x a D F hF hxa haF
  have hg' := apex_figure_facet_has_three_vertices hg x b D G hG hxb hbG
  have hfg : f ≠ g := fun h => hFG ((incidentFigureEquiv D 2).injective h)
  have hdis : Disjoint (faceCode D.figure 2 f) (faceCode D.figure 2 g) := by
    apply triangular_cliques_disjoint (vertexGraph D.figure) (by simpa using hn) hdegree
    · exact (faceCode_card D.figure 2 f).trans hf
    · exact (faceCode_card D.figure 2 g).trans hg'
    · exact triangular_face_clique D.figure f hf
    · exact triangular_face_clique D.figure g hg'
    · exact fun h => hfg (faceCode_injective D.figure 2 h)
  ext z
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hzF, hzG⟩
    have hzF' := (Finset.mem_filter.mp hzF).2
    have hzG' := (Finset.mem_filter.mp hzG).2
    by_contra hzx
    by_cases hxz : (vertexGraph P).Adj x z
    · let y := asNeighbor P z hxz
      have hqF := (neighborImage_mem_incidentFigure_iff D x.property 2 F y).mpr hzF'
      have hqG := (neighborImage_mem_incidentFigure_iff D x.property 2 G y).mpr hzG'
      apply Finset.disjoint_left.mp hdis
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqF⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqG⟩
    · let e : Nonedge P :=
        ⟨s(x, z), (SimpleGraph.compl_adj _ _ _).mpr ⟨Ne.symm hzx, hxz⟩⟩
      have hwithin (H : IncidentFace P x.val 3) (hzH : z.val ∈ H.val.val.carrier) :
          Within P H.val.val.carrier e := by
        apply (within_iff P H.val.val.carrier e).mpr
        intro v hv
        change v ∈ s(x, z) at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact H.property
        · exact hzH
      apply hFG
      exact Subtype.ext (nonedge_common_facet_unique_of_excess_zero P hg e
        F.val G.val (hwithin F hzF') (hwithin G hzG'))
  · rintro rfl
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.property⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.property⟩⟩

theorem two_apex_facets_cover_nine_vertices (P : ConvexPolytope d)
    (hn : P.vertices.card = 9) (x : P.vertices) (F G : Face P 3)
    (hF : Nat.card (VerticesOn P F.val.carrier) = 5)
    (hG : Nat.card (VerticesOn P G.val.carrier) = 5)
    (hinter : faceCode P 3 F ∩ faceCode P 3 G = {x}) :
    faceCode P 3 F ∪ faceCode P 3 G = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have h := Finset.card_union_add_card_inter (faceCode P 3 F) (faceCode P 3 G)
  rw [hinter, Finset.card_singleton, faceCode_card, faceCode_card, hF, hG] at h
  simp only [Finset.card_univ, Fintype.card_coe, hn]
  omega

end Papers.RationalityTen.NineBipyramidLocalPartition

end
end
end BundlePart23

section BundlePart24
/- Source: Papers/NineBipyramidGraphSystem.lean -/



@[expose] public section

/-!
# Closing the nonedge-cycle contradiction

Edges of the degree-two nonedge graph index the bipyramidal facets. The
local partition makes the selected-edge graph for each label have degree
two at that label and degree one elsewhere. The parity lemma gives
connectedness, and cyclic relabeling gives the forbidden four-vertex
intersection proved in `NineBipyramidCycle`.


-/

noncomputable section
namespace Papers.RationalityTen.NineBipyramidGraphSystem

open Set SimpleGraph
open scoped Classical BigOperators
open Papers.RationalityTen.NineBipyramidCycle
open Papers.PolytopeCyclicLabeling

variable {V : Type*} [Fintype V] [DecidableEq V]

def adjacencyEdge (G : SimpleGraph V) {v w : V} (h : G.Adj v w) : G.edgeSet :=
  ⟨s(v, w), h⟩

theorem adjacencyEdge_symm (G : SimpleGraph V) {v w : V} (h : G.Adj v w) :
    adjacencyEdge G h.symm = adjacencyEdge G h := by
  apply Subtype.ext
  exact Sym2.eq_swap

def labelGraph (G : SimpleGraph V) (F : G.edgeSet → Finset V) (k : V) :
    SimpleGraph V where
  Adj v w := ∃ h : G.Adj v w, k ∈ F (adjacencyEdge G h)
  symm := ⟨by
    intro v w h
    obtain ⟨hvw, hk⟩ := h
    refine ⟨hvw.symm, ?_⟩
    rw [adjacencyEdge_symm]
    exact hk⟩
  loopless := ⟨by
    intro v h
    exact G.irrefl h.choose⟩

theorem labelGraph_le (G : SimpleGraph V) (F : G.edgeSet → Finset V) (k : V) :
    labelGraph G F k ≤ G := fun _ _ h => h.choose

theorem labelGraph_adj_iff (G : SimpleGraph V) (F : G.edgeSet → Finset V)
    (k : V) {v w : V} (h : G.Adj v w) :
    (labelGraph G F k).Adj v w ↔ k ∈ F (adjacencyEdge G h) := by
  exact ⟨fun hh => hh.choose_spec, fun hh => ⟨h, hh⟩⟩

theorem labelGraph_degree (G : SimpleGraph V) (F : G.edgeSet → Finset V)
    (hdegree : ∀ v, G.degree v = 2)
    (hlocal : ∀ (v a b : V) (ha : G.Adj v a) (hb : G.Adj v b), a ≠ b →
      F (adjacencyEdge G ha) ∩ F (adjacencyEdge G hb) = {v} ∧
      F (adjacencyEdge G ha) ∪ F (adjacencyEdge G hb) = Finset.univ)
    (k v : V) : (labelGraph G F k).degree v = 1 + if v = k then 1 else 0 := by
  have hcard : (G.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcard
  have ha : G.Adj v a := (G.mem_neighborFinset _ _).mp (by rw [hN]; simp)
  have hb : G.Adj v b := (G.mem_neighborFinset _ _).mp (by rw [hN]; simp)
  obtain ⟨hinter, hunion⟩ := hlocal v a b ha hb hab
  have hboth :
      (k ∈ F (adjacencyEdge G ha) ∧ k ∈ F (adjacencyEdge G hb)) ↔ k = v := by
    rw [← Finset.mem_inter, hinter, Finset.mem_singleton]
  have heither : k ∈ F (adjacencyEdge G ha) ∨ k ∈ F (adjacencyEdge G hb) := by
    rw [← Finset.mem_union, hunion]
    exact Finset.mem_univ _
  have hH : (labelGraph G F k).neighborFinset v =
      ({a, b} : Finset V).filter (fun w => (labelGraph G F k).Adj v w) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    constructor
    · intro hw
      refine ⟨?_, hw⟩
      rw [← hN]
      exact (G.mem_neighborFinset _ _).mpr ((labelGraph_le G F k) hw)
    · exact fun hw => hw.2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hH]
  have hHa := labelGraph_adj_iff G F k ha
  have hHb := labelGraph_adj_iff G F k hb
  by_cases hka : k ∈ F (adjacencyEdge G ha) <;>
    by_cases hkb : k ∈ F (adjacencyEdge G hb) <;>
    by_cases hvk : v = k <;>
    simp_all [Finset.filter_insert, Finset.filter_singleton, Finset.card_pair]

theorem no_nine_vertex_facet_graph_system (G : SimpleGraph V)
    (hcard : Fintype.card V = 9) (F : G.edgeSet → Finset V)
    (hdegree : ∀ v, G.degree v = 2)
    (hlocal : ∀ (v a b : V) (ha : G.Adj v a) (hb : G.Adj v b), a ≠ b →
      F (adjacencyEdge G ha) ∩ F (adjacencyEdge G hb) = {v} ∧
      F (adjacencyEdge G ha) ∪ F (adjacencyEdge G hb) = Finset.univ)
    (hinter : ∀ e f : G.edgeSet, e ≠ f → (F e ∩ F f).card ≤ 3) : False := by
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hconn : G.Connected := connected_of_label_degree_family G (labelGraph G F)
    (labelGraph_le G F) (labelGraph_degree G F hdegree hlocal)
  have hcycle := exists_cycleGraph_iso G hconn hdegree
  rw [hcard] at hcycle
  obtain ⟨ι⟩ := hcycle
  have hadj (i : Fin 9) : G.Adj (ι i) (ι (i + 1)) := by
    apply ι.toHom.map_adj
    rw [cycleGraph_adj]
    right
    simp
  let e : Fin 9 → G.edgeSet := fun i => adjacencyEdge G (hadj i)
  let C : Fin 9 → Finset (Fin 9) := fun i =>
    Finset.univ.filter (fun k => ι k ∈ F (e i))
  have hcin (i k : Fin 9) : k ∈ C i ↔ ι k ∈ F (e i) := by simp [C]
  apply no_nine_cycle_facet_family C
  · intro v k
    have hl : G.Adj (ι v) (ι (v - 1)) := by
      have h := (hadj (v - 1)).symm
      simpa only [sub_add_cancel] using h
    have hr := hadj v
    have hlr : ι (v - 1) ≠ ι (v + 1) := by
      intro h
      have hh := ι.injective h
      have hneq : ∀ i : Fin 9, i - 1 ≠ i + 1 := by decide
      exact hneq v hh
    obtain ⟨hinter', hunion⟩ := hlocal (ι v) (ι (v - 1)) (ι (v + 1)) hl hr hlr
    have hel : e (v - 1) = adjacencyEdge G hl := by
      apply Subtype.ext
      change s(ι (v - 1), ι (v - 1 + 1)) = s(ι v, ι (v - 1))
      rw [sub_add_cancel]
      exact Sym2.eq_swap
    have her : e v = adjacencyEdge G hr := rfl
    have hboth : (k ∈ C (v - 1) ∧ k ∈ C v) ↔ k = v := by
      rw [hcin, hcin, hel, her, ← Finset.mem_inter, hinter', Finset.mem_singleton]
      exact ι.injective.eq_iff
    have heither : k ∈ C (v - 1) ∨ k ∈ C v := by
      rw [hcin, hcin, hel, her, ← Finset.mem_union, hunion]
      exact Finset.mem_univ _
    by_cases hk1 : k ∈ C (v - 1) <;> by_cases hk2 : k ∈ C v <;>
      by_cases hkv : k = v <;> simp_all [memberIndicator]
  · intro i j hij
    have heij : e i ≠ e j := by
      intro h
      have hpair := congrArg (Sym2.map ι.symm) (congrArg Subtype.val h)
      have hpair' : s(i, i + 1) = s(j, j + 1) := by
        simpa only [e, adjacencyEdge, Sym2.map_mk, ι.symm_apply_apply] using hpair
      have hinj : ∀ a b : Fin 9, s(a, a + 1) = s(b, b + 1) → a = b := by decide
      exact hij (hinj i j hpair')
    have hmaps : Set.MapsTo ι (↑(C i ∩ C j) : Set (Fin 9))
        (↑(F (e i) ∩ F (e j)) : Set V) := by
      intro k hk
      obtain ⟨hki, hkj⟩ := Finset.mem_inter.mp hk
      exact Finset.mem_inter.mpr ⟨(hcin i k).mp hki, (hcin j k).mp hkj⟩
    exact (Finset.card_le_card_of_injOn ι hmaps ι.injective.injOn).trans
      (hinter (e i) (e j) heij)

end Papers.RationalityTen.NineBipyramidGraphSystem

end
end
end BundlePart24

section BundlePart25
/- Source: Papers/ActualNineBipyramidExclusion.lean -/



@[expose] public section

/-!
# The actual nine-bipyramid obstruction

This theorem has only the geometric hypotheses of the exceptional branch
in Appendix A.3: an intrinsic four-polytope with nine vertices, nine facets,
five vertices on every facet, triangular two-faces, and no simple vertex.
Euler counting, actual vertex figures, and the nonedge-cycle contradiction
derive `False`. No abstract boundary or combinatorial certificate is an input.


-/

noncomputable section
set_option maxHeartbeats 300000
set_option diagnostics true
namespace Papers.RationalityTen.ActualNineBipyramidExclusion

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation
open Papers.RationalityTen.NineBipyramidIncidence
open Papers.RationalityTen.SimplicialFiveFacetGeometry
open Papers.RationalityTen.NineBipyramidLocalPartition
open Papers.RationalityTen.NineBipyramidGraphSystem

theorem no_nine_five_vertex_simplicial_facets {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (hfacet : ∀ F : Face P 3, Nat.card (VerticesOn P F.val.carrier) = 5)
    (hg : polygonExcess P = 0)
    (hnonsimple : ∀ v : P.vertices, ¬IsSimpleVertex P v) : False := by
  obtain ⟨hedges, hinc, hdegrees⟩ :=
    nine_bipyramid_edge_and_degree_counts P hP hn hm hfacet hg hnonsimple
  trace "nine-bipyramid: counts obtained"
  have hdeg := nine_bipyramid_nonedge_degree_two P hP hn hm hfacet hg hnonsimple
  have hpairs := nonedge_card_add_edge_card P
  rw [hn, hedges] at hpairs
  have hnonedges : Nat.card (Nonedge P) = 9 := by norm_num only [Nat.choose] at hpairs; omega
  let A : Face P 3 ≃ Nonedge P := facetApexEquiv P hg hfacet (hm.trans hnonedges.symm)
  let F : Nonedge P → Finset P.vertices := fun e => faceCode P 3 (A.symm e)
  trace "nine-bipyramid: facet bijection defined"
  have hwithin (e : Nonedge P) : Within P (A.symm e).val.carrier e := by
    have h := (facetApexPair P hg hfacet (A.symm e)).property
    have he : (facetApexPair P hg hfacet (A.symm e)).val = e := A.apply_symm_apply e
    rw [he] at h
    exact h
  have hFmem (e : Nonedge P) (v : P.vertices) (hv : v ∈ e.val) :
      v.val ∈ (A.symm e).val.carrier :=
    (within_iff P (A.symm e).val.carrier e).mp (hwithin e) v hv
  trace "nine-bipyramid: applying abstract graph obstruction"
  apply no_nine_vertex_facet_graph_system (vertexGraph P)ᶜ
    (by simpa only [Fintype.card_coe] using hn) F
  · intro v
    exact (congrArg
      (fun I : Fintype ((vertexGraph P)ᶜ.neighborSet v) =>
        @SimpleGraph.degree _ (vertexGraph P)ᶜ v I)
      (Subsingleton.elim _ _)).trans (hdeg v)
  · trace "nine-bipyramid: local facet intersections"
    intro v a b ha hb hab
    let ea : Nonedge P := adjacencyEdge (vertexGraph P)ᶜ ha
    let eb : Nonedge P := adjacencyEdge (vertexGraph P)ᶜ hb
    have heaeb : ea ≠ eb := by
      intro h
      have hp : s(v, a) = s(v, b) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp hp with ⟨_, hab'⟩ | ⟨hvb, hav⟩
      · exact hab hab'
      · exact ((SimpleGraph.compl_adj _ _ _).mp hb).1 hvb
    have hFA : v.val ∈ (A.symm ea).val.carrier := hFmem ea v (Sym2.mem_mk_left _ _)
    have hFB : v.val ∈ (A.symm eb).val.carrier := hFmem eb v (Sym2.mem_mk_left _ _)
    let fa : IncidentFace P v.val 3 := ⟨A.symm ea, hFA⟩
    let fb : IncidentFace P v.val 3 := ⟨A.symm eb, hFB⟩
    have hne : fa ≠ fb := by
      intro h
      exact heaeb (A.symm.injective (congrArg Subtype.val h))
    have haF : a.val ∈ fa.val.val.carrier := hFmem ea a (Sym2.mem_mk_right _ _)
    have hbF : b.val ∈ fb.val.val.carrier := hFmem eb b (Sym2.mem_mk_right _ _)
    have hinter := two_apex_facets_intersect_only_at_vertex P hP hg v a b fa fb hne
      (hfacet _) (hfacet _) ha hb haF hbF (hdegrees v) (hinc v)
    have hunion := two_apex_facets_cover_nine_vertices P hn v fa.val fb.val
      (hfacet _) (hfacet _) hinter
    exact ⟨hinter, hunion⟩
  · intro e f hef
    apply distinct_facets_intersection_card_le_three P hg (A.symm e) (A.symm f)
    exact fun h => hef (A.symm.injective h)

end Papers.RationalityTen.ActualNineBipyramidExclusion

end
end
end BundlePart25

section BundlePart26
/- Source: Papers/SmallFacetRelationCounts.lean -/



@[expose] public section

/-!
# Exact shared-relation counts for facets with at most five vertices

Euler counting gives polygon excess at most one in each such three-face.
The actual polygon-relation rank is zero precisely when this excess is
zero, so the two are equal. The global count is consequently `E - g`.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget Papers.PolytopeFaceRestriction

theorem FiniteSpaceSupplement.rows_linearIndependent
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {U V : Submodule ℝ W} (D : FiniteSpaceSupplement U V) :
    LinearIndependent ℝ D.rows := by
  apply linearIndependent_iff_card_le_finrank_span.mpr
  have h := Submodule.finrank_add_le_finrank_add_finrank U
    (Submodule.span ℝ (Set.range D.rows))
  rw [D.spans] at h
  have hd := D.dimension
  change Fintype.card (Fin D.count) ≤ finrank ℝ (Submodule.span ℝ (Set.range D.rows))
  rw [Fintype.card_fin]
  omega

theorem FiniteSpaceSupplement.rows_ne_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {U V : Submodule ℝ W} (D : FiniteSpaceSupplement U V) (i : Fin D.count) :
    D.rows i ≠ 0 := D.rows_linearIndependent.ne_zero i

theorem actualPolygonRelationRank_eq_zero_iff {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    actualPolygonRelationRank P e F = 0 ↔ facetPolygonExcess P F = 0 := by
  constructor
  · intro hzero
    have hshapes := polygonRelationSpan_zero_shapes (vertexCoordinates P e)
      (polygonLabelsBelow P e F) (polygonLabelsBelow_rank P e F) hzero
    rw [facetPolygonExcess_eq_sum_faceBelow]
    apply Finset.sum_eq_zero
    intro R hR
    have hmem : actualFaceLabels P e R.val.val ∈ polygonLabelsBelow P e F :=
      Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩
    have hcard := hshapes _ hmem
    rw [actualFaceLabels_card] at hcard
    rw [hcard]
    norm_num
  · intro hzero
    have hle := actualPolygonRelationRank_le P e F
    rw [hzero] at hle
    omega

theorem twice_facet_polygon_excess_le_three_vertices_sub_twelve {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) :
    2 * facetPolygonExcess P F ≤ 3 * (facetVertexCount P F : ℤ) - 12 := by
  let Q := facePolytope P F.val.isFace
  have hQ : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have hcount : Q.vertices.card = facetVertexCount P F := by
    have h := Nat.card_congr (faceVerticesEquiv P F.val.isFace)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, facetVertexCount] using h.symm
  have hbound := vertex_edge_bound Q hQ
  rw [hcount, ← Nat.card_congr (faceBelowEquiv P F.val.isFace 1)] at hbound
  have hboundZ : 3 * (facetVertexCount P F : ℤ) ≤
      2 * Nat.card (FaceBelow P F.val.carrier 1) := by exact_mod_cast hbound
  have hformula := facet_polygon_excess_formula P F
  omega

theorem facetPolygonExcess_le_one_of_card_le_five {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3)
    (hF : facetVertexCount P F ≤ 5) : facetPolygonExcess P F ≤ 1 := by
  have h := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  omega

theorem actualPolygonRelationRank_eq_excess_of_card_le_five {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hF : facetVertexCount P F ≤ 5) :
    (actualPolygonRelationRank P e F : ℤ) = facetPolygonExcess P F := by
  have hnonneg : 0 ≤ facetPolygonExcess P F :=
    polygonExcess_nonnegative (facePolytope P F.val.isFace)
  have hmax := facetPolygonExcess_le_one_of_card_le_five P F hF
  have hle := actualPolygonRelationRank_le P e F
  by_cases hzero : actualPolygonRelationRank P e F = 0
  · rw [hzero, (actualPolygonRelationRank_eq_zero_iff P e F).mp hzero]
    rfl
  · have hpos : 1 ≤ actualPolygonRelationRank P e F := by omega
    omega

theorem actual_shared_count_of_card_le_five {d n : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    sharedRelationCount P (actualPolygonRelationRank P e) =
      facetExcess P - polygonExcess P := by
  unfold sharedRelationCount
  simp_rw [actualPolygonRelationRank_eq_excess_of_card_le_five P e _ (hfacets _)]
  rw [sum_facet_polygon_excess P hP]
  ring

theorem actual_sparse_shared_count_of_card_le_five {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (Fintype.card (SparseSharedRowIndex P e) : ℤ) =
      facetExcess P - polygonExcess P := by
  rw [sparseSharedRowIndex_card,
    actual_shared_count_of_card_le_five P hP e hfacets]

theorem actual_density_of_card_le_five_and_count_le_seven {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hcount : facetExcess P - polygonExcess P ≤ 7) : RationallyApproximable P := by
  apply actual_polytope_seven_shared_relations P hP e
  have h := actualSharedRowIndex_card P e
  rw [actual_shared_count_of_card_le_five P hP e hfacets] at h
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart26

section BundlePart27
/- Source: Papers/FiveVertexRelationSupport.lean -/



@[expose] public section

/-!
# Full support of a five-vertex simplicial facet relation

If four vertices of such a facet were affinely dependent, their span
would be a supporting plane: only one other vertex remains, so a linear
form vanishing on the four can be oriented positive at that last vertex.
The resulting actual face would have four vertices and dimension at most
two, contradicting the triangular boundary. This proves full support of
the unique facet relation at every realization.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open Papers.PolytopeFaceRestriction Papers.PolytopeIncidenceConfiguration
open Papers.RationalityTen.SimplicialFiveFacetGeometry

theorem five_vertex_simplicial_erase_rank {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hcard : Nat.card (VerticesOn P F.val.carrier) = 5)
    (hg : facetPolygonExcess P F = 0)
    (i : Fin n) (hi : i ∈ actualFaceLabels P e F.val) :
    subsetRank (vertexCoordinates P e) ((actualFaceLabels P e F.val).erase i) = 4 := by
  let p := vertexCoordinates P e
  let S := actualFaceLabels P e F.val
  have hS : S.card = 5 := (actualFaceLabels_card P e F.val).trans hcard
  have hSi : (S.erase i).card = 4 := by rw [Finset.card_erase_of_mem hi, hS]
  have hdim := globalRelationSpace_finrank p (S.erase i)
  have hrank : subsetRank p S = 4 := by
    rw [actualFaceLabels_rank, F.property]
  by_contra hbad
  change subsetRank p (S.erase i) ≠ 4 at hbad
  have hlow : subsetRank p (S.erase i) ≤ 3 := by omega
  let U := Submodule.span ℝ (p '' (↑(S.erase i) : Set (Fin n)))
  have hout : p i ∉ U := by
    intro hpi
    have hle : Submodule.span ℝ (p '' (↑S : Set (Fin n))) ≤ U := by
      apply Submodule.span_le.mpr
      rintro z ⟨j, hj, rfl⟩
      by_cases hji : j = i
      · subst j
        exact hpi
      · exact Submodule.subset_span ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, rfl⟩
    have h := Submodule.finrank_mono hle
    change subsetRank p S ≤ subsetRank p (S.erase i) at h
    omega
  obtain ⟨l₀, hl₀, hker⟩ := Submodule.exists_le_ker_of_notMem hout
  let l := (l₀ (p i))⁻¹ • l₀
  let a := functionalCoefficients l.toContinuousLinearMap
  let f := formOfVector a
  have hvalue (j : Fin n) : f (e j).val = l (p j) := by
    rw [← vector_dot_homogeneous]
    exact functionalCoefficients_dot l.toContinuousLinearMap (p j)
  have hfi : f (e i).val = 1 := by
    rw [hvalue]
    change (l₀ (p i))⁻¹ * l₀ (p i) = 1
    exact inv_mul_cancel₀ hl₀
  have hzero (j : Fin n) (hj : j ∈ S.erase i) : f (e j).val = 0 := by
    have hz : l₀ (p j) = 0 := hker (Submodule.subset_span ⟨j, hj, rfl⟩)
    rw [hvalue]
    change (l₀ (p i))⁻¹ * l₀ (p j) = 0
    rw [hz, mul_zero]
  let Q := facePolytope P F.val.isFace
  have hQdim : Q.dim = 3 := by
    change faceDim Q.toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  have hnonneg : ∀ x ∈ Q.toSet, 0 ≤ f x := by
    apply affine_nonneg_on_hull
    intro x hx
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj⟩ := e.surjective ⟨x, hxP⟩
    have hval : (e j).val = x := congrArg Subtype.val hj
    rw [← hval]
    by_cases hji : j = i
    · rw [hji, hfi]
      exact zero_le_one
    · have hjS : j ∈ S := (mem_actualFaceLabels P e F.val j).mpr (hval.symm ▸ hxF)
      rw [hzero j (Finset.mem_erase.mpr ⟨hji, hjS⟩)]
  have hne : (affineZeroFace Q f).Nonempty := by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (S.erase i).card by omega)
    refine ⟨(e j).val, ?_, hzero j hj⟩
    rw [facePolytope_toSet]
    exact (mem_actualFaceLabels P e F.val j).mp (Finset.mem_of_mem_erase hj)
  let A := affineZeroFace Q f
  have hAQ : Q.IsFace A := affineZeroFace_isFace Q f hnonneg hne
  have hAP : P.IsFace A := isFace_of_facePolytope P F.val.isFace hAQ
  have hAF : A ⊆ F.val.carrier := by
    have h := face_subset_toSet Q hAQ
    change A ⊆ (facePolytope P F.val.isFace).toSet at h
    rw [facePolytope_toSet] at h
    exact h
  have hlabels : actualFaceLabels P e ⟨A, hAP⟩ = S.erase i := by
    ext j
    rw [mem_actualFaceLabels, Finset.mem_erase]
    constructor
    · intro hjA
      refine ⟨?_, (mem_actualFaceLabels P e F.val j).mpr (hAF hjA)⟩
      intro hji
      have hz : f (e j).val = 0 := hjA.2
      rw [hji, hfi] at hz
      exact one_ne_zero hz
    · rintro ⟨hji, hjS⟩
      refine ⟨?_, hzero j (Finset.mem_erase.mpr ⟨hji, hjS⟩)⟩
      rw [facePolytope_toSet]
      exact (mem_actualFaceLabels P e F.val j).mp hjS
  have hfour : Nat.card (VerticesOn Q A) = 4 := by
    rw [verticesOn_facePolytope_card P F.val.isFace hAF,
      ← actualFaceLabels_card P e ⟨A, hAP⟩, hlabels, hSi]
  have hproper : A ⊂ Q.toSet := by
    refine ⟨face_subset_toSet Q hAQ, ?_⟩
    intro hback
    have hiQ : (e i).val ∈ Q.toSet := by
      rw [facePolytope_toSet]
      exact (mem_actualFaceLabels P e F.val i).mp hi
    have hz : f (e i).val = 0 := (hback hiQ).2
    rw [hfi] at hz
    exact one_ne_zero hz
  have hAdim := faceDim_lt_of_ssubset Q hAQ (toSet_isFace Q) hproper
  change faceDim A < Q.dim at hAdim
  rw [hQdim] at hAdim
  have hsmall := face_vertices_le_three_of_dim_le_two Q hg hAQ (by omega)
  omega

theorem five_vertex_simplicial_relation_full_support {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hcard : Nat.card (VerticesOn P F.val.carrier) = 5)
    (hg : facetPolygonExcess P F = 0)
    {v : Fin n → ℝ}
    (hv : v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val))
    (hv0 : v ≠ 0) : vectorSupport v = actualFaceLabels P e F.val := by
  let S := actualFaceLabels P e F.val
  let p := vertexCoordinates P e
  obtain ⟨hs, hpv⟩ := (mem_globalRelationSpace_iff p S v).mp hv
  have hfull (i : Fin n) (hi : i ∈ S) : v i ≠ 0 := by
    intro hvi
    have hcard' : (S.erase i).card = 4 := by
      rw [Finset.card_erase_of_mem hi, actualFaceLabels_card, hcard]
    have hrank := five_vertex_simplicial_erase_rank P e F hcard hg i hi
    change subsetRank p (S.erase i) = 4 at hrank
    have hdim := globalRelationSpace_finrank p (S.erase i)
    have hbot : globalRelationSpace p (S.erase i) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    have hmem : v ∈ globalRelationSpace p (S.erase i) := by
      apply (mem_globalRelationSpace_iff p _ v).mpr
      refine ⟨?_, hpv⟩
      intro j hj
      by_cases hji : j = i
      · simpa only [hji] using hvi
      · exact hs j (fun hjS => hj (Finset.mem_erase.mpr ⟨hji, hjS⟩))
    rw [hbot] at hmem
    exact hv0 hmem
  ext i
  simp only [vectorSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hi => by by_contra hin; exact hi (hs i hin), hfull i⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart27

section BundlePart28
/- Source: Papers/SmallFacetSparseSupport.lean -/



@[expose] public section

/-!
# Exact nonzero counts in the small-facet relation matrix

With at most five vertices per facet, every polygon row has exactly four
entries and every nonempty facet supplement has exactly five. Thus the
sparse construction attains `nnz = 5c - g`; in the nine-facet-excess,
one-quadrilateral branch this is exactly 39.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget
open Papers.RationalityTen.SimplicialFiveFacetGeometry

theorem polygon_card_lt_containing_facet {d : ℕ}
    (P : ConvexPolytope d) (R : Face P 2) (F : Face P 3)
    (hRF : R.val.carrier ⊆ F.val.carrier) :
    Nat.card (VerticesOn P R.val.carrier) < facetVertexCount P F := by
  have hsub : faceCode P 2 R ⊆ faceCode P 3 F := by
    intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hRF (Finset.mem_filter.mp hv).2⟩
  have hne : faceCode P 2 R ≠ faceCode P 3 F := by
    intro h
    have hRF' : R.val.carrier = F.val.carrier := by
      apply face_eq_of_vertex_membership P R.val.isFace F.val.isFace
      intro v
      have hh : v ∈ faceCode P 2 R ↔ v ∈ faceCode P 3 F := by rw [h]
      simpa only [faceCode, Finset.mem_filter, Finset.mem_univ, true_and] using hh
    have hd := congrArg faceDim hRF'
    rw [R.property, F.property] at hd
    omega
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [faceCode_card, faceCode_card] at hlt
  exact hlt

theorem polygon_card_le_four_of_facet_card_le_five {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (R : Face P 2) : Nat.card (VerticesOn P R.val.carrier) ≤ 4 := by
  have hcofaces := ridge_coface_card P 2 hP R
  change Nat.card (Coface P R.val.carrier 3) = 2 at hcofaces
  have hex : Nonempty (Coface P R.val.carrier 3) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card (Coface P R.val.carrier 3) by omega)).1
  obtain ⟨F⟩ := hex
  have hlt := polygon_card_lt_containing_facet P R F.val F.property
  have hbound := hfacets F.val
  change Nat.card (VerticesOn P R.val.carrier) <
    Nat.card (VerticesOn P F.val.val.carrier) at hlt
  change Nat.card (VerticesOn P F.val.val.carrier) ≤ 5 at hbound
  omega

theorem polygon_card_le_four_of_one_large_facet {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (F₀ : Face P 3)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 5)
    (R : Face P 2) : Nat.card (VerticesOn P R.val.carrier) ≤ 4 := by
  let T := Finset.univ.filter (fun F : Face P 3 => R.val.carrier ⊆ F.val.carrier)
  have hc : T.card = 2 := by
    simpa only [T, Coface, Nat.card_eq_fintype_card, Fintype.card_subtype]
      using ridge_coface_card P 2 hP R
  obtain ⟨F, hF⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (show ({F₀} : Finset (Face P 3)).card < T.card by simp [hc])
  obtain ⟨hFT, hFF₀⟩ := Finset.mem_sdiff.mp hF
  have hne : F ≠ F₀ := by simpa only [Finset.mem_singleton] using hFF₀
  have hlt := polygon_card_lt_containing_facet P R F (Finset.mem_filter.mp hFT).2
  have hbound := hother F hne
  omega

theorem actualPolygonSparseBasis_support_card_of_small_facets {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (R : Face P 2) (i : Fin (actualPolygonSparseBasis P e R).count) :
    (vectorSupport ((actualPolygonSparseBasis P e R).rows i)).card = 4 := by
  have hcount := actualPolygonSparseBasis_count P e R
  have hmax := polygon_card_le_four_of_facet_card_le_five P hP hfacets R
  have hc : Nat.card (VerticesOn P R.val.carrier) = 4 := by have := i.isLt; omega
  have hsmallcard := vertices_card_ge_dim_add_one P
  rw [hP] at hsmallcard
  let v := (actualPolygonSparseBasis P e R).rows i
  let S := actualFaceLabels P e R.val
  have hv : v ∈ globalRelationSpace (vertexCoordinates P e) S :=
    (actualPolygonSparseBasis P e R).mem i
  have hv0 : v ≠ 0 := (actualPolygonSparseBasis P e R).toFiniteSpaceSupplement.rows_ne_zero i
  have hScard : S.card = 4 := (actualFaceLabels_card P e R.val).trans hc
  have hfull := four_relation_full_support (vertexCoordinates P e)
    (vertexCoordinates_small_independent P e (by omega)) hScard hv hv0
  have houtside := ((mem_globalRelationSpace_iff (vertexCoordinates P e) S v).mp hv).1
  have hs : vectorSupport v = S := by
    ext j
    simp only [vectorSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hj => by by_contra hjS; exact hj (houtside j hjS), hfull j⟩
  rw [hs, hScard]

theorem actualFacetSparseSupplement_support_card_of_small_facets {n : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (F : Face P 3) (i : Fin (actualFacetSparseSupplement P e F).count) :
    (vectorSupport ((actualFacetSparseSupplement P e F).rows i)).card = 5 := by
  have hcount := actualFacetSparseSupplement_count P e F
  have hmax := hfacets F
  change Nat.card (VerticesOn P F.val.carrier) ≤ 5 at hmax
  have hc : Nat.card (VerticesOn P F.val.carrier) = 5 := by have := i.isLt; omega
  have hrank : actualPolygonRelationRank P e F = 0 := by have := i.isLt; omega
  have hg := (actualPolygonRelationRank_eq_zero_iff P e F).mp hrank
  have hs := five_vertex_simplicial_relation_full_support P e F hc hg
    ((actualFacetSparseSupplement P e F).mem i)
    ((actualFacetSparseSupplement P e F).toFiniteSpaceSupplement.rows_ne_zero i)
  rw [hs, actualFaceLabels_card, hc]

theorem actualSparseSharedMatrix_nonzeros_eq_of_small_facets {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (totalNonzeros (actualSparseSharedMatrix P e) : ℤ) =
      5 * Fintype.card (SparseSharedRowIndex P e) - polygonExcess P := by
  have heq : totalNonzeros (actualSparseSharedMatrix P e) =
      totalNonzeros (actualSparseSharedRow P e) := by
    exact Fintype.sum_equiv ((Fintype.equivFin (SparseSharedRowIndex P e)).symm)
      _ _ (fun _ => rfl)
  have hrow : totalNonzeros (actualSparseSharedRow P e) =
      4 * (∑ R : Face P 2, (actualPolygonSparseBasis P e R).count) +
      5 * (∑ F : Face P 3, (actualFacetSparseSupplement P e F).count) := by
    unfold totalNonzeros
    change (∑ i :
      (Σ R : Face P 2, Fin (actualPolygonSparseBasis P e R).count) ⊕
      (Σ F : Face P 3, Fin (actualFacetSparseSupplement P e F).count),
      (vectorSupport (actualSparseSharedRow P e i)).card) = _
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sigma, actualSparseSharedRow]
    simp_rw [actualPolygonSparseBasis_support_card_of_small_facets P hP e hfacets,
      actualFacetSparseSupplement_support_card_of_small_facets P e hfacets]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> norm_num only [Nat.cast_id] <;> ring
  have hcard : Fintype.card (SparseSharedRowIndex P e) =
      (∑ R : Face P 2, (actualPolygonSparseBasis P e R).count) +
      (∑ F : Face P 3, (actualFacetSparseSupplement P e F).count) := by
    simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  have hpoly : ((∑ R : Face P 2, (actualPolygonSparseBasis P e R).count) : ℤ) =
      polygonExcess P := by
    simp only [Nat.cast_sum, actualPolygonSparseBasis_count, polygonExcess]
  rw [heq, hrow, hcard]
  push_cast
  rw [← hpoly]
  ring

theorem actualSparseSharedMatrix_has_thirtynine_nonzeros {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hE : facetExcess P = 9) (hg : polygonExcess P = 1) :
    totalNonzeros (actualSparseSharedMatrix P e) = 39 := by
  have hcount := actual_sparse_shared_count_of_card_le_five P hP e hfacets
  have hnonzero := actualSparseSharedMatrix_nonzeros_eq_of_small_facets P hP e hfacets
  rw [hE, hg] at hcount
  rw [hg] at hnonzero
  omega

theorem nine_four_supports_force_thirtysix_nonzeros
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : I → Fin 9 → ℝ) (L : Finset (Finset I))
    (hL : L.card = 9) (hfour : ∀ S ∈ L, S.card = 4)
    (hrequired : ∀ S ∈ L, ∃ j : Fin 9, columnSupport C j = S) :
    totalNonzeros C = 36 := by
  let T := (Finset.univ : Finset (Fin 9)).image (columnSupport C)
  have hsub : L ⊆ T := by
    intro S hS
    obtain ⟨j, hj⟩ := hrequired S hS
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hT : T.card ≤ 9 := by
    exact Finset.card_image_le.trans (by simp)
  have heq : L = T := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hcolumn (j : Fin 9) : (columnSupport C j).card = 4 := by
    apply hfour
    rw [heq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [totalNonzeros_eq_sum_columns]
  simp only [hcolumn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- This is the precise counting exclusion used for the single-quadrilateral
nine-vertex case: no family of nine distinct four-supports can all be required. -/
theorem actual_single_quadrilateral_omits_four_support
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 9 ≃ P.vertices)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hE : facetExcess P = 9) (hg : polygonExcess P = 1)
    (L : Finset (Finset (Fin (Fintype.card (SparseSharedRowIndex P e)))))
    (hL : L.card = 9) (hfour : ∀ S ∈ L, S.card = 4) :
    ∃ S ∈ L, ∀ j : Fin 9, columnSupport (actualSparseSharedMatrix P e) j ≠ S := by
  by_contra h
  push_neg at h
  have h36 := nine_four_supports_force_thirtysix_nonzeros
    (actualSparseSharedMatrix P e) L hL hfour h
  have h39 := actualSparseSharedMatrix_has_thirtynine_nonzeros P hP e hfacets hE hg
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart28

section BundlePart29
/- Source: Papers/PolygonDiagonalCounting.lean -/



@[expose] public section

/-!
# Counting polygon diagonals inside an actual facet

A nonedge is a diagonal of at most one polygon. This identifies the
diagonals allocated to a facet with the disjoint union of its polygons'
diagonals. For triangular and quadrilateral polygons, the allocated
weight therefore depends only on the number of facet vertices.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeFaceRestriction
open Papers.PolytopeNonedgeAllocation Papers.PolytopeFaceNonedges

variable {d : ℕ}

def facetDiagonalSigmaMap (P : ConvexPolytope d) (F : Face P 3) :
    (Σ R : FaceBelow P F.val.carrier 2, NonedgesOn P R.val.val.carrier) →
      DiagonalsOn P F.val.carrier
  | ⟨R, e⟩ => ⟨e.val,
      ⟨R.property e.property.1, R.property e.property.2⟩,
      R.val, e.property.1, e.property.2⟩

theorem facetDiagonalSigmaMap_bijective (P : ConvexPolytope d) (F : Face P 3) :
    Function.Bijective (facetDiagonalSigmaMap P F) := by
  constructor
  · rintro ⟨R, e⟩ ⟨S, f⟩ h
    have hef : e.val = f.val := congrArg Subtype.val h
    obtain ⟨hne, hnon⟩ := nonedge_out P e.val
    have hxS : e.val.val.out.1.val ∈ S.val.val.carrier := by rw [hef]; exact f.property.1
    have hyS : e.val.val.out.2.val ∈ S.val.val.carrier := by rw [hef]; exact f.property.2
    have hRS : R = S := Subtype.ext (polygon_diagonal_unique P _ _ hne hnon
      R.val S.val e.property.1 e.property.2 hxS hyS)
    subst S
    have hef' : e = f := Subtype.ext hef
    subst f
    rfl
  · intro e
    obtain ⟨R, hxR, hyR⟩ := e.property.2
    obtain ⟨hne, hnon⟩ := nonedge_out P e.val
    have hRF := diagonal_face_subset P _ _ hne hnon R hxR hyR
      F.val.isFace e.property.1.1 e.property.1.2
    refine ⟨⟨⟨R, hRF⟩, ⟨e.val, hxR, hyR⟩⟩, ?_⟩
    exact Subtype.ext rfl

def facetDiagonalSigmaEquiv (P : ConvexPolytope d) (F : Face P 3) :
    (Σ R : FaceBelow P F.val.carrier 2, NonedgesOn P R.val.val.carrier) ≃
      DiagonalsOn P F.val.carrier :=
  Equiv.ofBijective (facetDiagonalSigmaMap P F) (facetDiagonalSigmaMap_bijective P F)

theorem facetDiagonalCount_eq_sum_polygon_diagonals (P : ConvexPolytope d)
    (F : Face P 3) :
    (facetDiagonalCount P F : ℤ) =
      ∑ R : FaceBelow P F.val.carrier 2,
        (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) := by
  have h := Nat.card_congr (facetDiagonalSigmaEquiv P F)
  have hc : facetDiagonalCount P F =
      ∑ R : FaceBelow P F.val.carrier 2, Nat.card (NonedgesOn P R.val.val.carrier) := by
    simpa only [facetDiagonalCount, Nat.card_eq_fintype_card, Fintype.card_sigma] using h.symm
  exact_mod_cast hc

theorem facet_diagonal_count_twice_polygon_excess (P : ConvexPolytope d)
    (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    (facetDiagonalCount P F : ℤ) = 2 * facetPolygonExcess P F := by
  have hlocal (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) =
        2 * ((Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3) := by
    have hmin := face_vertices_card_ge_dim_add_one P 2 R.val
    have hmax := hpolygons R
    have hc := polygon_nonedge_count P R.val
    have hr : Nat.card (VerticesOn P R.val.val.carrier) = 3 ∨
        Nat.card (VerticesOn P R.val.val.carrier) = 4 := by omega
    rcases hr with hr | hr <;> rw [hr] at hc ⊢ <;> norm_num only [Nat.choose] at hc ⊢ <;> omega
  rw [facetDiagonalCount_eq_sum_polygon_diagonals, facetPolygonExcess_eq_sum_faceBelow,
    Finset.mul_sum]
  exact Finset.sum_congr (by ext; simp) (fun R _ => hlocal R)

theorem allocatedFacetWeight_of_triangles_quadrilaterals (P : ConvexPolytope d)
    (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    allocatedFacetWeight P F =
      ((facetVertexCount P F : ℚ) - 4) * ((facetVertexCount P F : ℚ) - 3) / 2 := by
  have hid := facet_weight_surplus_identity P F 0
  have hd := facet_diagonal_count_twice_polygon_excess P F hpolygons
  have hdQ : (facetDiagonalCount P F : ℚ) = 2 * (facetPolygonExcess P F : ℚ) := by
    exact_mod_cast hd
  unfold rankSurplus at hid
  norm_num only [Nat.cast_zero, add_zero, sub_zero] at hid
  nlinarith only [hid, hdQ]

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart29

section BundlePart30
/- Source: Papers/SixFacetNineVertexBudget.lean -/



@[expose] public section

/-!
# The one-six-vertex-facet branch on nine vertices

Every polygon lies in two facets, so one large facet cannot create a
pentagon when all other facets have five vertices. The exact diagonal
count gives allocated weights three and one. The global budget forces
at least three quadrilaterals and at most eight shared rows. Equality
places three polygon relations in the two-dimensional relation space
of the six-vertex facet.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget
open Papers.PolytopeNonedgeAllocation

theorem six_facet_rank_one_excess_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (hPcard : 3 ≤ P.vertices.card)
    (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hone : actualPolygonRelationRank P e F = 1) : facetPolygonExcess P F = 1 := by
  have hd := facet_diagonal_count_twice_polygon_excess P F hpolygons
  have hd2 := actualPolygonRelationRank_one P e hPcard F hone
  rw [hd2] at hd
  omega

theorem six_facet_relation_excess_le_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (hPcard : 3 ≤ P.vertices.card)
    (F : Face P 3) (hF : facetVertexCount P F = 6)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : ℤ) ≤ 1 := by
  have hgmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hgmax
  by_cases hzero : actualPolygonRelationRank P e F = 0
  · rw [hzero, (actualPolygonRelationRank_eq_zero_iff P e F).mp hzero]
    norm_num
  by_cases hone : actualPolygonRelationRank P e F = 1
  · rw [hone, six_facet_rank_one_excess_one P e hPcard F hpolygons hone]
    norm_num
  · omega

theorem six_facet_excess_one_forces_three_two {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (hPcard : 3 ≤ P.vertices.card)
    (F : Face P 3) (hF : facetVertexCount P F = 6)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4)
    (hexcess : facetPolygonExcess P F - (actualPolygonRelationRank P e F : ℤ) = 1) :
    facetPolygonExcess P F = 3 ∧ actualPolygonRelationRank P e F = 2 := by
  have hgmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hF] at hgmax
  have hzero : actualPolygonRelationRank P e F ≠ 0 := by
    intro h
    rw [h, (actualPolygonRelationRank_eq_zero_iff P e F).mp h] at hexcess
    norm_num at hexcess
  have hone : actualPolygonRelationRank P e F ≠ 1 := by
    intro h
    rw [h, six_facet_rank_one_excess_one P e hPcard F hpolygons h] at hexcess
    norm_num at hexcess
  omega

theorem one_large_facet_shared_count {d n : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (e : Fin n ≃ P.vertices)
    (F₀ : Face P 3)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 5) :
    sharedRelationCount P (actualPolygonRelationRank P e) =
      facetExcess P - polygonExcess P +
        (facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : ℤ)) := by
  let ε := facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : ℤ)
  have hpoint (F : Face P 3) : (actualPolygonRelationRank P e F : ℤ) =
      facetPolygonExcess P F - if F = F₀ then ε else 0 := by
    by_cases hF : F = F₀
    · subst F
      simp only [ite_true, ε]
      ring
    · rw [if_neg hF, sub_zero]
      exact actualPolygonRelationRank_eq_excess_of_card_le_five P e F (hother F hF)
  have hsum : (∑ F : Face P 3, (actualPolygonRelationRank P e F : ℤ)) =
      2 * polygonExcess P - ε := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, sum_facet_polygon_excess P hP]
    simp
  unfold sharedRelationCount
  rw [hsum]
  dsimp only [ε]
  ring

theorem nine_vertex_one_six_facet_budget {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 6)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F = 5) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 8 ∧
      (Fintype.card (SparseSharedRowIndex P e) = 8 →
        polygonExcess P = 3 ∧ facetPolygonExcess P F₀ = 3 ∧
          actualPolygonRelationRank P e F₀ = 2) := by
  have hotherle (F : Face P 3) (hF : F ≠ F₀) : facetVertexCount P F ≤ 5 := by
    rw [hother F hF]
  have hpolygons := polygon_card_le_four_of_one_large_facet P hP F₀ hotherle
  have hlocal (F : Face P 3) := allocatedFacetWeight_of_triangles_quadrilaterals P F
    (fun R => hpolygons R.val)
  have hweight (F : Face P 3) : allocatedFacetWeight P F = 1 + if F = F₀ then 2 else 0 := by
    rw [hlocal]
    by_cases hF : F = F₀
    · subst F
      rw [hF₀]
      norm_num
    · rw [hother F hF, if_neg hF]
      norm_num
  have hweights : (∑ F : Face P 3, allocatedFacetWeight P F) = 11 := by
    simp_rw [hweight]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hm]
    norm_num
  have hD := allocated_weights_le_nonedge_card P hP
  rw [hweights] at hD
  have hDnat : 11 ≤ Nat.card (Nonedge P) := by exact_mod_cast hD
  have hEpoint (F : Face P 3) : ((facetVertexCount P F : ℤ) - 4) =
      1 + if F = F₀ then 1 else 0 := by
    by_cases hF : F = F₀
    · subst F
      rw [hF₀]
      norm_num
    · rw [hother F hF, if_neg hF]
      norm_num
  have hE : facetExcess P = 10 := by
    change (∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4)) = 10
    simp_rw [hEpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hm]
    simp
  have hid := actual_excess_identity P hP
  rw [hE, hn, hm] at hid
  norm_num only [show Nat.choose 9 2 = 36 by decide, Nat.cast_ofNat] at hid
  have hg : 3 ≤ polygonExcess P := by omega
  have hPcard : 3 ≤ P.vertices.card := by omega
  have heps := six_facet_relation_excess_le_one P e hPcard F₀ hF₀
    (fun R => hpolygons R.val)
  have hcount := sparseSharedRowIndex_card P e
  rw [one_large_facet_shared_count P hP e F₀ hotherle, hE] at hcount
  constructor
  · omega
  · intro h8
    have heps1 : facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : ℤ) = 1 := by
      rw [h8] at hcount
      omega
    have hg3 : polygonExcess P = 3 := by rw [h8] at hcount; omega
    obtain ⟨hlocal3, hrank2⟩ := six_facet_excess_one_forces_three_two P e hPcard F₀ hF₀
      (fun R => hpolygons R.val) heps1
    exact ⟨hg3, hlocal3, hrank2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart30

section BundlePart31
/- Source: Papers/SixFacetThreeRowDependence.lean -/



@[expose] public section

/-!
# The three-row dependence excluding the golden obstruction

Local polygon-basis rows inject into the globally selected row set. Their
number is the local polygon excess, and their span lies in the actual
local polygon-relation space. Excess three and rank two therefore produce
a nonzero vector in the transpose kernel supported on at most three row
positions. This is incompatible with the golden row-space support bound.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus Papers.PolytopeFaceRestriction

theorem exists_sparse_transpose_kernel_of_subset_rank_lt {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin c))
    (hrank : subsetRank C S < S.card) :
    ∃ v : Fin c → ℝ, v ≠ 0 ∧ C.transpose.mulVec v = 0 ∧
      (vectorSupport v).card ≤ S.card := by
  have hdim := globalRelationSpace_finrank C S
  have hne : globalRelationSpace C S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨v, hv, hv0⟩ := (globalRelationSpace C S).ne_bot_iff.mp hne
  obtain ⟨hout, hker⟩ := (mem_globalRelationSpace_iff C S v).mp hv
  refine ⟨v, hv0, hker, Finset.card_le_card ?_⟩
  intro i hi
  by_contra hin
  exact (mem_vectorSupport v i).mp hi (hout i hin)

def LocalPolygonSparseRowIndex {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :=
  Σ R : FaceBelow P F.val.carrier 2, Fin (actualPolygonSparseBasis P e R.val).count

instance {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    Fintype (LocalPolygonSparseRowIndex P e F) := by
  unfold LocalPolygonSparseRowIndex
  infer_instance

def localPolygonSparseRowEmbedding {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    LocalPolygonSparseRowIndex P e F ↪ SparseSharedRowIndex P e where
  toFun i := Sum.inl ⟨i.1.val, i.2⟩
  inj' := by
    rintro ⟨⟨R, hRF⟩, i⟩ ⟨⟨S, hSF⟩, j⟩ h
    have h' := Sum.inl.inj h
    cases h'
    rfl

theorem localPolygonSparseRowIndex_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    (Fintype.card (LocalPolygonSparseRowIndex P e F) : ℤ) = facetPolygonExcess P F := by
  simp only [LocalPolygonSparseRowIndex, Fintype.card_sigma, Fintype.card_fin,
    Nat.cast_sum, actualPolygonSparseBasis_count]
  exact (facetPolygonExcess_eq_sum_faceBelow P F).symm

theorem localPolygonSparseRow_mem {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3)
    (i : LocalPolygonSparseRowIndex P e F) :
    actualSparseSharedRow P e (localPolygonSparseRowEmbedding P e F i) ∈
      polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) := by
  apply globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
    (Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, rfl⟩)
  exact (actualPolygonSparseBasis P e i.1.val).mem i.2

theorem three_polygon_rows_rank_two_give_sparse_left_kernel {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hg : facetPolygonExcess P F = 3)
    (hrank : actualPolygonRelationRank P e F = 2) :
    ∃ v : Fin (Fintype.card (SparseSharedRowIndex P e)) → ℝ,
      v ≠ 0 ∧ (actualSparseSharedMatrix P e).transpose.mulVec v = 0 ∧
        (vectorSupport v).card ≤ 3 := by
  let f : LocalPolygonSparseRowIndex P e F →
      Fin (Fintype.card (SparseSharedRowIndex P e)) :=
    fun i => Fintype.equivFin (SparseSharedRowIndex P e)
      (localPolygonSparseRowEmbedding P e F i)
  have hf : Function.Injective f :=
    (Fintype.equivFin (SparseSharedRowIndex P e)).injective.comp
      (localPolygonSparseRowEmbedding P e F).injective
  let S := Finset.univ.image f
  have hS : S.card = 3 := by
    have hc := localPolygonSparseRowIndex_card P e F
    rw [hg] at hc
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    omega
  have hrow (i : LocalPolygonSparseRowIndex P e F) :
      actualSparseSharedMatrix P e (f i) =
        actualSparseSharedRow P e (localPolygonSparseRowEmbedding P e F i) := by
    simp only [actualSparseSharedMatrix, f, Equiv.symm_apply_apply]
  have hle : Submodule.span ℝ (actualSparseSharedMatrix P e ''
      (↑S : Set (Fin (Fintype.card (SparseSharedRowIndex P e))))) ≤
      polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) := by
    apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    rw [hrow]
    exact localPolygonSparseRow_mem P e F i
  have hdim := Submodule.finrank_mono hle
  change subsetRank (actualSparseSharedMatrix P e) S ≤ actualPolygonRelationRank P e F at hdim
  rw [hrank] at hdim
  obtain ⟨v, hv, hker, hsupp⟩ := exists_sparse_transpose_kernel_of_subset_rank_lt
    (actualSparseSharedMatrix P e) S (by omega)
  exact ⟨v, hv, hker, by omega⟩

theorem nine_vertex_one_six_facet_rows_or_sparse_left_kernel {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 9) (hm : Nat.card (Face P 3) = 9)
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 6)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F = 5) :
    Fintype.card (SparseSharedRowIndex P e) ≤ 7 ∨
      (Fintype.card (SparseSharedRowIndex P e) = 8 ∧
        ∃ v : Fin (Fintype.card (SparseSharedRowIndex P e)) → ℝ,
          v ≠ 0 ∧ (actualSparseSharedMatrix P e).transpose.mulVec v = 0 ∧
            (vectorSupport v).card ≤ 3) := by
  obtain ⟨hle, heq⟩ := nine_vertex_one_six_facet_budget P hP e hn hm F₀ hF₀ hother
  by_cases hsmall : Fintype.card (SparseSharedRowIndex P e) ≤ 7
  · exact Or.inl hsmall
  · have h8 : Fintype.card (SparseSharedRowIndex P e) = 8 := by omega
    obtain ⟨_, hg, hrank⟩ := heq h8
    exact Or.inr ⟨h8, three_polygon_rows_rank_two_give_sparse_left_kernel P e F₀ hg hrank⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart31

section BundlePart32
/- Source: Papers/NineVertexFacetShapes.lean -/



@[expose] public section

/-!
# Exact facet-size reductions in the nine-vertex budget

The selected nonsimplicial facets are exactly the three-faces with more
than four vertices. Their count bounds the facet excess. Equality forces
all of them to have five vertices; excess ten with nine such facets forces
one six-vertex facet and eight five-vertex facets.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus

def nonsimplicialFacets {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => 4 < facetVertexCount P F

@[simp] theorem mem_nonsimplicialFacets {d : ℕ} (P : ConvexPolytope d) (F : Face P 3) :
    F ∈ nonsimplicialFacets P ↔ 4 < facetVertexCount P F := by
  simp [nonsimplicialFacets]

theorem nonsimplicial_facets_card_le_excess {d : ℕ} (P : ConvexPolytope d) :
    ((nonsimplicialFacets P).card : ℤ) ≤ facetExcess P := by
  have hpoint (F : Face P 3) : (if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) ≤
      (facetVertexCount P F : ℤ) - 4 := by
    have hmin :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
    by_cases hF : F ∈ nonsimplicialFacets P
    · have hbig := (mem_nonsimplicialFacets P F).mp hF
      rw [if_pos hF]
      omega
    · rw [if_neg hF]
      change 0 ≤ (Nat.card (VerticesOn P F.val.carrier) : ℤ) - 4
      omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun F _ => hpoint F)
  change (∑ F : Face P 3, if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) ≤ facetExcess P at h
  simpa only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] using h

theorem nine_nonsimplicial_facets_nine_excess {d : ℕ}
    (P : ConvexPolytope d) (hN : 9 ≤ (nonsimplicialFacets P).card)
    (hE : facetExcess P = 9) :
    (nonsimplicialFacets P).card = 9 ∧
      (∀ F : Face P 3, facetVertexCount P F ≤ 5) ∧
      (∀ F ∈ nonsimplicialFacets P, facetVertexCount P F = 5) := by
  have hcardle := nonsimplicial_facets_card_le_excess P
  rw [hE] at hcardle
  have hcard : (nonsimplicialFacets P).card = 9 := by omega
  have hpoint (F : Face P 3) : (if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) ≤
      (facetVertexCount P F : ℤ) - 4 := by
    have hmin :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
    by_cases hF : F ∈ nonsimplicialFacets P
    · have hbig := (mem_nonsimplicialFacets P F).mp hF
      rw [if_pos hF]
      omega
    · rw [if_neg hF]
      change 0 ≤ (Nat.card (VerticesOn P F.val.carrier) : ℤ) - 4
      omega
  have hsum : (∑ F : Face P 3, if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) =
      ∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4) := by
    change _ = facetExcess P
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hcard]
    exact hE.symm
  have heq := (Finset.sum_eq_sum_iff_of_le (fun F _ => hpoint F)).mp hsum
  have hlarge (F : Face P 3) (hF : F ∈ nonsimplicialFacets P) :
      facetVertexCount P F = 5 := by
    have h := heq F (Finset.mem_univ _)
    rw [if_pos hF] at h
    omega
  refine ⟨hcard, ?_, hlarge⟩
  intro F
  by_cases hF : F ∈ nonsimplicialFacets P
  · rw [hlarge F hF]
  · have hsmall := mt (mem_nonsimplicialFacets P F).mpr hF
    omega

theorem all_facets_nonsimplicial_of_nine_and_nine {d : ℕ}
    (P : ConvexPolytope d) (hm : Nat.card (Face P 3) = 9)
    (hN : 9 ≤ (nonsimplicialFacets P).card) :
    ∀ F : Face P 3, 5 ≤ facetVertexCount P F := by
  have hcard : (Finset.univ : Finset (Face P 3)).card ≤ (nonsimplicialFacets P).card := by
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hm] using hN
  have heq : nonsimplicialFacets P = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hcard
  intro F
  have hF : F ∈ nonsimplicialFacets P := by rw [heq]; exact Finset.mem_univ _
  have h := (mem_nonsimplicialFacets P F).mp hF
  omega

theorem nonnegative_integer_sum_one {I : Type*} [Fintype I]
    (f : I → ℤ) (hnonneg : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = 1) :
    ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  have hpos : ∃ i, 0 < f i := by
    by_contra h
    push_neg at h
    have hz : ∀ i, f i = 0 := fun i => le_antisymm (h i) (hnonneg i)
    simp only [hz, Finset.sum_const_zero] at hsum
    omega
  obtain ⟨i, hi⟩ := hpos
  have hi_le := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  rw [hsum] at hi_le
  have hi1 : f i = 1 := by omega
  have hpoint (j : I) : (if j = i then (1 : ℤ) else 0) ≤ f j := by
    by_cases hji : j = i
    · subst j
      simp only [if_pos rfl, hi1]
      exact le_rfl
    · simpa only [if_neg hji] using hnonneg j
  have hsum' : (∑ j : I, if j = i then (1 : ℤ) else 0) = ∑ j, f j := by
    rw [hsum]
    simp
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hpoint j)).mp hsum'
  refine ⟨i, hi1, ?_⟩
  intro j hji
  have h := heq j (Finset.mem_univ _)
  simpa only [if_neg hji] using h.symm

theorem nine_facets_ten_excess_unique_six {d : ℕ}
    (P : ConvexPolytope d) (hm : Nat.card (Face P 3) = 9)
    (hN : 9 ≤ (nonsimplicialFacets P).card) (hE : facetExcess P = 10) :
    ∃ F₀ : Face P 3, facetVertexCount P F₀ = 6 ∧
      ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F = 5 := by
  have hmin := all_facets_nonsimplicial_of_nine_and_nine P hm hN
  let f := fun F : Face P 3 => (facetVertexCount P F : ℤ) - 5
  have hnonneg (F : Face P 3) : 0 ≤ f F := by dsimp [f]; have := hmin F; omega
  have hsum : ∑ F, f F = 1 := by
    have hpoint (F : Face P 3) : f F = ((facetVertexCount P F : ℤ) - 4) - 1 := by
      dsimp only [f]
      ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib]
    change facetExcess P - ∑ _F : Face P 3, (1 : ℤ) = 1
    rw [hE]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hm]
    norm_num
  obtain ⟨F₀, hF₀, hother⟩ := nonnegative_integer_sum_one f hnonneg hsum
  refine ⟨F₀, ?_, ?_⟩
  · dsimp [f] at hF₀
    omega
  · intro F hF
    have h := hother F hF
    dsimp [f] at h
    omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart32

section BundlePart33
/- Source: Papers/TenVertexSmallFacetBudgets.lean -/




@[expose] public section

/-!
# The actual small-facet residual has exactly 32 possible budgets

The parameters are the actual facet count, actual nonsimplicial-facet
count, and actual quadrilateral two-face count. The relation count is the
constructed sparse matrix count. The reduction uses the exact Euler and
allocated-nonedge identities; no finite enumeration is assumed.

The finite list is the list used by the 32 direct boundary-search inputs.
This theorem proves that their numerical ranges are exhaustive. It does
not prove that a boundary search within one range is exhaustive.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget

def quadrilateralFaces {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 2) :=
  Finset.univ.filter fun R => Nat.card (VerticesOn P R.val.carrier) = 4

theorem facetExcess_eq_nonsimplicial_count_of_small_facets {d : ℕ}
    (P : ConvexPolytope d)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    facetExcess P = ((nonsimplicialFacets P).card : ℤ) := by
  have hpoint (F : Face P 3) : (facetVertexCount P F : ℤ) - 4 =
      if F ∈ nonsimplicialFacets P then 1 else 0 := by
    have hlo :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
    have hhi := hfacets F
    by_cases hF : F ∈ nonsimplicialFacets P
    · rw [if_pos hF]
      have hbig := (mem_nonsimplicialFacets P F).mp hF
      change 4 ≤ facetVertexCount P F at hlo
      omega
    · rw [if_neg hF]
      have hsmall := mt (mem_nonsimplicialFacets P F).mpr hF
      change 4 ≤ facetVertexCount P F at hlo
      omega
  change (∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4)) = _
  simp_rw [hpoint]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem polygonExcess_eq_quadrilateral_count_of_small_facets {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    polygonExcess P = ((quadrilateralFaces P).card : ℤ) := by
  have hpoint (R : Face P 2) : (Nat.card (VerticesOn P R.val.carrier) : ℤ) - 3 =
      if R ∈ quadrilateralFaces P then 1 else 0 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R
    have hhi := polygon_card_le_four_of_facet_card_le_five P hP hfacets R
    by_cases hR : R ∈ quadrilateralFaces P
    · have hcard : Nat.card (VerticesOn P R.val.carrier) = 4 :=
        (Finset.mem_filter.mp hR).2
      rw [if_pos hR, hcard]
      norm_num
    · have hcard : Nat.card (VerticesOn P R.val.carrier) ≠ 4 := by
        intro h
        exact hR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [if_neg hR]
      omega
  unfold polygonExcess
  simp_rw [hpoint]
  simp

/-- This is the exact square-pyramid count before the independent
five-vertex shape classification is applied: a small facet contributes
one exactly when it contains a quadrilateral. -/
theorem small_facets_one_polygon_excess_count {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ((Finset.univ.filter fun F : Face P 3 => facetPolygonExcess P F = 1).card : ℤ) =
      2 * (quadrilateralFaces P).card := by
  have hpoint (F : Face P 3) : facetPolygonExcess P F =
      if facetPolygonExcess P F = 1 then 1 else 0 := by
    have hlo := polygonExcess_nonnegative (facePolytope P F.val.isFace)
    have hhi := facetPolygonExcess_le_one_of_card_le_five P F (hfacets F)
    change 0 ≤ facetPolygonExcess P F at hlo
    split_ifs <;> omega
  have h := sum_facet_polygon_excess P hP
  have heq : (∑ F : Face P 3, facetPolygonExcess P F) =
      ∑ F : Face P 3, if facetPolygonExcess P F = 1 then (1 : ℤ) else 0 :=
    Finset.sum_congr rfl (fun F _ => hpoint F)
  rw [heq] at h
  rw [polygonExcess_eq_quadrilateral_count_of_small_facets P hP hfacets] at h
  simpa using h

structure SmallFacetBudget where
  m : ℕ
  E : ℕ
  q : ℕ
  deriving DecidableEq

def smallFacetBudgets : List SmallFacetBudget :=
  [⟨10,10,0⟩, ⟨10,10,1⟩,
   ⟨11,10,0⟩, ⟨11,10,1⟩, ⟨11,11,0⟩, ⟨11,11,1⟩, ⟨11,11,2⟩,
   ⟨12,10,0⟩, ⟨12,10,1⟩, ⟨12,11,0⟩, ⟨12,11,1⟩, ⟨12,11,2⟩,
   ⟨12,12,1⟩, ⟨12,12,2⟩, ⟨12,12,3⟩,
   ⟨13,10,0⟩, ⟨13,10,1⟩, ⟨13,11,0⟩, ⟨13,11,1⟩, ⟨13,11,2⟩,
   ⟨13,12,2⟩, ⟨13,12,3⟩, ⟨13,13,4⟩,
   ⟨14,10,0⟩, ⟨14,10,1⟩, ⟨14,11,1⟩, ⟨14,11,2⟩, ⟨14,12,3⟩,
   ⟨15,10,0⟩, ⟨15,10,1⟩, ⟨15,11,2⟩, ⟨16,10,1⟩]

def SmallFacetBudget.Admissible (B : SmallFacetBudget) : Prop :=
  10 ≤ B.m ∧ 10 ≤ B.E ∧ B.E ≤ B.m ∧ B.m + B.E ≤ 26 ∧
    B.q + 9 ≤ B.E ∧ 2 * B.E + B.m ≤ 35 + B.q

instance (B : SmallFacetBudget) : Decidable B.Admissible := by
  unfold SmallFacetBudget.Admissible
  infer_instance

private theorem small_facet_budget_finite_coverage :
    ∀ (m : Fin 17) (E : Fin 14) (q : Fin 5),
      (SmallFacetBudget.mk m.val E.val q.val).Admissible →
        SmallFacetBudget.mk m.val E.val q.val ∈ smallFacetBudgets := by
  decide +kernel

theorem SmallFacetBudget.mem_budgets (B : SmallFacetBudget) (h : B.Admissible) :
    B ∈ smallFacetBudgets := by
  have hm : B.m < 17 := by unfold SmallFacetBudget.Admissible at h; omega
  have hE : B.E < 14 := by unfold SmallFacetBudget.Admissible at h; omega
  have hq : B.q < 5 := by unfold SmallFacetBudget.Admissible at h; omega
  exact small_facet_budget_finite_coverage ⟨B.m, hm⟩ ⟨B.E, hE⟩ ⟨B.q, hq⟩ h

theorem smallFacetBudgets_length : smallFacetBudgets.length = 32 := by decide +kernel

/-- The 32 numerical regimes cover every actual residual whose facets
have at most five vertices. The ten-nonsimplicial-facet and nine-row
hypotheses are precisely the complements of the preceding density
reductions; they do not assert a finite classification. -/
theorem actual_small_facet_budget_mem {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
      (quadrilateralFaces P).card ∈ smallFacetBudgets := by
  apply SmallFacetBudget.mem_budgets
  have hE := facetExcess_eq_nonsimplicial_count_of_small_facets P hfacets
  have hg := polygonExcess_eq_quadrilateral_count_of_small_facets P hP hfacets
  have hcount := actual_sparse_shared_count_of_card_le_five P hP e hfacets
  have hbound := actualSharedRowIndex_count_bound P hP e
  rw [← sparseSharedRowIndex_card_eq] at hbound
  have hexcess := actual_excess_identity P hP
  have hnonedges := (actual_polygon_relation_budget P hP e).1
  rw [hn] at hbound hexcess
  norm_num only [show Nat.choose 10 2 = 45 by decide, Nat.cast_ofNat] at hbound hexcess
  rw [hE, hg] at hcount hexcess
  rw [hE] at hbound hnonedges
  have hcard := Finset.card_le_card (Finset.subset_univ (nonsimplicialFacets P))
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
  unfold SmallFacetBudget.Admissible
  dsimp only [SmallFacetBudget.m, SmallFacetBudget.E, SmallFacetBudget.q]
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart33

section BundlePart34
/- Source: ActualNonedgeFacetCoverage.lean -/





@[expose] public section

/-!
# Exactly which nonedges occur inside facets

The half-weight convention for polygon diagonals counts each covered
nonedge once, regardless of whether it belongs to one or two facets.
Consequently the union of the internal nonedges of facets has cardinal
exactly the allocated weight sum. For facets with at most five vertices,
this cardinal is exactly the number of nonsimplicial facets.

This is a necessary property of every actual polytope in the small-facet
search. It does not assume a classification or a successful search.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeNonedgeAllocation Papers.PolytopeFaceNonedges
open Papers.PolytopeFacetSurplus

variable {d : ℕ}

/-- The actual nonedges whose two endpoints lie in a common facet. -/
def coveredNonedges (P : ConvexPolytope d) : Finset (Nonedge P) :=
  Finset.univ.filter fun e => (CommonFacets P e.val.out.1 e.val.out.2).Nonempty

/-- Each covered nonedge contributes exactly one to the total allocation.
Diagonals have two half contributions; all other covered nonedges have
one whole contribution. -/
theorem pairFacetWeight_sum_eq_indicator (P : ConvexPolytope d)
    (hP : P.dim = 4) (e : Nonedge P) :
    (∑ F : Face P 3, pairFacetWeight P e F) =
      if e ∈ coveredNonedges P then (1 : ℚ) else 0 := by
  rw [pairFacetWeight_sum]
  obtain ⟨hne, hnon⟩ := nonedge_out P e
  by_cases hd : IsPolygonDiagonal P e.val.out.1 e.val.out.2
  · have hc := diagonal_common_facets_card P hP _ _ hne hnon hd
    have hm : e ∈ coveredNonedges P := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Finset.card_pos.mp (by omega)⟩
    rw [if_pos hd, if_pos hm, hc]
    norm_num
  · rw [if_neg hd, mul_one]
    have hle := nonedge_common_facets_le_two P hP _ _ hne hnon
    have hnot : (CommonFacets P e.val.out.1 e.val.out.2).card ≠ 2 := by
      intro hc
      exact hd ((two_common_facets_iff_diagonal P hP _ _ hne hnon).mp hc)
    by_cases hm : e ∈ coveredNonedges P
    · have hpos := Finset.card_pos.mpr (Finset.mem_filter.mp hm).2
      have hc : (CommonFacets P e.val.out.1 e.val.out.2).card = 1 := by omega
      rw [if_pos hm, hc]
      norm_num
    · have hempty : CommonFacets P e.val.out.1 e.val.out.2 = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro h
        exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [if_neg hm, hempty]
      simp

theorem allocated_weight_sum_eq_covered_nonedge_card (P : ConvexPolytope d)
    (hP : P.dim = 4) :
    (∑ F : Face P 3, allocatedFacetWeight P F) =
      ((coveredNonedges P).card : ℚ) := by
  unfold allocatedFacetWeight
  rw [Finset.sum_comm]
  simp_rw [pairFacetWeight_sum_eq_indicator P hP]
  letI : DecidablePred (fun e : Nonedge P => e ∈ coveredNonedges P) :=
    fun e => Finset.decidableMem e (coveredNonedges P)
  have h := Finset.sum_boole (R := ℚ)
    (fun e : Nonedge P => e ∈ coveredNonedges P) Finset.univ
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using h

/-- With at most five vertices in each facet, its allocated contribution
is its number of vertices minus four. -/
theorem small_facet_allocated_weight (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) (F : Face P 3) :
    allocatedFacetWeight P F = (facetVertexCount P F : ℚ) - 4 := by
  rw [allocatedFacetWeight_of_triangles_quadrilaterals P F
    (fun R => polygon_card_le_four_of_facet_card_le_five P hP hfacets R.val)]
  have hlo : 4 ≤ facetVertexCount P F :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  have hhi := hfacets F
  have hc : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 := by omega
  rcases hc with hc | hc <;> rw [hc] <;> norm_num

theorem allocated_weight_sum_of_small_facets (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (∑ F : Face P 3, allocatedFacetWeight P F) =
      ((nonsimplicialFacets P).card : ℚ) := by
  have hpoint (F : Face P 3) : allocatedFacetWeight P F =
      if F ∈ nonsimplicialFacets P then (1 : ℚ) else 0 := by
    rw [small_facet_allocated_weight P hP hfacets]
    have hlo : 4 ≤ facetVertexCount P F :=
      Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
    have hhi := hfacets F
    by_cases hF : F ∈ nonsimplicialFacets P
    · have hc : facetVertexCount P F = 5 := by
        have := (mem_nonsimplicialFacets P F).mp hF
        omega
      rw [if_pos hF, hc]
      norm_num
    · have hc : facetVertexCount P F = 4 := by
        have := mt (mem_nonsimplicialFacets P F).mpr hF
        omega
      rw [if_neg hF, hc]
      norm_num
  simp_rw [hpoint]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The complete union of facet-internal nonedges has exactly `E` members,
where `E` is the actual nonsimplicial-facet count. -/
theorem small_facet_covered_nonedge_card (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (coveredNonedges P).card = (nonsimplicialFacets P).card := by
  have h := (allocated_weight_sum_eq_covered_nonedge_card P hP).symm.trans
    (allocated_weight_sum_of_small_facets P hP hfacets)
  exact_mod_cast h

theorem pairFacetWeight_nonnegative (P : ConvexPolytope d)
    (e : Nonedge P) (F : Face P 3) : 0 ≤ pairFacetWeight P e F := by
  unfold pairFacetWeight
  split_ifs <;> norm_num

/-- A nonedge inside a small facet forces that facet to be nonsimplicial. -/
theorem small_facet_containing_nonedge_is_nonsimplicial (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (e : Nonedge P) (F : Face P 3) (he : Within P F.val.carrier e) :
    F ∈ nonsimplicialFacets P := by
  have hm : F ∈ CommonFacets P e.val.out.1 e.val.out.2 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  have hpos : 0 < pairFacetWeight P e F := by
    unfold pairFacetWeight
    rw [if_pos hm]
    split_ifs <;> norm_num
  have hle : pairFacetWeight P e F ≤ allocatedFacetWeight P F :=
    Finset.single_le_sum (fun f _ => pairFacetWeight_nonnegative P f F)
      (Finset.mem_univ e)
  rw [small_facet_allocated_weight P hP hfacets] at hle
  apply (mem_nonsimplicialFacets P F).mpr
  have hcardQ : (4 : ℚ) < facetVertexCount P F := by linarith
  exact_mod_cast hcardQ

/-- An explicit union formulation, restricted to nonsimplicial facets. -/
theorem small_facet_internal_nonedge_union (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (nonsimplicialFacets P).biUnion
      (fun F => Finset.univ.filter fun e : Nonedge P => Within P F.val.carrier e) =
        coveredNonedges P := by
  ext e
  simp only [coveredNonedges, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨F, _, he⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  · rintro ⟨F, hF⟩
    have he : Within P F.val.carrier e := (Finset.mem_filter.mp hF).2
    exact ⟨F, small_facet_containing_nonedge_is_nonsimplicial P hP hfacets e F he, he⟩

theorem small_facet_internal_nonedge_union_card (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ((nonsimplicialFacets P).biUnion
      (fun F => Finset.univ.filter fun e : Nonedge P => Within P F.val.carrier e)).card =
        (nonsimplicialFacets P).card := by
  rw [small_facet_internal_nonedge_union P hP hfacets]
  exact small_facet_covered_nonedge_card P hP hfacets

/-- Equality of the global nonedge count with `E` forces every global
nonedge to occur in a nonsimplicial facet. -/
theorem small_facet_all_nonedges_covered (P : ConvexPolytope d)
    (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hcount : Nat.card (Nonedge P) = (nonsimplicialFacets P).card)
    (e : Nonedge P) :
    ∃ F ∈ nonsimplicialFacets P, Within P F.val.carrier e := by
  have hcard : (Finset.univ : Finset (Nonedge P)).card ≤ (coveredNonedges P).card := by
    rw [small_facet_covered_nonedge_card P hP hfacets]
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hcount.le
  have hall : coveredNonedges P = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hcard
  have he : e ∈ coveredNonedges P := hall.symm ▸ Finset.mem_univ e
  rw [← small_facet_internal_nonedge_union P hP hfacets] at he
  obtain ⟨F, hF, he⟩ := Finset.mem_biUnion.mp he
  exact ⟨F, hF, (Finset.mem_filter.mp he).2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart34
