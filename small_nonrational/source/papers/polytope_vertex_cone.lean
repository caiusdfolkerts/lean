module
public import Cubical.Polytope.FiguraAlVertice
public import Papers.SimpleCornerFaces
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Actual edge directions at a vertex

The local-to-global step is extracted from the monotone-pivot argument
in the polytope library.  It applies in every intrinsic dimension.
The neighbour directions consequently span the entire direction space.
At a full-dimensional simple vertex they form a basis, and every point
of the polytope has nonnegative coordinates in that basis.
-/

noncomputable section

namespace Papers.PolytopeVertexCone

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped RealInnerProductSpace Classical

variable {n : ℕ}

theorem maximum_on_vertices_of_neighbors (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hxV : x ∈ P.vertices)
    (hlocal : ∀ y, GeneralVertexStep P x y → l y ≤ l x) :
    ∀ z ∈ P.vertices, l z ≤ l x := by
  intro z hzV
  by_contra hnot
  have hlxz : l x < l z := lt_of_not_ge hnot
  have hxFace : P.IsFace ({x} : Set (E n)) := vertex_isFace P hxV
  obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm l
  have hwspec : ∀ y : E n, inner ℝ w y = l y := by
    intro y
    dsimp only [w]
    exact InnerProductSpace.toDual_symm_apply
  have hwconst : ∀ y ∈ ({x} : Set (E n)),
      inner ℝ w y = inner ℝ w x := by
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
  have hwup : ∃ u ∈ P.vertices, inner ℝ w x < inner ℝ w u :=
    ⟨z, hzV, by simpa only [hwspec] using hlxz⟩
  obtain ⟨f, hf, hxf, himprove⟩ :=
    perno_parametrico_crescente_monotono P hxFace g hg x
      (Set.mem_singleton x) w hwconst hwup
  have hfdimpos : 1 ≤ faceDim f := by
    have hlt := faceDim_lt_of_ssubset P hxFace hf hxf
    rw [faceDim_singleton] at hlt
    omega
  obtain ⟨e, he, hde, hxe, hef⟩ :=
    edge_inside_face_at_vertex P hf hxV (hxf.1 (Set.mem_singleton x)) hfdimpos
  obtain ⟨y, hyV, hye, hyne, _hseg⟩ :=
    spigolo_segmento P he hde hxV hxe
  have hynot : y ∉ ({x} : Set (E n)) := by
    simpa [Set.mem_singleton_iff] using hyne
  have hxylt : l x < l y := by
    have hinc := himprove y (hef hye) hynot
    simpa only [hwspec] using hinc
  have hxyle : l y ≤ l x :=
    hlocal y ⟨hyV, hyne.symm, e, he, hde, hxe, hye⟩
  exact (not_lt_of_ge hxyle) hxylt

theorem maximum_on_body_of_neighbors (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hxV : x ∈ P.vertices)
    (hlocal : ∀ y, GeneralVertexStep P x y → l y ≤ l x) :
    ∀ z ∈ P.toSet, l z ≤ l x := by
  have hverts := maximum_on_vertices_of_neighbors P l hxV hlocal
  have hc : Convex ℝ {z : E n | l z ≤ l x} :=
    (convex_Iic (l x)).linear_preimage l.toLinearMap
  exact convexHull_min hverts hc

theorem minimum_on_body_of_neighbors (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hxV : x ∈ P.vertices)
    (hlocal : ∀ y, GeneralVertexStep P x y → l x ≤ l y) :
    ∀ z ∈ P.toSet, l x ≤ l z := by
  have h := maximum_on_body_of_neighbors P (-l) hxV
    (fun y hy => neg_le_neg (hlocal y hy))
  intro z hz
  simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using h z hz

theorem constant_on_body_of_neighbors (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x : E n} (hxV : x ∈ P.vertices)
    (hlocal : ∀ y, GeneralVertexStep P x y → l y = l x) :
    ∀ z ∈ P.toSet, l z = l x := by
  intro z hz
  exact le_antisymm
    (maximum_on_body_of_neighbors P l hxV (fun y hy => (hlocal y hy).le) z hz)
    (minimum_on_body_of_neighbors P l hxV (fun y hy => (hlocal y hy).ge) z hz)

def neighborSpan (P : ConvexPolytope n) (v : E n) : Submodule ℝ (E n) :=
  Submodule.span ℝ ((fun w => w - v) '' {w | GeneralVertexStep P v w})

theorem sub_mem_neighborSpan (P : ConvexPolytope n)
    {v x : E n} (hv : v ∈ P.vertices) (hx : x ∈ P.toSet) :
    x - v ∈ neighborSpan P v := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (neighborSpan P v) (x - v)).mp
  intro l hl
  have hlocal : ∀ w, GeneralVertexStep P v w → l w = l v := by
    intro w hw
    have hmem : w - v ∈ neighborSpan P v :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    have hz := (Submodule.mem_dualAnnihilator l).mp hl (w - v) hmem
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have heq := constant_on_body_of_neighbors P l.toContinuousLinearMap hv hlocal x hx
  change l x = l v at heq
  simpa only [map_sub] using (sub_eq_zero.mpr heq)

theorem neighborSpan_eq_vectorSpan (P : ConvexPolytope n)
    {v : E n} (hv : v ∈ P.vertices) :
    neighborSpan P v = vectorSpan ℝ P.toSet := by
  have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ hw.1) hvT
  · rw [vectorSpan_eq_span_vsub_set_right ℝ hvT]
    apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    exact sub_mem_neighborSpan P hv hw

def actualNeighbors (P : ConvexPolytope n) (v : E n) : Finset (E n) :=
  P.vertices.filter (GeneralVertexStep P v)

theorem mem_actualNeighbors_iff (P : ConvexPolytope n) (v w : E n) :
    w ∈ actualNeighbors P v ↔ GeneralVertexStep P v w := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨h.1, h⟩

theorem neighborSpan_eq_range_span (P : ConvexPolytope n) (v : E n) :
    neighborSpan P v =
      Submodule.span ℝ (Set.range (fun w : actualNeighbors P v => (w : E n) - v)) := by
  unfold neighborSpan
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, (mem_actualNeighbors_iff P v w).mpr hw⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, (mem_actualNeighbors_iff P v w).mp w.2, rfl⟩

/-- The intrinsic simple-vertex statement also applies to a facet embedded
in a larger ambient space. -/
theorem neighbor_directions_independent_of_card_eq_dim
    (P : ConvexPolytope n) {v : E n} (hv : v ∈ P.vertices)
    (hsimple : (actualNeighbors P v).card = P.dim) :
    LinearIndependent ℝ (fun w : actualNeighbors P v => (w : E n) - v) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (actualNeighbors P v) =
    finrank ℝ (Submodule.span ℝ
      (Set.range (fun w : actualNeighbors P v => (w : E n) - v)))
  rw [← neighborSpan_eq_range_span, neighborSpan_eq_vectorSpan P hv]
  simpa only [Fintype.card_coe, ConvexPolytope.dim] using hsimple

theorem neighborSpan_eq_top (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {v : E n} (hv : v ∈ P.vertices) :
    neighborSpan P v = ⊤ := by
  rw [neighborSpan_eq_vectorSpan P hv]
  apply Submodule.eq_top_of_finrank_eq
  calc
    finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
    _ = finrank ℝ (E n) := by simp [E]

def actualNeighborBasis (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {v : E n} (hv : v ∈ P.vertices) (hsimple : (actualNeighbors P v).card = n) :
    Basis (actualNeighbors P v) ℝ (E n) :=
  basisOfTopLeSpanOfCardEqFinrank (fun w => (w : E n) - v)
    (by rw [← neighborSpan_eq_range_span, neighborSpan_eq_top P hfull hv])
    (by simpa [E] using hsimple)

theorem actualNeighborBasis_apply (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {v : E n} (hv : v ∈ P.vertices) (hsimple : (actualNeighbors P v).card = n)
    (w : actualNeighbors P v) :
    actualNeighborBasis P hfull hv hsimple w = (w : E n) - v := by
  simp only [actualNeighborBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem actualNeighborBasis_coordinates_nonnegative
    (P : ConvexPolytope n) (hfull : P.IsFullDim)
    {v : E n} (hv : v ∈ P.vertices) (hsimple : (actualNeighbors P v).card = n)
    {x : E n} (hx : x ∈ P.toSet) (i : actualNeighbors P v) :
    0 ≤ (actualNeighborBasis P hfull hv hsimple).repr (x - v) i := by
  let b := actualNeighborBasis P hfull hv hsimple
  let l : E n →ₗ[ℝ] ℝ := (Finsupp.lapply i).comp b.repr.toLinearMap
  have hlocal : ∀ w, GeneralVertexStep P v w →
      l.toContinuousLinearMap v ≤ l.toContinuousLinearMap w := by
    intro w hw
    let j : actualNeighbors P v := ⟨w, (mem_actualNeighbors_iff P v w).mpr hw⟩
    have hb : b j = w - v := actualNeighborBasis_apply P hfull hv hsimple j
    have hn : 0 ≤ b.repr (w - v) i := by
      rw [← hb, b.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    have heq : l (w - v) = b.repr (w - v) i := rfl
    have hnonneg : 0 ≤ l (w - v) := by
      rw [heq]
      exact hn
    have hle : 0 ≤ l w - l v := by
      simpa only [map_sub] using hnonneg
    exact sub_nonneg.mp hle
  have hle := minimum_on_body_of_neighbors P l.toContinuousLinearMap hv hlocal x hx
  change l v ≤ l x at hle
  change 0 ≤ l (x - v)
  simpa only [map_sub, sub_nonneg] using hle

end Papers.PolytopeVertexCone
