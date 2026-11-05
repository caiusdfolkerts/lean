module
public import consolidated.deletion_fields
public import consolidated.root_graph
public import consolidated_dev.intrinsic_figure_geometry
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option Elab.async false

section BundlePart0
/- Source: Papers/PolytopeVertexCone.lean -/







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

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/FaceVertexCardinality.lean -/





@[expose] public section

/-!
# Dimension bounds from the actual vertices of a face

A nonempty set of affine dimension r cannot lie in the convex hull of
fewer than r + 1 points.  The result is also provided for injective affine
images, which is the form needed when an exposed Minkowski face contains
a translated face of a summand.  The containing finite set is explicit;
it must be identified with the actual face vertices in the application.
-/

namespace Papers.FaceVertexCardinality

open Set Module
open Papers.HomogeneousSpanDimension

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem liftSpan_mono {S T : Set E} (h : S ⊆ T) :
    liftSpan S ≤ liftSpan T :=
  Submodule.span_mono (Set.image_mono h)

theorem liftSpan_convexHull (S : Set E) :
    liftSpan (convexHull ℝ S) = liftSpan S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    have hconv : Convex ℝ {y : E | liftPoint y ∈ liftSpan S} := by
      intro y hy z hz a b ha hb hab
      change liftPoint (a • y + b • z) ∈ liftSpan S
      have heq : liftPoint (a • y + b • z) =
          a • liftPoint y + b • liftPoint z := by
        apply Prod.ext
        · rfl
        · change (1 : ℝ) = a * 1 + b * 1
          simpa only [mul_one] using hab.symm
      rw [heq]
      exact (liftSpan S).add_mem ((liftSpan S).smul_mem a hy)
        ((liftSpan S).smul_mem b hz)
    exact convexHull_min (fun y hy => liftPoint_mem hy) hconv hx
  · exact liftSpan_mono (subset_convexHull ℝ S)

theorem finrank_vectorSpan_affineImage
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f.linear) (S : Set E) :
    finrank ℝ (vectorSpan ℝ (f '' S)) =
      finrank ℝ (vectorSpan ℝ S) := by
  rw [← AffineMap.map_vectorSpan f]
  have hinj : Function.Injective
      (f.linear.comp (vectorSpan ℝ S).subtype) :=
    hf.comp Subtype.val_injective
  have h := LinearMap.finrank_range_of_inj hinj
  have hrange : (f.linear.comp (vectorSpan ℝ S).subtype).range =
      (vectorSpan ℝ S).map f.linear := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at h
  exact h

variable [FiniteDimensional ℝ E]

theorem finrank_liftSpan_finset_le_card (X : Finset E) :
    finrank ℝ (liftSpan (X : Set E)) ≤ X.card := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) (X.image liftPoint)
  change finrank ℝ (Submodule.span ℝ ((X.image liftPoint : Finset (E × ℝ)) : Set (E × ℝ))) ≤
    (X.image liftPoint).card at h
  have hset : ((X.image liftPoint : Finset (E × ℝ)) : Set (E × ℝ)) =
      liftPoint '' (X : Set E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  rw [hset] at h
  have h' : finrank ℝ (liftSpan (X : Set E)) ≤
      (X.image liftPoint).card := by
    exact h
  exact h'.trans Finset.card_image_le

theorem dimension_add_one_le_card_of_subset_hull
    {S : Set E} (hS : S.Nonempty) (X : Finset E)
    (hSX : S ⊆ convexHull ℝ (X : Set E)) :
    finrank ℝ (vectorSpan ℝ S) + 1 ≤ X.card := by
  calc
    finrank ℝ (vectorSpan ℝ S) + 1 =
        finrank ℝ (liftSpan S) := (finrank_liftSpan hS).symm
    _ ≤ finrank ℝ (liftSpan (convexHull ℝ (X : Set E))) :=
      Submodule.finrank_mono (liftSpan_mono hSX)
    _ = finrank ℝ (liftSpan (X : Set E)) := by rw [liftSpan_convexHull]
    _ ≤ X.card := finrank_liftSpan_finset_le_card X

variable [FiniteDimensional ℝ F]

theorem dimension_add_one_le_card_of_affineImage_subset_hull
    {S : Set E} (hS : S.Nonempty)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f.linear)
    (X : Finset F) (hSX : f '' S ⊆ convexHull ℝ (X : Set F)) :
    finrank ℝ (vectorSpan ℝ S) + 1 ≤ X.card := by
  have h := dimension_add_one_le_card_of_subset_hull
    (hS.image f) X hSX
  simpa only [finrank_vectorSpan_affineImage f hf] using h

end Papers.FaceVertexCardinality

end
end BundlePart1

section BundlePart2
/- Source: Papers/PolytopeBalinski.lean -/







@[expose] public section

/-!
# Intrinsic Balinski connectivity

Deleting fewer than dim P vertices leaves the actual edge graph
connected.  The proof uses a height constant on the removed points and
one retained anchor, monotone edge pivots, and finite perturbations.
The ambient space may have dimension greater than dim P.
-/

noncomputable section
namespace Papers.PolytopeBalinski

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone Papers.FiniteGraphOptimization
open scoped Classical

variable {n : ℕ}

def vertexGraph (P : ConvexPolytope n) : SimpleGraph P.vertices where
  Adj x y := GeneralVertexStep P (x : E n) (y : E n)
  symm := ⟨by
    rintro x y ⟨hy, hxy, e, he, hde, hxe, hye⟩
    exact ⟨x.2, hxy.symm, e, he, hde, hye, hxe⟩⟩
  loopless := ⟨by
    rintro x ⟨_, hne, _⟩
    exact hne rfl⟩

theorem exists_improving_neighbor (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) {x z : E n}
    (hx : x ∈ P.vertices) (hz : z ∈ P.vertices) (hlt : l x < l z) :
    ∃ y, GeneralVertexStep P x y ∧ l x < l y := by
  by_contra hn
  have hlocal : ∀ y, GeneralVertexStep P x y → l y ≤ l x := by
    intro y hy
    by_contra hny
    exact hn ⟨y, hy, lt_of_not_ge hny⟩
  have hle := maximum_on_vertices_of_neighbors P l hx hlocal z hz
  exact (not_lt_of_ge hle) hlt

theorem exists_strict_vertex_exposer (P : ConvexPolytope n)
    {q : E n} (hq : q ∈ P.vertices) :
    ∃ g : E n →L[ℝ] ℝ, ∀ v ∈ P.vertices, v ≠ q → g v < g q := by
  obtain ⟨g, hg⟩ := (vertex_isFace P hq).1 (Set.singleton_nonempty q)
  have hqmax : ∀ v ∈ P.toSet, g v ≤ g q := by
    have hmem : q ∈ ({q} : Set (E n)) := Set.mem_singleton q
    rw [hg] at hmem
    exact hmem.2
  refine ⟨g, ?_⟩
  intro v hv hvq
  have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv
  rcases lt_or_eq_of_le (hqmax v hvT) with hlt | heq
  · exact hlt
  · have hmem : v ∈ ({q} : Set (E n)) := by
      rw [hg]
      refine ⟨hvT, ?_⟩
      intro w hw
      rw [heq]
      exact hqmax w hw
    exact (hvq (Set.mem_singleton_iff.mp hmem)).elim

theorem positive_vertexGraph_connected (P : ConvexPolytope n)
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hpos : ∃ v ∈ P.vertices, c < l v) :
    ((vertexGraph P).induce {v : P.vertices | c < l (v : E n)}).Connected := by
  classical
  obtain ⟨q, hq, hqmax⟩ :=
    Finset.exists_max_image P.vertices l P.vertices_nonempty
  have hqpos : c < l q := by
    obtain ⟨v, hv, hvc⟩ := hpos
    exact hvc.trans_le (hqmax v hv)
  obtain ⟨g, hg⟩ := exists_strict_vertex_exposer P hq
  let pairs := (P.vertices.product P.vertices).filter
    (fun p : E n × E n => c < l p.1 ∧ l p.2 ≤ c)
  have hgap : ∀ p ∈ pairs, 0 < l p.1 - l p.2 := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    exact sub_pos.mpr (hc.2.trans_lt hc.1)
  obtain ⟨ε, hε, hpert⟩ :=
    exists_small_positive_perturbation pairs
      (fun p => l p.1 - l p.2) (fun p => g p.1 - g p.2) hgap
  let L : E n →L[ℝ] ℝ := l + ε • g
  have horder : ∀ v ∈ P.vertices, ∀ w ∈ P.vertices,
      c < l v → l w ≤ c → L w < L v := by
    intro v hv w hw hvc hwc
    have hp : (v,w) ∈ pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hvc,hwc⟩
    have hh := hpert ε hε le_rfl (v,w) hp
    change 0 < l v - l w + ε * (g v - g w) at hh
    change l w + ε * g w < l v + ε * g v
    nlinarith
  have hLmax : ∀ v ∈ P.vertices, v ≠ q → L v < L q := by
    intro v hv hvq
    have hl := hqmax v hv
    have hh := mul_lt_mul_of_pos_left (hg v hv hvq) hε
    change l v + ε * g v < l q + ε * g q
    linarith
  let Pos : Set P.vertices := {v | c < l (v : E n)}
  let H := (vertexGraph P).induce Pos
  letI : Fintype Pos := Fintype.ofFinite _
  let m : Pos := ⟨⟨q,hq⟩,hqpos⟩
  apply connected_of_strict_descent H (fun v => -L (v.1 : E n)) m
  intro v hvm
  have hvq : (v.1 : E n) ≠ q := by
    intro heq
    apply hvm
    apply Subtype.ext
    exact Subtype.ext heq
  obtain ⟨w, hvw, hwL⟩ :=
    exists_improving_neighbor P L v.1.2 hq (hLmax _ v.1.2 hvq)
  have hwpos : c < l w := by
    by_contra hnot
    have hh := horder _ v.1.2 w hvw.1 v.2 (le_of_not_gt hnot)
    exact (not_lt_of_ge hwL.le) hh
  refine ⟨⟨⟨w,hvw.1⟩,hwpos⟩,hvw,?_⟩
  exact neg_lt_neg hwL

theorem height_constant_on_small_set (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim)
    {v : E n} (hv : v ∈ P.vertices) :
    ∃ l : E n →L[ℝ] ℝ,
      (∀ s ∈ S, l s = l v) ∧ ∃ w ∈ P.vertices, l v < l w := by
  let U : Submodule ℝ (E n) :=
    Submodule.span ℝ (Set.range (fun s : S => (s : E n) - v))
  have hU : finrank ℝ U ≤ S.card := by
    have h := finrank_range_le_card (R := ℝ) (fun s : S => (s : E n) - v)
    simpa only [U, Set.finrank, Fintype.card_coe] using h
  have hnotle : ¬ neighborSpan P v ≤ U := by
    intro hle
    have hh := Submodule.finrank_mono hle
    rw [neighborSpan_eq_vectorSpan P hv] at hh
    change P.dim ≤ finrank ℝ U at hh
    omega
  have hout : ∃ w, GeneralVertexStep P v w ∧ w - v ∉ U := by
    by_contra h
    push_neg at h
    apply hnotle
    apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    exact h w hw
  obtain ⟨w, hw, hwU⟩ := hout
  have hnotall : ¬ ∀ φ : Module.Dual ℝ (E n),
      φ ∈ U.dualAnnihilator → φ (w - v) = 0 := by
    intro h
    exact hwU ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (w-v)).mp h)
  push_neg at hnotall
  obtain ⟨φ, hφ, hφwv⟩ := hnotall
  have htie : ∀ s ∈ S, φ s = φ v := by
    intro s hs
    have hmem : s - v ∈ U := Submodule.subset_span ⟨⟨s,hs⟩,rfl⟩
    have hz := (Submodule.mem_dualAnnihilator φ).mp hφ (s-v) hmem
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have hne : φ w ≠ φ v := by
    intro heq
    apply hφwv
    rw [map_sub, heq, sub_self]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨-φ.toContinuousLinearMap,?_,w,hw.1,?_⟩
    · intro s hs
      change -φ s = -φ v
      rw [htie s hs]
    · exact neg_lt_neg hlt
  · exact ⟨φ.toContinuousLinearMap,htie,w,hw.1,hgt⟩

theorem deleted_reachable_of_nonnegative_height
    (P : ConvexPolytope n) (S : Finset (E n))
    (l : E n →L[ℝ] ℝ) (c : ℝ)
    (hS : ∀ s ∈ S, l s = c)
    (hpos : ∃ v ∈ P.vertices, c < l v)
    (x y : {v : P.vertices | (v : E n) ∉ S})
    (hx : c ≤ l (x.1 : E n)) (hy : c ≤ l (y.1 : E n)) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Reachable x y := by
  let Pos : Set P.vertices := {v | c < l (v : E n)}
  let Del : Set P.vertices := {v | (v : E n) ∉ S}
  let G := vertexGraph P
  have hsub : Pos ⊆ Del := by
    intro v hv hvS
    have hh := hS v hvS
    exact (ne_of_gt hv) hh
  let inclusion : G.induce Pos →g G.induce Del :=
    (G.induceHomOfLE hsub).toHom
  have htoPos : ∀ v : Del, c ≤ l (v.1 : E n) →
      ∃ w : Pos, (G.induce Del).Reachable v (inclusion w) := by
    intro v hv
    by_cases hvpos : c < l (v.1 : E n)
    · exact ⟨⟨v.1,hvpos⟩,SimpleGraph.Reachable.rfl⟩
    · have hvlevel : l (v.1 : E n) = c := le_antisymm (le_of_not_gt hvpos) hv
      obtain ⟨q,hq,hqpos⟩ := hpos
      obtain ⟨w,hvw,hwlevel⟩ :=
        exists_improving_neighbor P l v.1.2 hq (by rw [hvlevel]; exact hqpos)
      have hwpos : c < l w := by simpa only [hvlevel] using hwlevel
      let ww : Pos := ⟨⟨w,hvw.1⟩,hwpos⟩
      have hadj : (G.induce Del).Adj v (inclusion ww) := hvw
      exact ⟨ww,hadj.reachable⟩
  obtain ⟨xp,hxp⟩ := htoPos x hx
  obtain ⟨yp,hyp⟩ := htoPos y hy
  have hpconn := positive_vertexGraph_connected P l c hpos
  have hp : (G.induce Pos).Reachable xp yp := hpconn.preconnected xp yp
  exact hxp.trans ((hp.map inclusion).trans hyp.symm)

theorem deleted_vertexGraph_reachable (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim)
    (x y : {v : P.vertices | (v : E n) ∉ S}) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Reachable x y := by
  obtain ⟨l,hS,hpos⟩ := height_constant_on_small_set P S hcard x.1.2
  by_cases hy : l (x.1 : E n) ≤ l (y.1 : E n)
  · exact deleted_reachable_of_nonnegative_height P S l (l x.1) hS hpos
      x y le_rfl hy
  · have hylt : l (y.1 : E n) < l (x.1 : E n) := lt_of_not_ge hy
    apply deleted_reachable_of_nonnegative_height P S (-l) (-l x.1)
    · intro s hs
      change -l s = -l x.1
      rw [hS s hs]
    · exact ⟨y.1,y.1.2,neg_lt_neg hylt⟩
    · exact le_rfl
    · exact neg_le_neg hylt.le

theorem deleted_vertexGraph_connected (P : ConvexPolytope n)
    (S : Finset (E n)) (hcard : S.card < P.dim) :
    ((vertexGraph P).induce {v : P.vertices | (v : E n) ∉ S}).Connected := by
  have hnonempty : ∃ v ∈ P.vertices, v ∉ S := by
    by_contra h
    push_neg at h
    have hsubset : P.vertices ⊆ S := h
    have hcount := Finset.card_le_card hsubset
    have hbody : P.toSet.Nonempty := by
      obtain ⟨v,hv⟩ := P.vertices_nonempty
      exact ⟨v,subset_convexHull ℝ _ hv⟩
    have hdim := Papers.FaceVertexCardinality.dimension_add_one_le_card_of_subset_hull
      hbody P.vertices Set.Subset.rfl
    change P.dim + 1 ≤ P.vertices.card at hdim
    omega
  obtain ⟨v,hv,hvS⟩ := hnonempty
  letI : Nonempty {w : P.vertices | (w : E n) ∉ S} := ⟨⟨⟨v,hv⟩,hvS⟩⟩
  exact { preconnected := deleted_vertexGraph_reachable P S hcard }

theorem vertexGraph_connected (P : ConvexPolytope n) :
    (vertexGraph P).Connected := by
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  have hpos : ∃ w ∈ P.vertices, (-1 : ℝ) < (0 : E n →L[ℝ] ℝ) w :=
    ⟨v,hv,by norm_num⟩
  let T : Set P.vertices := {w | (-1 : ℝ) < (0 : E n →L[ℝ] ℝ) (w : E n)}
  have hconn : ((vertexGraph P).induce T).Connected :=
    positive_vertexGraph_connected P 0 (-1) hpos
  letI : Nonempty P.vertices := ⟨⟨v,hv⟩⟩
  refine { preconnected := ?_ }
  intro x y
  have hx : x ∈ T := by norm_num [T]
  have hy : y ∈ T := by norm_num [T]
  exact (hconn.preconnected ⟨x,hx⟩ ⟨y,hy⟩).map
    (SimpleGraph.Embedding.induce T).toHom

theorem vertexGraph_preconnected (P : ConvexPolytope n) :
    (vertexGraph P).Preconnected :=
  (vertexGraph_connected P).preconnected

theorem vertexGraph_delete_one_connected (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) (q : P.vertices) :
    ((vertexGraph P).induce {r : P.vertices | r ≠ q}).Connected := by
  have hcard : ({(q : E n)} : Finset (E n)).card < P.dim := by
    simpa only [Finset.card_singleton] using (show 1 < P.dim by omega)
  have hc := deleted_vertexGraph_connected P {(q : E n)} hcard
  have hset : {r : P.vertices | (r : E n) ∉ ({(q : E n)} : Finset (E n))} =
      {r : P.vertices | r ≠ q} := by
    ext r
    constructor
    · intro h heq
      apply h
      exact Finset.mem_singleton.mpr (congrArg Subtype.val heq)
    · intro h hr
      apply h
      exact Subtype.ext (Finset.mem_singleton.mp hr)
  rw [hset] at hc
  exact hc

theorem vertexGraph_delete_one_preconnected (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) (q : P.vertices) :
    ((vertexGraph P).induce {r : P.vertices | r ≠ q}).Preconnected :=
  (vertexGraph_delete_one_connected P hdim q).preconnected

end Papers.PolytopeBalinski

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ActualFaceOrder.lean -/




@[expose] public section

/-!
# Transport through the actual face order

The objects are all nonempty exposed faces of the geometric polytope,
ordered by set inclusion.  Vertex transport is derived from minimal
faces.  Dimension preservation follows by induction using genuine
facets of genuine face polytopes; it is not supplied as a certificate.
-/

noncomputable section
namespace Papers.ActualFaceOrder

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n m : ℕ}

abbrev FaceObject (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

def vertexFace (P : ConvexPolytope n) (v : P.vertices) : FaceObject P :=
  ⟨{(v : E n)},vertex_isFace P v.2⟩

theorem vertexFace_injective (P : ConvexPolytope n) :
    Function.Injective (vertexFace P) := by
  intro v w h
  apply Subtype.ext
  have hs : ({(v : E n)} : Set (E n)) = {(w : E n)} :=
    congrArg Subtype.val h
  exact Set.singleton_injective hs

private theorem nonempty_subset_singleton_eq {X : Type*} {S : Set X} {x : X}
    (hS : S.Nonempty) (hsub : S ⊆ {x}) : S = {x} := by
  apply Set.Subset.antisymm hsub
  intro y hy
  obtain ⟨z,hz⟩ := hS
  have hzx : z = x := Set.mem_singleton_iff.mp (hsub hz)
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  simpa only [hyx, hzx] using hz

theorem image_vertex_is_singleton {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : P.vertices) :
    ∃ q : Q.vertices, (e (vertexFace P v)).val = {(q : E m)} := by
  let F := e (vertexFace P v)
  let R := facePolytope Q F.property
  obtain ⟨q,hq⟩ := R.vertices_nonempty
  have hqfilter : q ∈ Q.vertices.filter (· ∈ F.val) := hq
  have hqQ : q ∈ Q.vertices := (Finset.mem_filter.mp hqfilter).1
  have hqF : q ∈ F.val := (Finset.mem_filter.mp hqfilter).2
  let qq : Q.vertices := ⟨q,hqQ⟩
  have hsub : vertexFace Q qq ≤ F := by
    intro z hz
    have hzq : z = q := Set.mem_singleton_iff.mp hz
    simpa only [hzq] using hqF
  have hpre : e.symm (vertexFace Q qq) ≤ vertexFace P v := by
    simpa only [F, e.symm_apply_apply] using e.symm.monotone hsub
  have heqpre : e.symm (vertexFace Q qq) = vertexFace P v := by
    apply Subtype.ext
    exact nonempty_subset_singleton_eq
      (e.symm (vertexFace Q qq)).property.2 hpre
  have himage : vertexFace Q qq = F := by
    apply e.symm.injective
    simpa only [F, e.symm_apply_apply] using heqpre
  exact ⟨qq,(congrArg Subtype.val himage).symm⟩

def vertexMap {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : P.vertices) : Q.vertices :=
  (image_vertex_is_singleton e v).choose

theorem vertexMap_face {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : P.vertices) :
    vertexFace Q (vertexMap e v) = e (vertexFace P v) := by
  apply Subtype.ext
  exact (image_vertex_is_singleton e v).choose_spec.symm

def vertexEquiv {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) : P.vertices ≃ Q.vertices where
  toFun := vertexMap e
  invFun := vertexMap e.symm
  left_inv v := by
    apply vertexFace_injective P
    rw [vertexMap_face,vertexMap_face]
    exact e.symm_apply_apply _
  right_inv v := by
    apply vertexFace_injective Q
    rw [vertexMap_face,vertexMap_face]
    exact e.apply_symm_apply _

@[simp] theorem vertexEquiv_apply {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : P.vertices) :
    vertexEquiv e v = vertexMap e v := rfl

@[simp] theorem vertexEquiv_symm_apply {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : Q.vertices) :
    (vertexEquiv e).symm v = vertexMap e.symm v := rfl

theorem vertex_mem_face_iff {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (v : P.vertices) (F : FaceObject P) :
    (vertexEquiv e v : E m) ∈ (e F).val ↔ (v : E n) ∈ F.val := by
  constructor
  · intro hv
    have hsub : vertexFace Q (vertexMap e v) ≤ e F :=
      Set.singleton_subset_iff.mpr hv
    rw [vertexMap_face] at hsub
    have hpre : vertexFace P v ≤ F := e.le_iff_le.mp hsub
    exact hpre (Set.mem_singleton _)
  · intro hv
    have hsub : vertexFace P v ≤ F := Set.singleton_subset_iff.mpr hv
    have him := e.monotone hsub
    rw [← vertexMap_face] at him
    exact him (Set.mem_singleton _)

theorem faceDim_le_image {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (F : FaceObject P) :
    faceDim F.val ≤ faceDim (e F).val := by
  have h : ∀ k : ℕ, ∀ F : FaceObject P, faceDim F.val = k →
      k ≤ faceDim (e F).val := by
    intro k
    induction k with
    | zero =>
        intro F hF
        exact Nat.zero_le _
    | succ k ih =>
        intro F hF
        let R := facePolytope P F.property
        have hRdim : Module.finrank ℝ (vectorSpan ℝ R.toSet) = k + 1 := by
          rw [facePolytope_toSet P F.property]
          exact hF
        obtain ⟨G,hG,hGdim⟩ := facet_exists R (by omega)
        have hGdim : faceDim G = k := by
          rw [hRdim] at hGdim
          simpa only [Nat.add_sub_cancel] using hGdim
        have hGP : P.IsFace G := isFace_of_facePolytope P F.property hG
        have hGF : G ⊆ F.val := by
          rw [← facePolytope_toSet P F.property]
          exact face_subset_toSet R hG
        have hne : G ≠ F.val := by
          intro heq
          rw [heq,hF] at hGdim
          omega
        let GG : FaceObject P := ⟨G,hGP⟩
        have hproper : GG < F :=
          ⟨hGF,fun hFG => hne (Set.Subset.antisymm hGF hFG)⟩
        have him : e GG < e F := e.strictMono hproper
        have hdimlt :=
          faceDim_lt_of_ssubset Q (e GG).property (e F).property him
        have hkle := ih GG hGdim
        omega
  exact h _ F rfl

theorem faceDim_image {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (F : FaceObject P) :
    faceDim (e F).val = faceDim F.val := by
  apply le_antisymm
  · simpa only [e.symm_apply_apply] using faceDim_le_image e.symm (e F)
  · exact faceDim_le_image e F

theorem edge_forward {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (x y : P.vertices)
    (h : GeneralVertexStep P (x : E n) (y : E n)) :
    GeneralVertexStep Q (vertexEquiv e x : E m) (vertexEquiv e y : E m) := by
  obtain ⟨hy,hxy,F,hF,hFdim,hxF,hyF⟩ := h
  let FF : FaceObject P := ⟨F,hF⟩
  refine ⟨(vertexEquiv e y).2,?_,(e FF).val,(e FF).property,?_,?_,?_⟩
  · intro heq
    have hvertices : vertexEquiv e x = vertexEquiv e y := Subtype.ext heq
    exact hxy (congrArg Subtype.val ((vertexEquiv e).injective hvertices))
  · rw [faceDim_image]
    exact hFdim
  · exact (vertex_mem_face_iff e x FF).mpr hxF
  · exact (vertex_mem_face_iff e y FF).mpr hyF

theorem edge_iff {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) (x y : P.vertices) :
    GeneralVertexStep Q (vertexEquiv e x : E m) (vertexEquiv e y : E m) ↔
      GeneralVertexStep P (x : E n) (y : E n) := by
  constructor
  · intro h
    have hback := edge_forward e.symm (vertexEquiv e x) (vertexEquiv e y) h
    change GeneralVertexStep P
      ((vertexEquiv e).symm (vertexEquiv e x) : E n)
      ((vertexEquiv e).symm (vertexEquiv e y) : E n) at hback
    simpa only [Equiv.symm_apply_apply] using hback
  · exact edge_forward e x y

def topFace (P : ConvexPolytope n) : FaceObject P :=
  ⟨P.toSet,toSet_isFace P⟩

theorem image_topFace {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) :
    e (topFace P) = topFace Q := by
  apply le_antisymm
  · exact face_subset_toSet Q (e (topFace P)).property
  · have hpre : e.symm (topFace Q) ≤ topFace P :=
      face_subset_toSet P (e.symm (topFace Q)).property
    simpa only [e.apply_symm_apply] using e.monotone hpre

theorem dim_eq {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) : Q.dim = P.dim := by
  have h := faceDim_image e (topFace P)
  rw [image_topFace] at h
  exact h

theorem vertices_card_eq {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q) :
    P.vertices.card = Q.vertices.card := by
  simpa using Fintype.card_congr (vertexEquiv e)

end Papers.ActualFaceOrder

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ExposedEdgeCenters.lean -/
@[expose] public section









/-!
# A crossing center inside a polytope

This file uses the ordinary exposed-segment and extreme-point properties of
actual polytope edges and vertices.  It proves the geometric classification
before any counting or graph connectivity is invoked.
-/

namespace Papers.Polytopes.ExposedEdgeCenters

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

def point (x : V) : V × ℝ := (x, 1)

def edgeLine (x y : V) : Submodule ℝ (V × ℝ) :=
  Submodule.span ℝ ({point x, point y} : Set (V × ℝ))

theorem convex_point_image (C : Set V) (hC : Convex ℝ C) :
    Convex ℝ (point '' C) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hC hx hy ha hb hab, ?_⟩
  apply Prod.ext
  · rfl
  · change 1 = a * 1 + b * 1
    simpa using hab.symm

/-- Homogeneous linear extension of an ordinary affine form. -/
def affineForm (g : V →ᵃ[ℝ] ℝ) : (V × ℝ) →ₗ[ℝ] ℝ where
  toFun p := g.linear p.1 + p.2 * g 0
  map_add' p q := by
    change g.linear (p.1 + q.1) + (p.2 + q.2) * g 0 =
      (g.linear p.1 + p.2 * g 0) + (g.linear q.1 + q.2 * g 0)
    rw [map_add]
    ring
  map_smul' c p := by
    change g.linear (c • p.1) + (c * p.2) * g 0 =
      c * (g.linear p.1 + p.2 * g 0)
    rw [map_smul]
    change c * g.linear p.1 + (c * p.2) * g 0 =
      c * (g.linear p.1 + p.2 * g 0)
    ring

@[simp]
theorem affineForm_point (g : V →ᵃ[ℝ] ℝ) (x : V) :
    affineForm g (point x) = g x := by
  change g.linear x + 1 * g 0 = g x
  rw [one_mul]
  simpa only [vadd_eq_add, add_zero] using (g.map_vadd (0 : V) x).symm


theorem point_weighted_sum (x y : V) (a b : ℝ) (hab : a + b = 1) :
    point (a • x + b • y) = a • point x + b • point y := by
  apply Prod.ext
  · rfl
  · change 1 = a * 1 + b * 1
    simpa using hab.symm

theorem affine_apply_weighted_sum
    (g : V →ᵃ[ℝ] ℝ) (x y : V) (a b : ℝ) (hab : a + b = 1) :
    g (a • x + b • y) = a * g x + b * g y := by
  rw [← affineForm_point, point_weighted_sum x y a b hab, map_add,
    map_smul, map_smul, affineForm_point, affineForm_point]
  rfl

/-- An actual nonnegative affine support exposing a segment makes that
segment an extreme subset of the convex body. -/
theorem isExtreme_segment_of_affine_support
    (C : Set V) (hC : Convex ℝ C) (g : V →ᵃ[ℝ] ℝ)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C)
    (hnonneg : ∀ z ∈ C, 0 ≤ g z)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y) :
    IsExtreme ℝ C (segment ℝ x y) := by
  have hsub : segment ℝ x y ⊆ C := by
    rintro z ⟨a,b,ha,hb,hab,rfl⟩
    exact hC hx hy ha hb hab
  refine ⟨hsub, ?_⟩
  intro u hu v hv z hz hzopen
  obtain ⟨a,b,ha,hb,hab,habz⟩ := hzopen
  have hgz : g z = 0 := (hzero z (hsub hz)).mpr hz
  have hsum : a * g u + b * g v = 0 := by
    rw [← affine_apply_weighted_sum g u v a b hab, habz]
    exact hgz
  have hgu : g u = 0 := by
    by_contra hne
    have hpositive : 0 < a * g u :=
      mul_pos ha (lt_of_le_of_ne (hnonneg u hu) (by intro h; exact hne h.symm))
    have hsecond : 0 ≤ b * g v := mul_nonneg hb.le (hnonneg v hv)
    linarith
  exact (hzero u hu).mp hgu

theorem point_ne_zero (x : V) : point x ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  norm_num [point] at this

theorem edgeLine_le_ker_affineForm
    (g : V →ᵃ[ℝ] ℝ) {x y : V} (hx : g x = 0) (hy : g y = 0) :
    edgeLine x y ≤ (affineForm g).ker := by
  refine Submodule.span_le.mpr ?_
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · change affineForm g (point x) = 0
    simpa using hx
  · have hw' : w = point y := Set.mem_singleton_iff.mp hw
    subst w
    change affineForm g (point y) = 0
    simpa using hy

theorem edgeLine_comm (x y : V) : edgeLine x y = edgeLine y x := by
  simp only [edgeLine, Set.pair_comm]

theorem affine_eq_zero_on_edgeLine
    (g : V →ᵃ[ℝ] ℝ) {x y z : V}
    (hx : g x = 0) (hy : g y = 0)
    (hz : point z ∈ edgeLine x y) :
    g z = 0 := by
  have hle : edgeLine x y ≤ (affineForm g).ker := by
    refine Submodule.span_le.mpr ?_
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · change affineForm g (point x) = 0
      simpa using hx
    · have hw' : w = point y := Set.mem_singleton_iff.mp hw
      subst w
      change affineForm g (point y) = 0
      simpa using hy
  simpa using hle hz

/-- The center point belongs to the actual exposed edge, because its supporting
form vanishes on the whole homogeneous edge line. -/
theorem mem_segment_of_center_in_body
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y z : V}
    (hx : g x = 0) (hy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (hzC : z ∈ C) (hzline : point z ∈ edgeLine x y) :
    z ∈ segment ℝ x y :=
  (hzero z hzC).mp (affine_eq_zero_on_edgeLine g hx hy hzline)

theorem extreme_point_on_segment
    (C : Set V) {x y z : V}
    (hz : z ∈ C.extremePoints ℝ) (hx : x ∈ C) (hy : y ∈ C)
    (hsegment : z ∈ segment ℝ x y) :
    z = x ∨ z = y := by
  rcases (mem_extremePoints_iff_forall_segment.mp hz).2 x hx y hy hsegment with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem support_zero_iff_endpoint
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C)
    (hgx : g x = 0) (hgy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    {z : V} (hz : z ∈ C.extremePoints ℝ) :
    g z = 0 ↔ z = x ∨ z = y := by
  constructor
  · intro hg
    exact extreme_point_on_segment C hz hx hy ((hzero z hz.1).mp hg)
  · rintro (rfl | rfl) <;> assumption


theorem endpoint_of_vertex_center
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y v : V}
    (hx : x ∈ C) (hy : y ∈ C) (hv : v ∈ C.extremePoints ℝ)
    (hgx : g x = 0) (hgy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (J : Submodule ℝ (V × ℝ))
    (hJline : J ≤ edgeLine x y) (hvJ : point v ∈ J) :
    v = x ∨ v = y := by
  exact (support_zero_iff_endpoint C g hx hy hgx hgy hzero hv).mp
    (affine_eq_zero_on_edgeLine g hgx hgy (hJline hvJ))

theorem endpoints_eq_of_shared_nonvertex
    (C : Set V) {x y u v z : V}
    (hx : x ∈ C.extremePoints ℝ) (hy : y ∈ C.extremePoints ℝ)
    (hu : u ∈ C.extremePoints ℝ) (hv : v ∈ C.extremePoints ℝ)
    (hxy : x ≠ y)
    (huv : IsExtreme ℝ C (segment ℝ u v))
    (hzxy : z ∈ segment ℝ x y) (hzuv : z ∈ segment ℝ u v)
    (hz : z ∉ C.extremePoints ℝ) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hxz : x ≠ z := by
    intro h
    apply hz
    simpa [← h] using hx
  have hyz : y ≠ z := by
    intro h
    apply hz
    simpa [← h] using hy
  have hzopen : z ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right hxz hyz hzxy
  have hxuv : x ∈ segment ℝ u v :=
    huv.left_mem_of_mem_openSegment hx.1 hy.1 hzuv hzopen
  have hyuv : y ∈ segment ℝ u v :=
    huv.right_mem_of_mem_openSegment hx.1 hy.1 hzuv hzopen
  have hxend := extreme_point_on_segment C hx hu.1 hv.1 hxuv
  have hyend := extreme_point_on_segment C hy hu.1 hv.1 hyuv
  rcases hxend with hxu | hxv <;> rcases hyend with hyu | hyv
  · exact (hxy (hxu.trans hyu.symm)).elim
  · exact Or.inl ⟨hxu, hyv⟩
  · exact Or.inr ⟨hxv, hyu⟩
  · exact (hxy (hxv.trans hyv.symm)).elim

/-- A family of actual edges containing one point is either a star at an
extreme point or consists of one unordered edge. -/
theorem star_or_single_edge_of_common_point
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (z : V) (hz : ∀ i, z ∈ segment ℝ (left i) (right i)) :
    (z ∈ C.extremePoints ℝ ∧ ∀ i, z = left i ∨ z = right i) ∨
      (∀ i j, (left i = left j ∧ right i = right j) ∨
        (left i = right j ∧ right i = left j)) := by
  by_cases hzext : z ∈ C.extremePoints ℝ
  · exact Or.inl ⟨hzext, fun i =>
      extreme_point_on_segment C hzext (hl i).1 (hr i).1 (hz i)⟩
  · exact Or.inr (fun i j =>
      endpoints_eq_of_shared_nonvertex C (hl i) (hr i) (hl j) (hr j)
        (hne i) (hextreme j) (hz i) (hz j) hzext)

def CenterMeets (C : Set V) (J : Submodule ℝ (V × ℝ)) : Prop :=
  ∃ z ∈ C, point z ∈ J

/-- The inside-center classification for exposed edge lines. -/
theorem star_or_single_edge_of_center_meets
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hmeet : CenterMeets C J) :
    (∃ z ∈ C.extremePoints ℝ, point z ∈ J ∧
      ∀ i, z = left i ∨ z = right i) ∨
      (∀ i j, (left i = left j ∧ right i = right j) ∨
        (left i = right j ∧ right i = left j)) := by
  obtain ⟨z, hzC, hzJ⟩ := hmeet
  have hz (i : I) : z ∈ segment ℝ (left i) (right i) :=
    mem_segment_of_center_in_body C (support i) (hsleft i) (hsright i)
      (hszero i) hzC (hline i hzJ)
  rcases star_or_single_edge_of_common_point C left right hl hr hne hextreme z hz with
    ⟨hzext, hstar⟩ | hsingle
  · exact Or.inl ⟨z, hzext, hzJ, hstar⟩
  · exact Or.inr hsingle

/-- A projective center common to two disjoint actual edges is exterior.
This property survives every combinatorial realization of the matching. -/
theorem center_exterior_of_disjoint_edges
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (i j : I)
    (hdisjoint : Disjoint ({left i, right i} : Set V) {left j, right j}) :
    ¬ CenterMeets C J := by
  intro hmeet
  rcases star_or_single_edge_of_center_meets C left right hl hr hne hextreme
    support hsleft hsright hszero J hline hmeet with hstar | hsingle
  · obtain ⟨z, -, -, hz⟩ := hstar
    have hzi : z ∈ ({left i, right i} : Set V) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz i
    have hzj : z ∈ ({left j, right j} : Set V) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz j
    exact Set.disjoint_left.mp hdisjoint hzi hzj
  · have hi : left i ∈ ({left i, right i} : Set V) := by simp
    have hj : left i ∈ ({left j, right j} : Set V) := by
      rcases hsingle i j with h | h <;> simp [h.1]
    exact Set.disjoint_left.mp hdisjoint hi hj


/-- Distinct actual edges can share a projective point in the body only at
an actual vertex. The statement also covers edges with a common endpoint. -/
theorem exterior_center_of_distinct_exposed_edges
    (C : Set V) (hC : Convex ℝ C) {x y u v : V}
    (hx : x ∈ C.extremePoints ℝ) (hy : y ∈ C.extremePoints ℝ)
    (hu : u ∈ C.extremePoints ℝ) (hv : v ∈ C.extremePoints ℝ)
    (hxy : x ≠ y)
    (g h : V →ᵃ[ℝ] ℝ)
    (hgx : g x = 0) (hgy : g y = 0)
    (hhu : h u = 0) (hhv : h v = 0)
    (hgn : ∀ z ∈ C, 0 ≤ h z)
    (hgzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (hhzero : ∀ z ∈ C, h z = 0 ↔ z ∈ segment ℝ u v)
    (hdistinct : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)))
    (J : Submodule ℝ (V × ℝ))
    (hJxy : J ≤ edgeLine x y) (hJuv : J ≤ edgeLine u v)
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J) :
    ¬ CenterMeets C J := by
  rintro ⟨z,hzC,hzJ⟩
  have hzxy : z ∈ segment ℝ x y :=
    mem_segment_of_center_in_body C g hgx hgy hgzero hzC (hJxy hzJ)
  have hzuv : z ∈ segment ℝ u v :=
    mem_segment_of_center_in_body C h hhu hhv hhzero hzC (hJuv hzJ)
  have hznot : z ∉ C.extremePoints ℝ := fun hz => hnotvertex z hz hzJ
  have hex := isExtreme_segment_of_affine_support C hC h hu.1 hv.1 hgn hhzero
  exact hdistinct
    (endpoints_eq_of_shared_nonvertex C hx hy hu hv hxy hex hzxy hzuv hznot)

theorem center_eq_vertex_line (J : Submodule ℝ (V × ℝ))
    (hJ : Module.finrank ℝ J = 1) {z : V} (hz : point z ∈ J) :
    J = Submodule.span ℝ ({point z} : Set (V × ℝ)) :=
  eq_span_singleton_of_mem_of_finrank_eq_one hJ hz (point_ne_zero z)

/-- For canonically oriented crossing edges, the nonvertex alternative really
contains at most one edge index. Opposite endpoints have different colors,
which supplies hcross. -/
theorem crossing_family_subsingleton_of_inside_nonvertex_center
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J)
    (hmeet : CenterMeets C J)
    (hcross : ∀ i j, left i ≠ right j)
    (hinj : Function.Injective fun i => (left i, right i)) :
    Subsingleton I := by
  rcases star_or_single_edge_of_center_meets C left right hl hr hne hextreme
    support hsleft hsright hszero J hline hmeet with hstar | hsingle
  · obtain ⟨z, hz, hzJ, -⟩ := hstar
    exact (hnotvertex z hz hzJ).elim
  · refine ⟨fun i j => ?_⟩
    rcases hsingle i j with h | h
    · exact hinj (Prod.ext h.1 h.2)
    · exact (hcross i j h.1).elim

end Papers.Polytopes.ExposedEdgeCenters


end
end BundlePart4

section BundlePart5
/- Source: Papers/ActualEdgeSupports.lean -/





@[expose] public section

/-!
# Supporting affine forms for actual polytope edges

The face and extreme-point inputs used by the projective edge lemmas are
constructed here from the ordinary ConvexPolytope and GeneralVertexStep
definitions. No exposing-form or vertex-extremality certificate is assumed.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem actualStep_symm {P : ConvexPolytope d} {x y : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep P y x := by
  obtain ⟨hy,hne,F,hF,hdim,hxF,hyF⟩ := hxy
  exact ⟨hx,hne.symm,F,hF,hdim,hyF,hxF⟩

theorem vertex_mem_body_extremePoints (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) :
    x ∈ P.toSet.extremePoints ℝ := by
  change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hx

theorem vertex_mem_body_of_mem_vertices (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) : x ∈ P.toSet :=
  subset_convexHull ℝ _ hx

theorem actual_edge_eq_segment_of_endpoints
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 1)
    {x y : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxy : x ≠ y) (hxF : x ∈ F) (hyF : y ∈ F) :
    F = segment ℝ x y := by
  obtain ⟨z,hz,hzF,hzx,hseg⟩ := spigolo_segmento P hF hdim hx hxF
  have hyseg : y ∈ segment ℝ x z := by simpa only [← hseg] using hyF
  have hends := ExposedEdgeCenters.extreme_point_on_segment P.toSet
    (vertex_mem_body_extremePoints P hy)
    (vertex_mem_body_of_mem_vertices P hx) (vertex_mem_body_of_mem_vertices P hz) hyseg
  rcases hends with hyx | hyz
  · exact (hxy hyx.symm).elim
  · simpa only [hyz] using hseg

theorem segment_isFace_of_generalVertexStep
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    P.IsFace (segment ℝ x y) := by
  obtain ⟨F,hF,hdim,hxF,hyF⟩ := hxy.2.2
  have hseg := actual_edge_eq_segment_of_endpoints P F hF hdim
    hx hxy.1 hxy.2.1 hxF hyF
  simpa only [hseg] using hF

theorem segment_faceDim_of_generalVertexStep
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    faceDim (segment ℝ x y) = 1 := by
  obtain ⟨F,hF,hdim,hxF,hyF⟩ := hxy.2.2
  have hseg := actual_edge_eq_segment_of_endpoints P F hF hdim
    hx hxy.1 hxy.2.1 hxF hyF
  simpa only [hseg] using hdim

/-- Every actual nonempty face has a nonnegative affine exposing form. -/
theorem exists_nonnegative_affine_face_form
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F) :
    ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ z ∈ P.toSet, 0 ≤ g z) ∧
      (∀ z ∈ P.toSet, g z = 0 ↔ z ∈ F) := by
  obtain ⟨x,hxF⟩ := hF.2
  obtain ⟨l,hl⟩ := hF.1 hF.2
  have hx' := hxF
  rw [hl] at hx'
  let g : E d →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (E d) (l x) - l.toLinearMap.toAffineMap
  have hg (z : E d) : g z = l x - l z := rfl
  refine ⟨g,?_,?_⟩
  · intro z hz
    rw [hg]
    exact sub_nonneg.mpr (hx'.2 z hz)
  · intro z hz
    rw [hg,sub_eq_zero]
    constructor
    · intro heq
      rw [hl]
      refine ⟨hz,?_⟩
      intro w hw
      exact (hx'.2 w hw).trans_eq heq
    · intro hzF
      rw [hl] at hzF
      exact le_antisymm (hzF.2 x hx'.1) (hx'.2 z hz)

/-- Actual edges supply precisely the forms required by the center geometry. -/
theorem exists_nonnegative_affine_edge_form
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ z ∈ P.toSet, 0 ≤ g z) ∧
      (∀ z ∈ P.toSet, g z = 0 ↔ z ∈ segment ℝ x y) :=
  exists_nonnegative_affine_face_form P (segment ℝ x y)
    (segment_isFace_of_generalVertexStep P hx hxy)

end Papers.Polytopes


end
end
end BundlePart5

section BundlePart6
/- Source: Papers/ActualFaceFiniteness.lean -/



@[expose] public section

/-! The finite type of genuine nonempty exposed faces, using facce_finite. -/

noncomputable section
namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ}

def ActualFaceType (P : ConvexPolytope d) :=
  {F : Set (E d) // P.IsFace F}

noncomputable instance actualFaceTypeFintype (P : ConvexPolytope d) :
    Fintype (ActualFaceType P) :=
  (facce_finite P).fintype

end Papers.Polytopes


end
end
end BundlePart6

section BundlePart7
/- Source: Papers/ActualNeighborBound.lean -/




@[expose] public section

/-! Actual graph degree is at least intrinsic dimension, from tangent span. -/

namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

/-- The degree bound derived from the full actual tangent-direction span. -/
theorem actual_neighbor_card_ge_dim
    (P : ConvexPolytope d) {v : E d} (hv : v ∈ P.vertices) :
    P.dim ≤ (Papers.PolytopeVertexCone.actualNeighbors P v).card := by
  classical
  have h := finrank_range_le_card (R := ℝ)
    (fun w : Papers.PolytopeVertexCone.actualNeighbors P v => w.val - v)
  have hbound : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun w : Papers.PolytopeVertexCone.actualNeighbors P v => w.val - v))) ≤
        (Papers.PolytopeVertexCone.actualNeighbors P v).card := by
    simpa only [Set.finrank,Fintype.card_coe] using h
  rw [← Papers.PolytopeVertexCone.neighborSpan_eq_range_span,
    Papers.PolytopeVertexCone.neighborSpan_eq_vectorSpan P hv] at hbound
  exact hbound


end Papers.Polytopes


end
end BundlePart7

section BundlePart8
/- Source: Papers/IncidentTwoFacesCount.lean -/
@[expose] public section




/-!
# Counting two-faces incident to an actual edge

The generic counting lemma below consumes an actual vertex-figure neighbor
embedding.  Constructing that embedding from the checked vertex-slice face
correspondence is a separate geometric step; this file does not substitute the
existence of such an embedding for the desired unconditional theorem.
-/

namespace Papers.Polytopes

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

/-- Actual nonempty two-faces containing both endpoints of an edge. -/
noncomputable def incidentTwoFaces (P : ConvexPolytope d) (x y : E d) :
    Finset (ActualFaceType P) := by
  classical
  exact Finset.univ.filter fun F => faceDim F.val = 2 ∧ x ∈ F.val ∧ y ∈ F.val

/-- The dimension bound follows from the usual degree bound in the vertex
figure and an injection of actual neighboring vertices into incident two-faces. -/
theorem incidentTwoFaces_card_from_vertexFigure
    (P : ConvexPolytope d) (x y : E d)
    (Q : ConvexPolytope e) (q : E e) (hq : q ∈ Q.vertices)
    (hdim : Q.dim + 1 = P.dim)
    (lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y)
    (hlift : Function.Injective lift) :
    P.dim ≤ (incidentTwoFaces P x y).card + 1 := by
  classical
  have hdegree := actual_neighbor_card_ge_dim Q hq
  have hcard : (Papers.PolytopeVertexCone.actualNeighbors Q q).card ≤ (incidentTwoFaces P x y).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift hlift
  omega

theorem incidentTwoFaces_card_from_vertexFigure_fullDim
    (P : ConvexPolytope d) (hP : P.IsFullDim) (x y : E d)
    (Q : ConvexPolytope e) (q : E e) (hq : q ∈ Q.vertices)
    (hdim : Q.dim + 1 = P.dim)
    (lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y)
    (hlift : Function.Injective lift) :
    d - 1 ≤ (incidentTwoFaces P x y).card := by
  have h := incidentTwoFaces_card_from_vertexFigure P x y Q q hq hdim lift hlift
  change P.dim = d at hP
  omega

end Papers.Polytopes


end
end BundlePart8

section BundlePart9
/- Source: Papers/IncidentTwoFacesActual.lean -/






@[expose] public section

/-!
# The actual incident two-face lower bound

A genuine vertex figure is constructed by vertexFigure_galois_exists.
The chosen edge becomes a vertex of that figure. Every neighboring vertex
of the figure lifts to a distinct actual two-face containing the original
edge. Thus the ordinary vertex-degree bound supplies the required count.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- A zero-dimensional actual face is the singleton of an actual vertex. -/
theorem actual_zeroFace_is_vertex
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 0) :
    ∃ x ∈ P.vertices, F = {x} := by
  obtain ⟨x,hFx⟩ := faccia_dim0_singoletto hF.2 hdim
  have hxext : x ∈ P.toSet.extremePoints ℝ := by
    have hs : IsExposed ℝ P.toSet ({x} : Set (E d)) := by
      simpa only [hFx] using hF.1
    exact hs.isExtreme.mem_extremePoints
  have hxV : x ∈ P.vertices := by
    change x ∈ (P.vertices : Set (E d))
    rw [P.vertices_eq_extremePoints]
    exact hxext
  exact ⟨x,hxV,hFx⟩

theorem incidentTwoFaces_card_actual
    (P : ConvexPolytope d) {x y : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    P.dim ≤ (incidentTwoFaces P x y).card + 1 := by
  have he : P.IsFace (segment ℝ x y) :=
    segment_isFace_of_generalVertexStep P hx hxy
  have hedim : faceDim (segment ℝ x y) = 1 :=
    segment_faceDim_of_generalVertexStep P hx hxy
  have hxT : x ∈ P.toSet := vertex_mem_body_of_mem_vertices P hx
  have hPpos : 1 ≤ faceDim P.toSet := by
    have hle := Submodule.finrank_mono
      (vectorSpan_mono ℝ (face_subset_toSet P he))
    change faceDim (segment ℝ x y) ≤ faceDim P.toSet at hle
    rwa [hedim] at hle
  have hxFacePolytope : x ∈ (facePolytope P (toSet_isFace P)).vertices := by
    change x ∈ P.vertices.filter (· ∈ P.toSet)
    exact Finset.mem_filter.mpr ⟨hx,hxT⟩
  obtain ⟨D⟩ := vertexFigure_galois_exists P P.toSet (toSet_isFace P)
    x hxFacePolytope hPpos
  let Q := D.figure
  let edge : PositiveVertexStarFace P P.toSet x :=
    { carrier := segment ℝ x y
      isFace := he
      subset_base := face_subset_toSet P he
      mem_vertex := left_mem_segment ℝ _ _
      dim_pos := by rw [hedim] }
  have himage_dim : faceDim (D.faceEquiv edge).carrier = 0 := by
    have h := D.map_dim edge
    change faceDim (D.faceEquiv edge).carrier + 1 =
      faceDim (segment ℝ x y) at h
    rw [hedim] at h
    omega
  obtain ⟨q,hq,himage⟩ := actual_zeroFace_is_vertex Q
    (D.faceEquiv edge).carrier (D.faceEquiv edge).isFace himage_dim
  have hQdim : Q.dim + 1 = P.dim :=
    D.figure_dim_add_one (toSet_isFace P) hxT hPpos
  have hzStep (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : GeneralVertexStep Q q z.val := by
    exact (Finset.mem_filter.mp z.property).2
  let liftFace (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : PositiveVertexStarFace P P.toSet x :=
    D.faceEquiv.symm
      { carrier := segment ℝ q z.val
        isFace := segment_isFace_of_generalVertexStep Q hq (hzStep z) }
  have lift_image (z : Papers.PolytopeVertexCone.actualNeighbors Q q) :
      (D.faceEquiv (liftFace z)).carrier = segment ℝ q z.val := by
    simp only [liftFace,D.faceEquiv.apply_symm_apply]
  have lift_dim (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : faceDim (liftFace z).carrier = 2 := by
    have h := D.map_dim (liftFace z)
    rw [lift_image,segment_faceDim_of_generalVertexStep Q hq (hzStep z)] at h
    omega
  have edge_subset_lift (z : Papers.PolytopeVertexCone.actualNeighbors Q q) :
      edge.carrier ⊆ (liftFace z).carrier := by
    apply (D.map_subset_iff edge (liftFace z)).mpr
    rw [himage,lift_image]
    exact Set.singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
  let lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y := fun z =>
    ⟨⟨(liftFace z).carrier,(liftFace z).isFace⟩,by
      change (⟨(liftFace z).carrier,(liftFace z).isFace⟩ : ActualFaceType P) ∈
        Finset.univ.filter (fun F : ActualFaceType P =>
          faceDim F.val = 2 ∧ x ∈ F.val ∧ y ∈ F.val)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lift_dim z,(liftFace z).mem_vertex,
        edge_subset_lift z (right_mem_segment ℝ _ _)⟩⟩
  have hlift : Function.Injective lift := by
    intro z w hzw
    have hcar : (liftFace z).carrier = (liftFace w).carrier :=
      congrArg (fun F : incidentTwoFaces P x y => F.val.val) hzw
    have hstar : liftFace z = liftFace w := PositiveVertexStarFace.ext hcar
    have hsegments : segment ℝ q z.val = segment ℝ q w.val := by
      have hh := congrArg (fun F : PositiveVertexStarFace P P.toSet x =>
        (D.faceEquiv F).carrier) hstar
      simpa only [lift_image] using hh
    have hwseg : w.val ∈ segment ℝ q z.val := by
      rw [hsegments]
      exact right_mem_segment ℝ _ _
    have hends := ExposedEdgeCenters.extreme_point_on_segment Q.toSet
      (vertex_mem_body_extremePoints Q (hzStep w).1)
      (vertex_mem_body_of_mem_vertices Q hq)
      (vertex_mem_body_of_mem_vertices Q (hzStep z).1) hwseg
    rcases hends with hwq | hwz
    · exact ((hzStep w).2.1 hwq.symm).elim
    · exact Subtype.ext hwz.symm
  exact incidentTwoFaces_card_from_vertexFigure P x y Q q hq hQdim lift hlift

theorem incidentTwoFaces_card_actual_fullDim
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    {x y : E d} (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    d - 1 ≤ (incidentTwoFaces P x y).card := by
  have h := incidentTwoFaces_card_actual P hx hxy
  change P.dim = d at hP
  omega

end Papers.Polytopes


end
end
end BundlePart9

section BundlePart10
/- Source: Papers/ActualVertexFigureGraph.lean -/



@[expose] public section

/-!
# Vertices and edges of a genuine vertex figure

The figure is the actual polytope supplied by the proved Galois construction.
Its vertices are in bijection with actual neighbors of the base vertex.
Its edges correspond precisely to actual two-faces through that vertex.
-/

noncomputable section
namespace Papers.Polytopes.ActualVertexFigure

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem exists_figure (P : ConvexPolytope d) {x : E d}
    (hx : x ∈ P.vertices) (hpos : 1 ≤ P.dim) :
    Nonempty (VertexFigureGaloisData P P.toSet x) := by
  have hxT := vertex_mem_body_of_mem_vertices P hx
  have hxF : x ∈ (facePolytope P (toSet_isFace P)).vertices := by
    change x ∈ P.vertices.filter (· ∈ P.toSet)
    exact Finset.mem_filter.mpr ⟨hx,hxT⟩
  exact vertexFigure_galois_exists P P.toSet (toSet_isFace P) x hxF hpos

theorem neighbor_step (P : ConvexPolytope d) (x : E d)
    (y : Papers.PolytopeVertexCone.actualNeighbors P x) : GeneralVertexStep P x y.val :=
  (Finset.mem_filter.mp y.property).2

def neighborVertex (P : ConvexPolytope d) (x : E d)
    (y : Papers.PolytopeVertexCone.actualNeighbors P x) : P.vertices :=
  ⟨y.val,(neighbor_step P x y).1⟩

def asNeighbor (P : ConvexPolytope d) {x : E d} (y : P.vertices)
    (hxy : GeneralVertexStep P x y.val) : Papers.PolytopeVertexCone.actualNeighbors P x :=
  ⟨y.val,Finset.mem_filter.mpr ⟨y.property,hxy⟩⟩

theorem neighborVertex_asNeighbor (P : ConvexPolytope d) {x : E d}
    (y : P.vertices) (hxy : GeneralVertexStep P x y.val) :
    neighborVertex P x (asNeighbor P y hxy) = y := rfl

def neighborStarFace (P : ConvexPolytope d) {x : E d}
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    PositiveVertexStarFace P P.toSet x where
  carrier := segment ℝ x y.val
  isFace := segment_isFace_of_generalVertexStep P hx (neighbor_step P x y)
  subset_base := face_subset_toSet P
    (segment_isFace_of_generalVertexStep P hx (neighbor_step P x y))
  mem_vertex := left_mem_segment ℝ _ _
  dim_pos := by
    rw [segment_faceDim_of_generalVertexStep P hx (neighbor_step P x y)]

variable {P : ConvexPolytope d} {x : E d}

theorem neighbor_image_exists (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    ∃ q ∈ D.figure.vertices, (D.faceEquiv (neighborStarFace P hx y)).carrier = {q} := by
  apply actual_zeroFace_is_vertex D.figure _ (D.faceEquiv (neighborStarFace P hx y)).isFace
  have h := D.map_dim (neighborStarFace P hx y)
  change faceDim (D.faceEquiv (neighborStarFace P hx y)).carrier + 1 =
    faceDim (segment ℝ x y.val) at h
  rw [segment_faceDim_of_generalVertexStep P hx (neighbor_step P x y)] at h
  omega

def neighborImage (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) : D.figure.vertices :=
  ⟨Classical.choose (neighbor_image_exists D hx y),
    (Classical.choose_spec (neighbor_image_exists D hx y)).1⟩

theorem neighborImage_face (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    (D.faceEquiv (neighborStarFace P hx y)).carrier = {(neighborImage D hx y).val} :=
  (Classical.choose_spec (neighbor_image_exists D hx y)).2

theorem neighborImage_injective (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Function.Injective (neighborImage D hx) := by
  intro y z hyz
  have himages : D.faceEquiv (neighborStarFace P hx y) =
      D.faceEquiv (neighborStarFace P hx z) := by
    apply PolytopeFace.ext
    rw [neighborImage_face,neighborImage_face,hyz]
  have hstars := D.faceEquiv.injective himages
  have hsegments : segment ℝ x y.val = segment ℝ x z.val :=
    congrArg PositiveVertexStarFace.carrier hstars
  have hzseg : z.val ∈ segment ℝ x y.val := by
    rw [hsegments]
    exact right_mem_segment ℝ _ _
  have hends := ExposedEdgeCenters.extreme_point_on_segment P.toSet
    (vertex_mem_body_extremePoints P (neighbor_step P x z).1)
    (vertex_mem_body_of_mem_vertices P hx)
    (vertex_mem_body_of_mem_vertices P (neighbor_step P x y).1) hzseg
  rcases hends with hzx | hzy
  · exact ((neighbor_step P x z).2.1 hzx.symm).elim
  · exact Subtype.ext hzy.symm

theorem neighborImage_surjective (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Function.Surjective (neighborImage D hx) := by
  intro q
  let S : PositiveVertexStarFace P P.toSet x :=
    D.faceEquiv.symm
      { carrier := {q.val}
        isFace := vertex_isFace D.figure q.property }
  have himage : (D.faceEquiv S).carrier = {q.val} := by
    simp only [S,D.faceEquiv.apply_symm_apply]
  have hdim : faceDim S.carrier = 1 := by
    have h := D.map_dim S
    rw [himage,faceDim_singleton] at h
    omega
  obtain ⟨y,hy,hyS,hyx,hseg⟩ := spigolo_segmento P S.isFace hdim hx S.mem_vertex
  have hxy : GeneralVertexStep P x y :=
    ⟨hy,hyx.symm,S.carrier,S.isFace,hdim,S.mem_vertex,hyS⟩
  let y' : Papers.PolytopeVertexCone.actualNeighbors P x :=
    ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩⟩
  refine ⟨y',?_⟩
  have hstar : neighborStarFace P hx y' = S := by
    apply PositiveVertexStarFace.ext
    exact hseg.symm
  have hsingle : {(neighborImage D hx y').val} = ({q.val} : Set (E d)) := by
    calc
      {(neighborImage D hx y').val} =
          (D.faceEquiv (neighborStarFace P hx y')).carrier :=
        (neighborImage_face D hx y').symm
      _ = (D.faceEquiv S).carrier := by rw [hstar]
      _ = {q.val} := himage
  exact Subtype.ext (Set.singleton_injective hsingle)

def neighborEquiv (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Papers.PolytopeVertexCone.actualNeighbors P x ≃ D.figure.vertices :=
  Equiv.ofBijective (neighborImage D hx)
    ⟨neighborImage_injective D hx,neighborImage_surjective D hx⟩

theorem figure_edge_iff_twoFace (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y z : Papers.PolytopeVertexCone.actualNeighbors P x) (hyz : y ≠ z) :
    GeneralVertexStep D.figure (neighborImage D hx y).val (neighborImage D hx z).val ↔
      ∃ F : Set (E d), P.IsFace F ∧ faceDim F = 2 ∧
        x ∈ F ∧ y.val ∈ F ∧ z.val ∈ F := by
  constructor
  · intro hstep
    obtain ⟨A,hA,hAdim,hyA,hzA⟩ := hstep.2.2
    let S : PositiveVertexStarFace P P.toSet x :=
      D.faceEquiv.symm { carrier := A, isFace := hA }
    have himage : (D.faceEquiv S).carrier = A := by
      simp only [S,D.faceEquiv.apply_symm_apply]
    have hdim : faceDim S.carrier = 2 := by
      have h := D.map_dim S
      rw [himage,hAdim] at h
      omega
    have hyS : (neighborStarFace P hx y).carrier ⊆ S.carrier := by
      apply (D.map_subset_iff _ _).mpr
      rw [neighborImage_face,himage]
      exact Set.singleton_subset_iff.mpr hyA
    have hzS : (neighborStarFace P hx z).carrier ⊆ S.carrier := by
      apply (D.map_subset_iff _ _).mpr
      rw [neighborImage_face,himage]
      exact Set.singleton_subset_iff.mpr hzA
    exact ⟨S.carrier,S.isFace,hdim,S.mem_vertex,
      hyS (right_mem_segment ℝ _ _),hzS (right_mem_segment ℝ _ _)⟩
  · rintro ⟨F,hF,hdim,hxF,hyF,hzF⟩
    let S : PositiveVertexStarFace P P.toSet x :=
      { carrier := F
        isFace := hF
        subset_base := face_subset_toSet P hF
        mem_vertex := hxF
        dim_pos := by omega }
    have hFconv : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
    have hyS : (neighborStarFace P hx y).carrier ⊆ S.carrier :=
      hFconv.segment_subset hxF hyF
    have hzS : (neighborStarFace P hx z).carrier ⊆ S.carrier :=
      hFconv.segment_subset hxF hzF
    have hiy : (neighborImage D hx y).val ∈ (D.faceEquiv S).carrier := by
      apply (D.map_subset_iff _ _).mp hyS
      rw [neighborImage_face]
      exact Set.mem_singleton _
    have hiz : (neighborImage D hx z).val ∈ (D.faceEquiv S).carrier := by
      apply (D.map_subset_iff _ _).mp hzS
      rw [neighborImage_face]
      exact Set.mem_singleton _
    have hidim : faceDim (D.faceEquiv S).carrier = 1 := by
      have h := D.map_dim S
      change faceDim (D.faceEquiv S).carrier + 1 = faceDim F at h
      rw [hdim] at h
      omega
    refine ⟨(neighborImage D hx z).property,?_,(D.faceEquiv S).carrier,
      (D.faceEquiv S).isFace,hidim,hiy,hiz⟩
    intro h
    exact hyz (neighborImage_injective D hx (Subtype.ext h))

end Papers.Polytopes.ActualVertexFigure


end
end
end BundlePart10
