module
public import Cubical.Polytope.SottoPolitopo
public import Cubical.Polytope.DueVertici
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Cubical.Polytope.ConnettivitaGlobale
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Real.Sqrt
public import Cubical.Polytope.FacciaArgmax
public import Cubical.Polytope.BalinskiGenerale
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Lean.Elab.Tactic.Omega
public import Papers.PolytopeIncidenceCounting
public import Papers.PolytopeEulerFour

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Cubical/Polytope/Faces.lean -/



@[expose] public section

/-!
# Finite face sets of genuine convex polytopes

These results concern exposed geometric faces of a convex hull.  No
combinatorial incidence or face-count property is assumed in the definitions.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- A finite convex polytope has only finitely many nonempty faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by
  classical
  apply (P.vertices.powerset.finite_toSet.image
    (fun s : Finset (E n) => convexHull ℝ (s : Set (E n)))).subset
  intro F hF
  refine ⟨P.vertices.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · exact (face_eq_hull_vertices P hF).symm

/-- Geometric faces are determined by the vertices they contain. -/
theorem face_eq_iff_vertices_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G) :
    F = G ↔ (∀ v ∈ P.vertices, v ∈ F ↔ v ∈ G) := by
  classical
  constructor
  · intro h v hv
    rw [h]
  · intro h
    rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
    congr 2
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvF⟩
      exact ⟨hv, (h v hv).mp hvF⟩
    · rintro ⟨hv, hvG⟩
      exact ⟨hv, (h v hv).mpr hvG⟩

/-- Nonempty intersections of faces are common faces, geometrically. -/
theorem isFace_inter (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hne : (F ∩ G).Nonempty) : P.IsFace (F ∩ G) :=
  ⟨hF.1.inter hG.1, hne⟩

/-- All nonempty faces, represented as geometric subsets. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset

@[simp] theorem mem_faceSet (P : ConvexPolytope n) (F : Set (E n)) :
    F ∈ faceSet P ↔ P.IsFace F := by
  classical
  simp [faceSet]

/-- The number of geometric faces of affine dimension `i`. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart0

section BundlePart1
/- Source: Cubical/Polytope/Graph.lean -/





@[expose] public section

/-!
# The actual edge graph of a finite convex polytope

Vertices are precisely the extreme points listed by the geometric polytope.
Two distinct vertices are adjacent when they lie on a common exposed face
of affine dimension one.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The nonempty geometric face poset, ordered by inclusion. -/
abbrev FaceType (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

noncomputable instance faceTypeFintype (P : ConvexPolytope n) :
    Fintype (FaceType P) := (finite_isFace P).fintype

/-- Vertices of a geometric convex polytope. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}

/-- The ordinary graph of vertices and edges of a convex polytope. -/
def polytopeGraph (P : ConvexPolytope n) : SimpleGraph (VertexType P) where
  Adj u v := u ≠ v ∧ ∃ F : Set (E n),
    P.IsFace F ∧ faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F
  symm := by
    constructor
    rintro u v ⟨hne, F, hF, hdF, hu, hv⟩
    exact ⟨hne.symm, F, hF, hdF, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Counting zero-dimensional faces agrees with counting extreme vertices. -/
theorem faceNumber_zero (P : ConvexPolytope n) :
    faceNumber P 0 = P.vertices.card := by
  classical
  have hfaces : (faceSet P).filter (fun F => faceDim F = 0) =
      P.vertices.image (fun v : E n => ({v} : Set (E n))) := by
    ext F
    simp only [Finset.mem_filter, mem_faceSet, Finset.mem_image]
    constructor
    · rintro ⟨hF, hd⟩
      obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hd
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vertex_isFace P hv, faceDim_singleton v⟩
  unfold faceNumber
  rw [hfaces]
  exact Finset.card_image_of_injective _ (fun _ _ h => Set.singleton_injective h)

/-- An exposed edge is the segment joining any two distinct vertices on it. -/
theorem edge_eq_segment (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (hne : u ≠ v) :
    F = segment ℝ u v := by
  obtain ⟨w, hw, hwF, hwu, hseg⟩ := spigolo_segmento P hF hdF hu huF
  have hvend : v = u ∨ v = w :=
    vertice_in_segmento_estremo_generico P hF hseg hv hvF
  rcases hvend with hvu | hvw
  · exact (hne hvu.symm).elim
  · simpa only [← hvw] using hseg

/-- The geometric edge containing two distinct vertices is unique. -/
theorem edge_unique (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 1) (hdG : faceDim G = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (huG : u ∈ G) (hvG : v ∈ G)
    (hne : u ≠ v) : F = G := by
  rw [edge_eq_segment P hF hdF hu hv huF hvF hne,
    edge_eq_segment P hG hdG hu hv huG hvG hne]

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart1

section BundlePart2
/- Source: Cubical/Polytope/FaceOrder.lean -/





@[expose] public section

/-!
# Combinatorial equivalences preserve geometric face dimension

An order isomorphism of nonempty geometric face posets already preserves
dimension. The proof uses complete flags and strict growth of affine
dimension along a proper inclusion of exposed faces. Thus no separate rank
preservation assumption is needed in the definition of a cubical polytope.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

theorem faceOrderIso_dimension_le (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim F.val ≤ faceDim (φ F).val := by
  classical
  let d := faceDim F.val
  obtain ⟨c, hcd, hcface, hcmono⟩ := chain_ending_at_face P F.property (d := d) rfl
  let C (k : ℕ) : FaceType P :=
    if hk : k ≤ d then ⟨c k, (hcface k hk).1⟩ else F
  have hC (k : ℕ) (hk : k ≤ d) : (C k).val = c k := by
    simp only [C, dif_pos hk]
  have hCd : C d = F := by
    apply Subtype.ext
    exact (hC d le_rfl).trans hcd
  have hstrict : StrictMonoOn (fun k => faceDim (φ (C k)).val) (Iic d) := by
    intro i hi j hj hij
    apply faceDim_lt_of_ssubset Q (φ (C i)).property (φ (C j)).property
    have hCij : C i < C j := by
      change (C i).val ⊂ (C j).val
      rw [hC i hi, hC j hj]
      exact hcmono i j hij hj
    exact φ.strictMono hCij
  have hbound := hstrict.Iic_id_le d le_rfl
  simpa only [hCd, d] using hbound

/-- Combinatorial equivalence of ordinary face posets preserves dimension. -/
theorem faceOrderIso_dimension (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim (φ F).val = faceDim F.val := by
  apply le_antisymm
  · simpa using faceOrderIso_dimension_le φ.symm (φ F)
  · exact faceOrderIso_dimension_le φ F

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart2

section BundlePart3
/- Source: Papers/PolytopeGeometry.lean -/




@[expose] public section

/-!
# Geometric consequences of ordinary combinatorial equivalence

These results do not add rank, incidence, or general-position hypotheses to
the face-order isomorphism.  They extract them from the actual convex bodies.
-/

noncomputable section

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d e : ℕ}

theorem vertex_mem_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet :=
  subset_convexHull ℝ _ hv

theorem vertex_is_extreme (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet.extremePoints ℝ := by
  change v ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hv

theorem vertex_mem_segment_iff (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices) :
    z ∈ segment ℝ x y ↔ z = x ∨ z = y := by
  constructor
  · intro h
    exact ((mem_extremePoints_iff_forall_segment.mp (vertex_is_extreme P hz)).2
      x (vertex_mem_body P hx) y (vertex_mem_body P hy) h).imp Eq.symm Eq.symm
  · rintro (h | h)
    · rw [h]
      exact left_mem_segment ℝ x y
    · rw [h]
      exact right_mem_segment ℝ x y

/-- No three distinct actual vertices are collinear, in any dimension. -/
theorem vertices_not_collinear (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬Collinear ℝ ({x, y, z} : Set (E d)) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases (vertex_mem_segment_iff P hx hz hy).mp h.mem_segment with h | h
    · exact hxy h.symm
    · exact hyz h
  · rcases (vertex_mem_segment_iff P hy hx hz).mp h.mem_segment with h | h
    · exact hyz h.symm
    · exact hxz h.symm
  · rcases (vertex_mem_segment_iff P hz hy hx).mp h.mem_segment with h | h
    · exact hxz h
    · exact hxy h

/-- A face's affine span cannot pick up an additional point of the body. -/
theorem body_inter_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) :
    P.toSet ∩ (affineSpan ℝ F : Set (E d)) = F := by
  obtain ⟨x₀, hx₀⟩ := hF.2
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hx₀' : x₀ ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x₀ := by
    rw [hl] at hx₀
    exact hx₀
  have hconst : Set.EqOn l.toLinearMap.toAffineMap
      (AffineMap.const ℝ (E d) (l x₀)) F := by
    intro y hy
    have hy' : y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y := by
      rw [hl] at hy
      exact hy
    exact le_antisymm (hx₀'.2 y hy'.1) (hy'.2 x₀ hx₀'.1)
  have hspan := AffineMap.eqOn_affineSpan (k := ℝ) hconst
  apply Set.Subset.antisymm
  · rintro y ⟨hyP, hyspan⟩
    rw [hl]
    refine ⟨hyP, fun z hz => ?_⟩
    have hy : l y = l x₀ := hspan hyspan
    rw [hy]
    exact hx₀'.2 z hz
  · intro y hy
    exact ⟨hF.1.subset hy, subset_affineSpan ℝ _ hy⟩

theorem vertex_notMem_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) {v : E d}
    (hv : v ∈ P.vertices) (hvF : v ∉ F) : v ∉ affineSpan ℝ F := by
  intro h
  apply hvF
  rw [← body_inter_affineSpan_face P hF]
  exact ⟨vertex_mem_body P hv, h⟩

def vertexFace (P : ConvexPolytope d) (v : VertexType P) : FaceType P :=
  ⟨{v.val}, vertex_isFace P v.property⟩

@[simp] theorem vertexFace_val (P : ConvexPolytope d) (v : VertexType P) :
    (vertexFace P v).val = {v.val} := rfl

@[simp] theorem vertexFace_dim (P : ConvexPolytope d) (v : VertexType P) :
    faceDim (vertexFace P v).val = 0 := faceDim_singleton v.val

theorem vertexFace_injective (P : ConvexPolytope d) :
    Function.Injective (vertexFace P) := by
  intro v w h
  apply Subtype.ext
  exact Set.singleton_injective (congrArg Subtype.val h)

@[simp] theorem vertexFace_le_iff (P : ConvexPolytope d) (v : VertexType P)
    (F : FaceType P) : vertexFace P v ≤ F ↔ v.val ∈ F.val :=
  Set.singleton_subset_iff

theorem exists_vertex_of_zero_face (P : ConvexPolytope d) (F : FaceType P)
    (hd : faceDim F.val = 0) : ∃ v : VertexType P, vertexFace P v = F := by
  obtain ⟨v, hvF, hv⟩ := punto_di_faccia0_e_vertice P F.property hd
  exact ⟨⟨v, hv⟩, Subtype.ext hvF.symm⟩

/-- The vertex induced by an isomorphism of ordinary nonempty face posets. -/
def imageVertex {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) : VertexType Q :=
  Classical.choose (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_face {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) :
    vertexFace Q (imageVertex φ v) = φ (vertexFace P v) :=
  Classical.choose_spec (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_mem_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) (F : FaceType P) :
    (imageVertex φ v).val ∈ (φ F).val ↔ v.val ∈ F.val := by
  rw [← vertexFace_le_iff, imageVertex_face, φ.le_iff_le, vertexFace_le_iff]

/-- Vertex correspondence is derived from the face-order isomorphism. -/
def vertexEquivOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : VertexType P ≃ VertexType Q where
  toFun := imageVertex φ
  invFun := imageVertex φ.symm
  left_inv v := by
    apply vertexFace_injective P
    rw [imageVertex_face, imageVertex_face, OrderIso.symm_apply_apply]
  right_inv v := by
    apply vertexFace_injective Q
    rw [imageVertex_face, imageVertex_face, OrderIso.apply_symm_apply]

theorem faceOrderIso_vertex_card {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : P.vertices.card = Q.vertices.card := by
  classical
  simpa only [VertexType, Fintype.card_coe] using
    Fintype.card_congr (vertexEquivOfFaceOrder φ)

def wholeFace (P : ConvexPolytope d) : FaceType P :=
  ⟨P.toSet, IsExposed.refl _, by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨v, vertex_mem_body P hv⟩⟩

theorem le_wholeFace (P : ConvexPolytope d) (F : FaceType P) :
    F ≤ wholeFace P := F.property.1.subset

@[simp] theorem image_wholeFace {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : φ (wholeFace P) = wholeFace Q := by
  apply le_antisymm
  · exact le_wholeFace Q _
  · have h := φ.monotone (le_wholeFace P (φ.symm (wholeFace Q)))
    simpa using h

theorem faceOrderIso_polytope_dim {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : Q.dim = P.dim := by
  have h := faceOrderIso_dimension φ (wholeFace P)
  rw [image_wholeFace] at h
  exact h

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/CompleteFaceLattice.lean -/




@[expose] public section

/-!
# Including the empty face

The polytope foundation stores nonempty exposed faces. This file proves that
its notion of combinatorial equivalence is equivalent to an order isomorphism
of the complete exposed-face posets, including the empty face.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def CompleteFaceType {d : ℕ} (P : ConvexPolytope d) :=
  {F : Set (E d) // IsExposed ℝ P.toSet F}

instance {d : ℕ} (P : ConvexPolytope d) : PartialOrder (CompleteFaceType P) :=
  inferInstanceAs (PartialOrder {F : Set (E d) // IsExposed ℝ P.toSet F})

instance {d : ℕ} (P : ConvexPolytope d) : OrderBot (CompleteFaceType P) where
  bot := ⟨∅, isExposed_empty⟩
  bot_le _ := Set.empty_subset _

theorem completeFace_ne_bot_iff {d : ℕ} {P : ConvexPolytope d} (F : CompleteFaceType P) :
    F ≠ ⊥ ↔ F.val.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def nonemptyFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    FaceType P ≃o {F : CompleteFaceType P // F ≠ ⊥} where
  toFun F := ⟨⟨F.val, F.property.1⟩,
    (completeFace_ne_bot_iff _).mpr F.property.2⟩
  invFun F := ⟨F.val.val, F.val.property, (completeFace_ne_bot_iff F.val).mp F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def completeFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    WithBot (FaceType P) ≃o CompleteFaceType P := by
  classical
  exact (nonemptyFaceOrderIso P).withBotCongr.trans WithBot.subtypeOrderIso

def extendFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : CompleteFaceType P ≃o CompleteFaceType Q :=
  (completeFaceOrderIso P).symm.trans (φ.withBotCongr.trans (completeFaceOrderIso Q))

def restrictCompleteFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : CompleteFaceType P ≃o CompleteFaceType Q) : FaceType P ≃o FaceType Q := by
  let ψ : {F : CompleteFaceType P // F ≠ ⊥} ≃o {F : CompleteFaceType Q // F ≠ ⊥} := {
    toFun := fun F => ⟨φ F.val, by
      intro h
      apply F.property
      apply φ.injective
      simpa only [φ.map_bot] using h⟩
    invFun := fun F => ⟨φ.symm F.val, by
      intro h
      apply F.property
      apply φ.symm.injective
      simpa only [φ.symm.map_bot] using h⟩
    left_inv := fun F => Subtype.ext (φ.symm_apply_apply F.val)
    right_inv := fun F => Subtype.ext (φ.apply_symm_apply F.val)
    map_rel_iff' := φ.le_iff_le }
  exact (nonemptyFaceOrderIso P).trans (ψ.trans (nonemptyFaceOrderIso Q).symm)

theorem nonempty_face_iso_iff_complete_face_iso {d e : ℕ}
    (P : ConvexPolytope d) (Q : ConvexPolytope e) :
    Nonempty (FaceType P ≃o FaceType Q) ↔ Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  ⟨fun ⟨φ⟩ => ⟨extendFaceOrderIso φ⟩, fun ⟨φ⟩ => ⟨restrictCompleteFaceOrderIso φ⟩⟩

end Papers.Polytopes

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/PolytopeTargets.lean -/








@[expose] public section

/-!
# Exact geometric targets for the two polytope papers

All objects below are actual finite convex hulls with their extreme vertices.
Faces are exposed faces, and combinatorial equivalence is an order isomorphism
of their ordinary face posets. In particular, neither field realizability nor
Minkowski decomposability is encoded by a conclusion to be proved.

The declarations ending in `Claim` are proposition-valued definitions recording
the original targets. Their presence does NOT assert or prove these claims.
-/

noncomputable section

open Set
open scoped Classical
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- The actual combinatorial equivalence relation on nonempty face posets.
The omitted empty face can be adjoined as a new least element. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Adjoining the empty face gives exactly the ordinary complete face-lattice
notion of combinatorial equivalence. -/
theorem combinatoriallyEquivalent_iff_complete_face_iso (P Q : ConvexPolytope d) :
    CombinatoriallyEquivalent P Q ↔
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  nonempty_face_iso_iff_complete_face_iso P Q

theorem CombinatoriallyEquivalent.refl (P : ConvexPolytope d) :
    CombinatoriallyEquivalent P P := ⟨OrderIso.refl _⟩

theorem CombinatoriallyEquivalent.symm {P Q : ConvexPolytope d}
    (h : CombinatoriallyEquivalent P Q) : CombinatoriallyEquivalent Q P :=
  h.elim (fun e => ⟨e.symm⟩)

theorem CombinatoriallyEquivalent.trans {P Q R : ConvexPolytope d}
    (h₁ : CombinatoriallyEquivalent P Q) (h₂ : CombinatoriallyEquivalent Q R) :
    CombinatoriallyEquivalent P R :=
  h₁.elim (fun e₁ => h₂.elim (fun e₂ => ⟨e₁.trans e₂⟩))

/-- A positive homothety, exactly as in the paper's cited definition.
A point summand is trivial because the other summand is a translate of P. -/
def IsHomotheticCopy (P A : ConvexPolytope d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : E d,
    A.toSet = (fun x : E d => r • x + b) '' P.toSet

/-- Ordinary nontrivial Minkowski decomposability, allowing summands of
any affine dimension in the ambient space. -/
def MinkowskiDecomposable (P : ConvexPolytope d) : Prop :=
  ∃ A B : ConvexPolytope d,
    P.toSet = A.toSet + B.toSet ∧
    ¬IsHomotheticCopy P A ∧ ¬IsHomotheticCopy P B

def ConditionallyDecomposable (P : ConvexPolytope d) : Prop :=
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ MinkowskiDecomposable Q) ∧
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ ¬MinkowskiDecomposable Q)

/-- Theorem 1 of the conditional-decomposability paper, including sharpness
for every dimension, not only a lower bound or a fixed-dimensional case. -/
def ConditionalDecomposabilityClaim : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    (∀ P : ConvexPolytope d, P.IsFullDim → ConditionallyDecomposable P →
      4 * d - 4 ≤ P.vertices.card) ∧
    (∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * d - 4)

def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i

def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

theorem realizableOver_iff_complete_face_iso (P : ConvexPolytope d) (K : Subfield ℝ) :
    RealizableOver P K ↔ ∃ Q : ConvexPolytope d,
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) ∧ CoordinatesIn K Q := by
  constructor
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mp hPQ, hK⟩
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mpr hPQ, hK⟩

def RationallyRealizable (P : ConvexPolytope d) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ RationalCoordinates Q

/-- Density in the space of labeled realizations, expressed without choosing
an enumeration of the vertices. The face-poset isomorphism identifies the
labels, and every vertex must move by less than the prescribed tolerance. -/
def RationallyDense (P : ConvexPolytope d) : Prop :=
  ∀ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ConvexPolytope d, ∃ φ : FaceType Q ≃o FaceType R,
        RationalCoordinates R ∧
        ∀ v : VertexType Q, dist (imageVertex φ v).val v.val < ε

theorem RationallyDense.realizable {P : ConvexPolytope d}
    (h : RationallyDense P) : RationallyRealizable P := by
  obtain ⟨Q, φ, hQ, _⟩ := h P (CombinatoriallyEquivalent.refl P) 1 zero_lt_one
  exact ⟨Q, ⟨φ⟩, hQ⟩

/-- Theorem 1 of the nonrational four-polytope paper. -/
def SeventeenVertexFieldClaim : Prop :=
  ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
    ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K

/-- Theorem 2 of the nonrational four-polytope paper. -/
def RationalityThroughTenClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card ≤ 10 → RationallyRealizable P

/-- Taking a nonempty subset of actual extreme vertices produces the
ordinary convex hull of exactly those vertices. -/
def vertexSubsetPolytope (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) : ConvexPolytope d where
  vertices := S
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxP : x ∈ P.vertices := hsub hx
      have hxext : x ∈ P.toSet.extremePoints ℝ := by
        change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
        rw [← P.vertices_eq_extremePoints]
        exact hxP
      have hhull : convexHull ℝ (S : Set (E d)) ⊆ P.toSet := by
        apply convexHull_mono
        exact hsub
      exact inter_extremePoints_subset_extremePoints_of_subset hhull
        ⟨subset_convexHull ℝ _ hx, hxext⟩
    · exact extremePoints_convexHull_subset

def deleteVertex (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) : ConvexPolytope d :=
  vertexSubsetPolytope P (P.vertices.erase v) hne (Finset.erase_subset _ _)

@[simp] theorem deleteVertex_vertices (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).vertices = P.vertices.erase v := rfl

@[simp] theorem deleteVertex_toSet (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).toSet = convexHull ℝ (P.vertices.erase v : Set (E d)) := rfl

def IsSimpleVertex (P : ConvexPolytope d) (v : VertexType P) : Prop := by
  classical
  exact (polytopeGraph P).degree v = P.dim

/-- The field-equality assertion of Theorem 3. Its additional density and
combinatorial-deletion assertions require separate targets. -/
def SimpleDeletionFieldsClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∀ hne : (P.vertices.erase v.val).Nonempty,
      ∀ K : Subfield ℝ, RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K

/-- The full Theorem 3: deletion preserves dimension, is determined by the
original face lattice and distinguished vertex, preserves every real
realization field, and preserves rational density in both directions. -/
def SimpleDeletionClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ)) ∧
      (∀ K : Subfield ℝ,
        RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K) ∧
      (RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne))

/-- Corollary 4, with the exact simple-vertex hypothesis. -/
def ElevenVertexSimpleClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card = 11 →
    (∃ v : VertexType P, IsSimpleVertex P v) → RationallyRealizable P

end Papers.Polytopes

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/FiniteHullCertificates.lean -/




@[expose] public section

/-!
# Finite supporting-form certificates for actual convex polytopes

A certificate is used only to supply linear inequalities.  The conclusions
about extreme points and exposed faces are derived with Mathlib convexity.
-/

noncomputable section
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d n m : ℕ}

theorem linear_lower_bound_on_hull (s : Finset (E d))
    (l : E d →L[ℝ] ℝ) (c : ℝ) (h : ∀ v ∈ s, c ≤ l v) :
    ∀ x ∈ convexHull ℝ (s : Set (E d)), c ≤ l x := by
  exact convexHull_min h (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c)

/-- A strict linear minimum on the generators is an exposed point of their
ordinary convex hull. -/
theorem strict_minimum_is_exposed (s : Finset (E d)) {v : E d} (hv : v ∈ s)
    (l : E d →L[ℝ] ℝ) (hstrict : ∀ w ∈ s, w ≠ v → l v < l w) :
    IsExposed ℝ (convexHull ℝ (s : Set (E d))) {v} := by
  have hmin : ∀ w ∈ convexHull ℝ (s : Set (E d)), l v ≤ l w := by
    apply linear_lower_bound_on_hull s l (l v)
    intro w hw
    by_cases h : w = v
    · simp [h]
    · exact (hstrict w hw h).le
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ _ hv, fun w hw => by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin w hw⟩
  · rintro ⟨hx, hmax⟩
    have hxv : l x = l v := by
      have h := hmax v (subset_convexHull ℝ _ hv)
      simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
      exact le_antisymm h (hmin x hx)
    have hxHull := PlatoniciL3.faccia_argmax s (-l) hx hmax
    have hsub : {w ∈ (s : Set (E d)) | (-l) w = (-l) x} ⊆ {v} := by
      rintro w ⟨hw, heq⟩
      change w = v
      by_contra hne
      have hlt := hstrict w hw hne
      simp only [ContinuousLinearMap.neg_apply, neg_inj] at heq
      rw [heq, hxv] at hlt
      exact lt_irrefl _ hlt
    exact (convexHull_min hsub (convex_singleton v)) hxHull

def polytopeOfStrictMinima (s : Finset (E d)) (hne : s.Nonempty)
    (hmin : ∀ v ∈ s, ∃ l : E d →L[ℝ] ℝ, ∀ w ∈ s, w ≠ v → l v < l w) :
    ConvexPolytope d where
  vertices := s
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨l, hl⟩ := hmin v hv
      exact (strict_minimum_is_exposed s hv l hl).isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset

/-- Nonnegative forms separating ordered pairs of labels imply that every
label represents an actual extreme vertex. -/
def polytopeOfSeparatingSupports (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    ConvexPolytope d := by
  classical
  let s := Finset.univ.image p
  have hs : s.Nonempty := ⟨p ⟨0, hn⟩, Finset.mem_image.mpr
    ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  apply polytopeOfStrictMinima s hs
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  let selected : Finset (Fin m) := Finset.univ.filter (fun f => l f (p v) = c f)
  refine ⟨∑ f ∈ selected, l f, ?_⟩
  intro y hy hyne
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := by
    intro h
    subst w
    exact hyne rfl
  obtain ⟨f, hfv, hfw⟩ := hsep v w hvw
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_lt_sum
  · intro g hg
    rw [(Finset.mem_filter.mp hg).2]
    exact hl g w
  · exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfv⟩, by simpa [hfv] using hfw⟩

@[simp] theorem polytopeOfSeparatingSupports_vertices
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices = Finset.univ.image p := rfl

theorem separatingSupports_injective (p : Fin n → E d)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    Function.Injective p := by
  intro v w hvw
  by_contra hne
  obtain ⟨f, hfv, hfw⟩ := hsep v w hne
  rw [← hvw, hfv] at hfw
  exact lt_irrefl _ hfw

theorem polytopeOfSeparatingSupports_card
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices.card = n := by
  classical
  rw [polytopeOfSeparatingSupports_vertices,
    Finset.card_image_of_injective _ (separatingSupports_injective p l c hsep)]
  simp

def minimumFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ) : Set (E d) :=
  {x ∈ P.toSet | l x = c}

theorem minimumFace_isFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ v ∈ P.vertices, c ≤ l v)
    (hattained : ∃ v ∈ P.vertices, l v = c) : P.IsFace (minimumFace P l c) := by
  obtain ⟨v, hv, hvc⟩ := hattained
  have hvbody : v ∈ P.toSet := subset_convexHull ℝ _ hv
  have hglobal := linear_lower_bound_on_hull P.vertices l c hbound
  refine ⟨?_, ⟨v, hvbody, hvc⟩⟩
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, fun y hy => ?_⟩
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff]
    rw [hxc]
    exact hglobal y hy
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm ?_ (hglobal x hx)⟩
    have h := hmax v hvbody
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
    simpa [hvc] using h

end Papers.Polytopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/ParallelMaps.lean -/





@[expose] public section

/-!
# Parallel maps on actual polytope edges

The edge relation is the geometric one: two distinct extreme vertices on an
exposed one-dimensional face. The local maximum principle is derived from
the finite face pivot, and all statements below concern this actual graph.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Pointwise RealInnerProductSpace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def IsParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, f y - f x = c • (y - x)

def IsPositiveParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, 0 < c ∧ f y - f x = c • (y - x)

theorem IsPositiveParallelMap.parallel {P : ConvexPolytope d} {f : E d → E d}
    (h : IsPositiveParallelMap P f) : IsParallelMap P f := by
  intro x hx y hy hxy
  obtain ⟨c, _, hc⟩ := h x hx y hy hxy
  exact ⟨c, hc⟩

def IsHomothetyOnVertices (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v ∈ P.vertices, f v = a • v + b

/-- Failure of a global linear maximum gives an actual increasing edge. -/
theorem exists_increasing_edge (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {x z : E d} (hx : x ∈ P.vertices) (hz : z ∈ P.vertices) (hlt : l x < l z) :
    ∃ y : E d, GeneralVertexStep P x y ∧ l x < l y := by
  have hxFace : P.IsFace ({x} : Set (E d)) := vertex_isFace P hx
  obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
  let w : E d := (InnerProductSpace.toDual ℝ (E d)).symm l
  have hw (y : E d) : inner ℝ w y = l y := InnerProductSpace.toDual_symm_apply
  have hconst : ∀ y ∈ ({x} : Set (E d)), inner ℝ w y = inner ℝ w x := by
    rintro y rfl
    rfl
  obtain ⟨F, hF, hproper, himprove⟩ := perno_parametrico_crescente_monotono
    P hxFace g hg x (Set.mem_singleton x) w hconst ⟨z, hz, by simpa only [hw] using hlt⟩
  have hdim : 1 ≤ faceDim F := by
    have h := faceDim_lt_of_ssubset P hxFace hF hproper
    rw [faceDim_singleton] at h
    omega
  obtain ⟨e, he, hde, hxe, heF⟩ := edge_inside_face_at_vertex P hF hx
    (hproper.1 (Set.mem_singleton x)) hdim
  obtain ⟨y, hy, hye, hyx, _⟩ := spigolo_segmento P he hde hx hxe
  refine ⟨y, ⟨hy, hyx.symm, e, he, hde, hxe, hye⟩, ?_⟩
  have hyout : y ∉ ({x} : Set (E d)) := by simpa only [Set.mem_singleton_iff] using hyx
  simpa only [hw] using himprove y (heF hye) hyout

theorem positive_parallel_max_reflect {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l (f y) ≤ l (f x)) :
    ∀ y ∈ P.vertices, l y ≤ l x := by
  intro z hz
  by_contra hnot
  obtain ⟨y, hxy, hlt⟩ := exists_increasing_edge P l hx hz (lt_of_not_ge hnot)
  obtain ⟨c, hc, heq⟩ := hf x hx y hxy.1 hxy
  have h := congrArg l heq
  simp only [map_sub, map_smul, smul_eq_mul] at h
  have hle := hmax y hxy.1
  nlinarith

/-- A parallel map remains constant under a supporting functional along
each face on which that functional is constant. -/
theorem parallel_constant_on_face {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsParallelMap P f) {F : Set (E d)} (hF : P.IsFace F)
    (l : E d →L[ℝ] ℝ) (hconst : ∀ x ∈ F, ∀ y ∈ F, l x = l y)
    {x y : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxF : x ∈ F) (hyF : y ∈ F) : l (f x) = l (f y) := by
  classical
  let Q := facePolytope P hF
  have hxQ : x ∈ Q.vertices := Finset.mem_filter.mpr ⟨hx, hxF⟩
  have hyQ : y ∈ Q.vertices := Finset.mem_filter.mpr ⟨hy, hyF⟩
  have hw := balinski_light_general Q hxQ hyQ
  have hwalk : ∀ z, Relation.ReflTransGen (GeneralVertexStep Q) x z →
      z ∈ Q.vertices ∧ l (f z) = l (f x) := by
    intro z hpath
    induction hpath with
    | refl => exact ⟨hxQ, rfl⟩
    | @tail u v hpath huv ih =>
      have hu := Finset.mem_filter.mp ih.1
      have hv := Finset.mem_filter.mp huv.1
      obtain ⟨_, hne, e, he, hde, hue, hve⟩ := huv
      have hstep : GeneralVertexStep P u v :=
        ⟨hv.1, hne, e, isFace_of_facePolytope P hF he, hde, hue, hve⟩
      obtain ⟨c, hc⟩ := hf u hu.1 v hv.1 hstep
      have h := congrArg l hc
      simp only [map_sub, map_smul, smul_eq_mul, hconst v hv.2 u hu.2,
        sub_self, mul_zero, sub_eq_zero] at h
      exact ⟨Finset.mem_filter.mpr hv, h.trans ih.2⟩
  exact (hwalk y hw).2.symm

theorem positive_parallel_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l y ≤ l x) :
    ∀ y ∈ P.vertices, l (f y) ≤ l (f x) := by
  classical
  obtain ⟨w, hw, hwm⟩ := P.vertices.exists_max_image (fun y => l (f y)) P.vertices_nonempty
  have hwmax := positive_parallel_max_reflect hf l hw hwm
  let F : Set (E d) := {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z}
  have hxF : x ∈ F := ⟨subset_convexHull ℝ _ hx, le_su_toSet P l hmax⟩
  have hwF : w ∈ F := ⟨subset_convexHull ℝ _ hw, le_su_toSet P l hwmax⟩
  have hF : P.IsFace F := ⟨by intro _; exact ⟨l, rfl⟩, ⟨x, hxF⟩⟩
  have hconst : ∀ a ∈ F, ∀ b ∈ F, l a = l b := by
    intro a ha b hb
    exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
  have heq := parallel_constant_on_face hf.parallel hF l hconst hx hw hxF hwF
  intro y hy
  exact (hwm y hy).trans_eq heq.symm

theorem positive_parallel_strict_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hstrict : ∀ y ∈ P.vertices, y ≠ x → l y < l x) :
    ∀ y ∈ P.vertices, y ≠ x → l (f y) < l (f x) := by
  have hmax : ∀ y ∈ P.vertices, l y ≤ l x := by
    intro y hy
    by_cases h : y = x
    · simp [h]
    · exact (hstrict y hy h).le
  have hfm := positive_parallel_max_preserve hf l hx hmax
  intro y hy hyx
  refine lt_of_le_of_ne (hfm y hy) ?_
  intro heq
  have hym : ∀ z ∈ P.vertices, l (f z) ≤ l (f y) := by
    intro z hz
    exact (hfm z hz).trans_eq heq.symm
  have h := positive_parallel_max_reflect hf l hy hym x hx
  exact (not_le_of_gt (hstrict y hy hyx)) h

theorem exists_vertex_exposer (P : ConvexPolytope d) {x : E d} (hx : x ∈ P.vertices) :
    ∃ l : E d →L[ℝ] ℝ, ∀ y ∈ P.vertices, y ≠ x → l y < l x := by
  obtain ⟨l, hl⟩ := (vertex_isFace P hx).1 (Set.singleton_nonempty x)
  have hm : x ∈ {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z} := by
    rw [← hl]
    exact Set.mem_singleton x
  refine ⟨l, ?_⟩
  intro y hy hyx
  have hybody : y ∈ P.toSet := subset_convexHull ℝ _ hy
  refine lt_of_le_of_ne (hm.2 y hybody) ?_
  intro heq
  apply hyx
  have hyface : y ∈ ({x} : Set (E d)) := by
    rw [hl]
    exact ⟨hybody, fun z hz => (hm.2 z hz).trans_eq heq.symm⟩
  exact hyface

def positiveMapPolytope (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) : ConvexPolytope d := by
  classical
  apply polytopeOfStrictMinima (P.vertices.image f) (P.vertices_nonempty.image f)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l, hl⟩ := exists_vertex_exposer P hv
  refine ⟨-l, ?_⟩
  intro y hy hyne
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  have hwv : w ≠ v := by intro h; exact hyne (congrArg f h)
  simpa only [ContinuousLinearMap.neg_apply, neg_lt_neg_iff] using
    positive_parallel_strict_max_preserve hf l hv hl w hw hwv

@[simp] theorem positiveMapPolytope_vertices (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) :
    (positiveMapPolytope P f hf).vertices = P.vertices.image f := rfl

end Papers.Polytopes

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/EdgeSpan.lean -/




@[expose] public section

/-!
# The directions of the edges at one vertex span the polytope

The proof uses the actual edge maximum principle. A functional that is
constant on the neighbors of a vertex is constant on every vertex, hence
on the whole convex hull. Separation of linear subspaces then gives the
span equality, without a full-dimensionality assumption.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem vertex_max_of_edge_max (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {v : E d} (hv : v ∈ P.vertices)
    (hmax : ∀ y, GeneralVertexStep P v y → l y ≤ l v) :
    ∀ z ∈ P.toSet, l z ≤ l v := by
  apply le_su_toSet P l
  intro z hz
  by_contra h
  obtain ⟨y, hstep, hlt⟩ := exists_increasing_edge P l hv hz (lt_of_not_ge h)
  exact (not_lt_of_ge (hmax y hstep)) hlt

theorem linear_constant_of_neighbors (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {v : E d} (hv : v ∈ P.vertices)
    (hconst : ∀ y, GeneralVertexStep P v y → l y = l v) :
    ∀ z ∈ P.toSet, l z = l v := by
  have hu := vertex_max_of_edge_max P l hv (fun y hy => (hconst y hy).le)
  have hl := vertex_max_of_edge_max P (-l) hv (by
    intro y hy
    simp only [ContinuousLinearMap.neg_apply, hconst y hy, le_refl])
  intro z hz
  exact le_antisymm (hu z hz) (by
    simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hl z hz)

theorem vectorSpan_le_ker_of_constant (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    (c : ℝ) (hconst : ∀ z ∈ P.toSet, l z = c) :
    vectorSpan ℝ P.toSet ≤ l.toLinearMap.ker := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hz
  change l (p - q) = 0
  rw [map_sub, hconst p hp, hconst q hq, sub_self]

def edgeStarSpan (P : ConvexPolytope d) (v : E d) : Submodule ℝ (E d) :=
  Submodule.span ℝ {w | ∃ y, GeneralVertexStep P v y ∧ w = y - v}

theorem edgeStarSpan_eq_vectorSpan (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : edgeStarSpan P v = vectorSpan ℝ P.toSet := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨y, hy, rfl⟩
    exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ hy.1)
      (subset_convexHull ℝ _ hv)
  · intro z hz
    by_contra hnot
    obtain ⟨g, hgz, hgW⟩ := Submodule.exists_le_ker_of_notMem hnot
    let l : E d →L[ℝ] ℝ := g.toContinuousLinearMap
    have hneighbors : ∀ y, GeneralVertexStep P v y → l y = l v := by
      intro y hy
      have hmem : y - v ∈ edgeStarSpan P v :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have hzero : g (y - v) = 0 := hgW hmem
      change g y = g v
      simpa only [map_sub, sub_eq_zero] using hzero
    have hbody := linear_constant_of_neighbors P l hv hneighbors
    have hzero : l z = 0 := vectorSpan_le_ker_of_constant P l (l v) hbody hz
    exact hgz hzero

theorem fullDim_edgeStarSpan (P : ConvexPolytope d) (hP : P.IsFullDim)
    {v : E d} (hv : v ∈ P.vertices) : edgeStarSpan P v = ⊤ := by
  rw [edgeStarSpan_eq_vectorSpan P hv]
  apply Submodule.eq_top_of_finrank_eq
  change finrank ℝ (vectorSpan ℝ P.toSet) = finrank ℝ (E d)
  rw [finrank_euclideanSpace_fin]
  exact hP

end Papers.Polytopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/SimpleVertexBasis.lean -/




@[expose] public section

/-!
# The genuine edge basis at a simple vertex

The basis is derived from actual incident edges and full dimensionality.
Its coordinate functionals are nonnegative on the whole body, by the
edge maximum principle. Thus the orthant normalization used for deletion
is a conclusion of simplicity, rather than an extra geometric assumption.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem adj_iff_generalVertexStep (P : ConvexPolytope d) (u v : VertexType P) :
    (polytopeGraph P).Adj u v ↔ GeneralVertexStep P u.val v.val := by
  constructor
  · rintro ⟨hne, e, he, hde, hue, hve⟩
    exact ⟨v.property, fun h => hne (Subtype.ext h), e, he, hde, hue, hve⟩
  · rintro ⟨_, hne, e, he, hde, hue, hve⟩
    exact ⟨fun h => hne (congrArg Subtype.val h), e, he, hde, hue, hve⟩

abbrev NeighborIndex (P : ConvexPolytope d) (v : VertexType P) :=
  (polytopeGraph P).neighborSet v

def neighborDirection (P : ConvexPolytope d) (v : VertexType P)
    (u : NeighborIndex P v) : E d := u.val.val - v.val

theorem range_neighborDirection (P : ConvexPolytope d) (v : VertexType P) :
    Set.range (neighborDirection P v) =
      {w | ∃ y, GeneralVertexStep P v.val y ∧ w = y - v.val} := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.val, (adj_iff_generalVertexStep P v u.val).mp u.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨⟨y, hy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hy.1⟩).mpr hy⟩, rfl⟩

theorem span_neighborDirection (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) : Submodule.span ℝ (Set.range (neighborDirection P v)) = ⊤ := by
  rw [range_neighborDirection]
  exact fullDim_edgeStarSpan P hP v.property

theorem card_neighbors_of_simple (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    Fintype.card (NeighborIndex P v) = finrank ℝ (E d) := by
  rw [SimpleGraph.card_neighborSet_eq_degree, finrank_euclideanSpace_fin]
  exact hs.trans hP

/-- No linear independence hypothesis is assumed: it follows from the
degree-d condition and the actual edge-star spanning theorem. -/
theorem simple_neighbor_directions_independent
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    LinearIndependent ℝ (neighborDirection P v) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [span_neighborDirection P hP v]) (card_neighbors_of_simple P hP v hs)

def simpleVertexBasis (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) : Basis (NeighborIndex P v) ℝ (E d) :=
  basisOfTopLeSpanOfCardEqFinrank (neighborDirection P v)
    (by rw [span_neighborDirection P hP v]) (card_neighbors_of_simple P hP v hs)

@[simp] theorem simpleVertexBasis_apply
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (u : NeighborIndex P v) :
    simpleVertexBasis P hP v hs u = u.val.val - v.val := by
  simp only [simpleVertexBasis, coe_basisOfTopLeSpanOfCardEqFinrank, neighborDirection]

/-- The ordinary edge-basis coordinates of every body point are
nonnegative after translating the simple vertex to the origin. -/
theorem simpleVertexBasis_coordinates_nonneg
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (x : E d) (hx : x ∈ P.toSet)
    (i : NeighborIndex P v) :
    0 ≤ (simpleVertexBasis P hP v hs).repr (x - v.val) i := by
  let b := simpleVertexBasis P hP v hs
  let l : E d →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  have hmax : ∀ y, GeneralVertexStep P v.val y → (-l) y ≤ (-l) v.val := by
    intro y hy
    let u : NeighborIndex P v :=
      ⟨⟨y, hy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hy.1⟩).mpr hy⟩
    have heq : l (y - v.val) = if i = u then 1 else 0 := by
      change b.coord i (y - v.val) = _
      have hbu : b u = y - v.val := simpleVertexBasis_apply P hP v hs u
      rw [← hbu]
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
    have hn : 0 ≤ l (y - v.val) := by
      rw [heq]
      split_ifs <;> norm_num
    simp only [map_sub] at hn
    change -l y ≤ -l v.val
    linarith
  have h := vertex_max_of_edge_max P (-l) v.property hmax x hx
  change 0 ≤ l (x - v.val)
  simp only [map_sub, ContinuousLinearMap.neg_apply] at *
  linarith

end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/SubpolytopeFaces.lean -/





@[expose] public section

/-!
# Retaining exposed faces in a smaller convex hull

An exposed face remains a face of any intermediate polytope containing it.
In particular an actual edge remains an edge after deleting other vertices.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem face_of_body_subset (P Q : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) (hQP : Q.toSet ⊆ P.toSet) (hFQ : F ⊆ Q.toSet) : Q.IsFace F := by
  obtain ⟨x, hx⟩ := hF.2
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hxP : x ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x := by
    have hx' := hx
    rw [hl] at hx'
    exact hx'
  refine ⟨?_, ⟨x, hx⟩⟩
  intro _
  refine ⟨l, ?_⟩
  ext z
  constructor
  · intro hz
    have hzP : z ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l z := by
      have hz' := hz
      rw [hl] at hz'
      exact hz'
    exact ⟨hFQ hz, fun y hy => hzP.2 y (hQP hy)⟩
  · rintro ⟨hzQ, hzmax⟩
    rw [hl]
    exact ⟨hQP hzQ, fun y hy => (hxP.2 y hy).trans (hzmax x (hFQ hx))⟩

theorem vertexSubset_body_subset (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) :
    (vertexSubsetPolytope P S hne hsub).toSet ⊆ P.toSet :=
  convexHull_mono hsub

theorem step_in_vertexSubset (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices)
    {x y : E d} (hx : x ∈ S) (hy : y ∈ S) (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep (vertexSubsetPolytope P S hne hsub) x y := by
  obtain ⟨_, hneXY, F, hF, hdF, hxF, hyF⟩ := hxy
  have hseg : F = segment ℝ x y := edge_eq_segment P hF hdF (hsub hx) (hsub hy) hxF hyF hneXY
  have hFQ : F ⊆ (vertexSubsetPolytope P S hne hsub).toSet := by
    rw [hseg]
    exact (convex_convexHull ℝ (S : Set (E d))).segment_subset
      (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)
  exact ⟨hy, hneXY, F, face_of_body_subset P _ hF
    (vertexSubset_body_subset P S hne hsub) hFQ, hdF, hxF, hyF⟩

theorem vectorSpan_polytope_vertices (P : ConvexPolytope d) :
    vectorSpan ℝ P.toSet = vectorSpan ℝ (P.vertices : Set (E d)) := by
  change vectorSpan ℝ (convexHull ℝ (P.vertices : Set (E d))) = _
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

theorem actual_vertices_card_gt_dim (P : ConvexPolytope d) : P.dim < P.vertices.card := by
  letI : Nonempty (VertexType P) := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨⟨v, hv⟩⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ
    (fun v : VertexType P => v.val)
  have hrange : Set.range (fun v : VertexType P => v.val) = (P.vertices : Set (E d)) := by
    ext v
    simp
  rw [hrange, ← vectorSpan_polytope_vertices P] at h
  have hcard : Fintype.card (VertexType P) = P.vertices.card := by simp
  rw [hcard] at h
  exact Nat.lt_of_succ_le h

theorem deleteVertex_coordinates (P : ConvexPolytope d) (K : Subfield ℝ)
    (hK : CoordinatesIn K P) (v : E d) (hne : (P.vertices.erase v).Nonempty) :
    CoordinatesIn K (deleteVertex P v hne) := by
  intro w hw i
  exact hK w (Finset.mem_of_mem_erase hw) i

end Papers.Polytopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/FiniteConvexGeometry.lean -/










@[expose] public section

/-!
# Finite convex hulls and one-dimensional exposed faces

The argument for `mem_hull_of_maximizers` is adapted from Daniele Cappello's
Apache-2.0-licensed `FacciaArgmax` module; see THIRD_PARTY.md. Its proof needs
only a normed vector space, so the stronger inner-product hypothesis in that
source is omitted here.
-/

noncomputable section
namespace Papers.Geometry
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_hull_of_maximizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmax : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l y) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  classical
  rw [Finset.convexHull_eq] at hy
  obtain ⟨w, hw0, hw1, hwy⟩ := hy
  have hM : ∀ x ∈ s, l x ≤ l y := fun x hx =>
    hmax x (subset_convexHull ℝ _ hx)
  have hyrep : y = ∑ x ∈ s, w x • x := by
    rw [← hwy, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rfl
  have hly : l y = ∑ x ∈ s, w x * l x := by
    rw [hyrep, map_sum]
    congr 1
    funext x
    rw [map_smul]
    rfl
  have hactive : ∀ x ∈ s, 0 < w x → l x = l y := by
    intro x hx hwx
    by_contra hne
    have hlt : l x < l y := lt_of_le_of_ne (hM x hx) hne
    have hsum : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l y := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact mul_le_mul_of_nonneg_left (hM z hz) (hw0 z hz)
      · exact ⟨x, hx, mul_lt_mul_of_pos_left hlt hwx⟩
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    rw [hly] at hsum
    exact lt_irrefl _ hsum
  have hzero : ∀ x ∈ s, ¬l x = l y → w x = 0 := by
    intro x hx hne
    by_contra hw
    exact hne (hactive x hx (lt_of_le_of_ne (hw0 x hx) (Ne.symm hw)))
  let sf : Finset E := s.filter (fun x => l x = l y)
  have hsub : sf ⊆ s := Finset.filter_subset _ _
  have hw1' : ∑ x ∈ sf, w x = 1 := by
    rw [← hw1]
    symm
    apply (Finset.sum_subset hsub ?_).symm
    intro x hx hnx
    apply hzero x hx
    intro heq
    exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
  have hyrep' : y = ∑ x ∈ sf, w x • x := by
    rw [hyrep]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have : w x = 0 := by
      apply hzero x hx
      intro heq
      exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
    rw [this, zero_smul]
  have hmem : y ∈ convexHull ℝ (sf : Set E) := by
    rw [Finset.convexHull_eq]
    refine ⟨w, fun z hz => hw0 z (hsub hz), hw1', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact hyrep'.symm
  have hset : (sf : Set E) = {x ∈ (s : Set E) | l x = l y} := by
    ext x
    simp [sf]
  rw [← hset]
  exact hmem

theorem mem_hull_of_minimizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmin : ∀ w ∈ convexHull ℝ (s : Set E), l y ≤ l w) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  simpa only [ContinuousLinearMap.neg_apply, neg_inj] using
    mem_hull_of_maximizers s (-l) hy (by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin)

theorem linear_lower_bound_on_convexHull (s : Set E) (l : E →L[ℝ] ℝ)
    (a : ℝ) (ha : ∀ x ∈ s, a ≤ l x) :
    ∀ x ∈ convexHull ℝ s, a ≤ l x :=
  convexHull_min ha (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) a)

/-- A finite convex hull contained in an affine line is a genuine closed
segment with endpoints among its generators. Degenerate segments are allowed. -/
theorem finite_hull_parallel_eq_segment (s : Finset E) (hs : s.Nonempty)
    (δ : E) (hδ : δ ≠ 0)
    (hparallel : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Submodule.span ℝ {δ}) :
    ∃ x ∈ s, ∃ y ∈ s, convexHull ℝ (s : Set E) = segment ℝ x y := by
  classical
  have hnot : δ ∉ (⊥ : Submodule ℝ E) := by simpa using hδ
  obtain ⟨g, hg, _⟩ := Submodule.exists_le_ker_of_notMem hnot
  let l : E →ₗ[ℝ] ℝ := (g δ)⁻¹ • g
  have hl : l δ = 1 := by simp [l, hg]
  obtain ⟨x, hx, hxmin⟩ := s.exists_min_image l hs
  obtain ⟨y, hy, hymax⟩ := s.exists_max_image l hs
  have hform (z : E) (hz : z ∈ s) : z - x = (l z - l x) • δ := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hparallel z hz x hx)
    have he : a = l z - l x := by
      have h := congrArg l ha
      simpa only [map_smul, map_sub, smul_eq_mul, hl, mul_one] using h
    exact (he ▸ ha).symm
  have hgen : (s : Set E) ⊆ segment ℝ x y := by
    intro z hz
    have hlow := hxmin z hz
    have hupp := hymax z hz
    have hxy := hxmin y hy
    by_cases hb : l y - l x = 0
    · have hzval : l z - l x = 0 := by linarith
      have hzx : z = x := by
        have h := hform z hz
        rw [hzval, zero_smul, sub_eq_zero] at h
        exact h
      rw [hzx]
      exact left_mem_segment ℝ x y
    · have hbpos : 0 < l y - l x := lt_of_le_of_ne (sub_nonneg.mpr hxy) (Ne.symm hb)
      rw [segment_eq_image']
      refine ⟨(l z - l x) / (l y - l x), ⟨div_nonneg (sub_nonneg.mpr hlow) hbpos.le,
        (div_le_one hbpos).mpr (by linarith)⟩, ?_⟩
      change x + ((l z - l x) / (l y - l x)) • (y - x) = z
      rw [hform y hy, smul_smul, div_mul_cancel₀ _ hb, ← hform z hz]
      module
  refine ⟨x, hx, y, hy, Set.Subset.antisymm
    (convexHull_min hgen (convex_segment x y)) ?_⟩
  exact (convex_convexHull ℝ (s : Set E)).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)

end Papers.Geometry

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/SimpleVertexCorner.lean -/







@[expose] public section

/-!
# Cutting off the corner at a simple vertex

The height is the sum of the genuine edge-basis coordinates. It is zero
at the chosen vertex and one at every neighbor. Every other actual vertex
has height strictly greater than one. Deleting the simple vertex is
exactly the intersection with the height-at-least-one halfspace.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def cornerHeight (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (x : E d) : ℝ :=
  ∑ i : NeighborIndex P v, (simpleVertexBasis P hP v hs).repr (x - v.val) i

@[simp] theorem cornerHeight_self (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    cornerHeight P hP v hs v.val = 0 := by
  simp [cornerHeight]

@[simp] theorem cornerHeight_neighbor (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (u : NeighborIndex P v) :
    cornerHeight P hP v hs u.val.val = 1 := by
  unfold cornerHeight
  rw [← simpleVertexBasis_apply P hP v hs u, Basis.repr_self]
  simp

theorem mem_corner_simplex_of_height_le_one
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (x : E d) (hx : x ∈ P.toSet)
    (hheight : cornerHeight P hP v hs x ≤ 1) :
    x ∈ convexHull ℝ (insert v.val (Set.range (fun u : NeighborIndex P v => u.val.val))) := by
  let b := simpleVertexBasis P hP v hs
  let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
  let w : Option (NeighborIndex P v) → ℝ
    | none => 1 - ∑ i, c i
    | some i => c i
  let z : Option (NeighborIndex P v) → E d
    | none => v.val
    | some i => i.val.val
  have hc : ∀ i, 0 ≤ c i := simpleVertexBasis_coordinates_nonneg P hP v hs x hx
  have hsum : ∑ i, c i ≤ 1 := hheight
  have hrep : ∑ i, c i • (i.val.val - v.val) = x - v.val := by
    simpa only [b, c, simpleVertexBasis_apply] using b.sum_repr (x - v.val)
  have hsumx : ∑ i, c i • i.val.val = x - v.val + (∑ i, c i) • v.val := by
    calc
      _ = ∑ i, (c i • (i.val.val - v.val) + c i • v.val) := by
        apply Finset.sum_congr rfl
        intro i _
        module
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_smul, hrep]
  apply mem_convexHull_of_exists_fintype w z
  · intro o
    cases o with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hc i
  · simp only [Fintype.sum_option, w]
    ring
  · intro o
    cases o with
    | none => exact Set.mem_insert _ _
    | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · simp only [Fintype.sum_option, w, z]
    rw [hsumx]
    module

/-- The strict corner inequality follows from extremality, without an
extra general-position or nondegeneracy assumption. -/
theorem cornerHeight_gt_one_of_non_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) {x : E d} (hx : x ∈ P.vertices)
    (hxv : x ≠ v.val) (hnot : ¬GeneralVertexStep P v.val x) :
    1 < cornerHeight P hP v hs x := by
  by_contra h
  let S : Set (E d) := insert v.val (Set.range (fun u : NeighborIndex P v => u.val.val))
  have hS : S ⊆ (P.vertices : Set (E d)) := by
    rintro y (rfl | ⟨u, rfl⟩)
    · exact v.property
    · exact u.val.property
  have hxc : x ∈ convexHull ℝ S :=
    mem_corner_simplex_of_height_le_one P hP v hs x (vertex_mem_body P hx) (le_of_not_gt h)
  have hext : x ∈ (convexHull ℝ S).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hS)
      ⟨hxc, vertex_is_extreme P hx⟩
  have hxS : x ∈ S := extremePoints_convexHull_subset hext
  rcases hxS with h | ⟨u, rfl⟩
  · exact hxv h
  · exact hnot ((adj_iff_generalVertexStep P v u.val).mp u.property)

theorem cornerHeight_ge_one_of_ne
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) {x : E d} (hx : x ∈ P.vertices) (hxv : x ≠ v.val) :
    1 ≤ cornerHeight P hP v hs x := by
  by_cases hstep : GeneralVertexStep P v.val x
  · let u : NeighborIndex P v :=
      ⟨⟨x, hx⟩, (adj_iff_generalVertexStep P v ⟨x, hx⟩).mpr hstep⟩
    exact (cornerHeight_neighbor P hP v hs u).ge
  · exact (cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hstep).le

theorem cornerHeight_eq_linear (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (x : E d) :
    cornerHeight P hP v hs x =
      (simpleVertexBasis P hP v hs).sumCoords x -
        (simpleVertexBasis P hP v hs).sumCoords v.val := by
  rw [← map_sub]
  change (∑ i, (simpleVertexBasis P hP v hs).repr (x - v.val) i) =
    ((simpleVertexBasis P hP v hs).repr (x - v.val)).sum (fun _ => id)
  exact (Finsupp.sum_fintype ((simpleVertexBasis P hP v hs).repr (x - v.val))
    (fun (_ : NeighborIndex P v) (r : ℝ) => r) (fun _ => rfl)).symm

theorem neighbor_mem_deletion (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) (u : NeighborIndex P v) :
    u.val.val ∈ (deleteVertex P v.val hne).toSet := by
  apply subset_convexHull ℝ _
  apply Finset.mem_erase.mpr
  have hstep := (adj_iff_generalVertexStep P v u.val).mp u.property
  exact ⟨hstep.2.1.symm, u.val.property⟩

/-- Deletion of a simple vertex is the literal geometric corner cut. -/
theorem deleteVertex_eq_height_halfspace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).toSet =
      {x ∈ P.toSet | 1 ≤ cornerHeight P hP v hs x} := by
  let b := simpleVertexBasis P hP v hs
  let h : E d →L[ℝ] ℝ := b.sumCoords.toContinuousLinearMap
  have hformula (x : E d) : cornerHeight P hP v hs x = h x - h v.val :=
    cornerHeight_eq_linear P hP v hs x
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨vertexSubset_body_subset P _ hne (Finset.erase_subset _ _) hx, ?_⟩
    have hbound : ∀ y ∈ P.vertices.erase v.val, 1 + h v.val ≤ h y := by
      intro y hy
      have hc := cornerHeight_ge_one_of_ne P hP v hs
        (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
      rw [hformula] at hc
      linarith
    have hc := Papers.Geometry.linear_lower_bound_on_convexHull
      (P.vertices.erase v.val : Set (E d)) h (1 + h v.val) hbound x hx
    rw [hformula]
    linarith
  · rintro x ⟨hxP, hxheight⟩
    by_contra hxQ
    obtain ⟨l, a, hbound, hax⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (P.vertices.erase v.val : Set (E d)))
      ((P.vertices.erase v.val).finite_toSet.isClosed_convexHull ℝ) hxQ
    have hav : a < l v.val := by
      by_contra hav
      have hpbound : ∀ y ∈ P.vertices, l y ≤ a := by
        intro y hy
        by_cases hyv : y = v.val
        · simpa only [hyv] using (le_of_not_gt hav)
        · exact (hbound y (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hyv, hy⟩))).le
      exact (not_lt_of_ge (le_su_toSet P l hpbound x hxP)) hax
    let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
    have hc : ∀ i, 0 ≤ c i := simpleVertexBasis_coordinates_nonneg P hP v hs x hxP
    have hlrep : l x - l v.val = ∑ i, c i * (l i.val.val - l v.val) := by
      rw [← map_sub, ← b.sum_repr (x - v.val), map_sum]
      simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, c]
    have hsbound : (∑ i, c i * (l i.val.val - l v.val)) ≤
        (∑ i, c i) * (a - l v.val) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hbound _ (neighbor_mem_deletion P v hne i)).le _) (hc i)
    have hsumge : 1 ≤ ∑ i, c i := hxheight
    have hprod := mul_le_mul_of_nonpos_right hsumge (sub_nonpos.mpr hav.le)
    rw [one_mul] at hprod
    linarith

end Papers.Polytopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/SimpleDeletionDimension.lean -/



@[expose] public section

/-!
# Full dimension after deletion of a simple vertex

The strict vertex-count hypothesis provides a vertex outside the corner
simplex. A functional constant on the deletion is constant on every
neighbor, and the edge-basis expansion at that extra vertex forces its
common edge increment to vanish. The functional is therefore zero. This
proves full dimension without assuming that the deleted hull is a polytope
of the desired dimension.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def neighborVertices (P : ConvexPolytope d) (v : VertexType P) : Finset (E d) :=
  Finset.univ.image (fun u : NeighborIndex P v => u.val.val)

theorem neighborVertices_card (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) : (neighborVertices P v).card = d := by
  rw [neighborVertices, Finset.card_image_of_injective _
    (fun u w h => Subtype.ext (Subtype.ext h)), Finset.card_univ,
    card_neighbors_of_simple P hP v hs, finrank_euclideanSpace_fin]

theorem vertex_notMem_neighborVertices (P : ConvexPolytope d) (v : VertexType P) :
    v.val ∉ neighborVertices P v := by
  intro h
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
  exact ((adj_iff_generalVertexStep P v u.val).mp u.property).2.1 hu.symm

theorem exists_vertex_outside_corner (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    ∃ x ∈ P.vertices, x ≠ v.val ∧ ¬GeneralVertexStep P v.val x := by
  have hcount : (insert v.val (neighborVertices P v)).card < P.vertices.card := by
    rw [Finset.card_insert_of_notMem (vertex_notMem_neighborVertices P v),
      neighborVertices_card P hP v hs]
    exact hcard
  obtain ⟨x, hx, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcount
  have hxv : x ≠ v.val := by
    intro h
    apply hnot
    rw [h]
    exact Finset.mem_insert_self _ _
  refine ⟨x, hx, hxv, ?_⟩
  intro hstep
  apply hnot
  apply Finset.mem_insert_of_mem
  let u : NeighborIndex P v :=
    ⟨⟨x, hx⟩, (adj_iff_generalVertexStep P v ⟨x, hx⟩).mpr hstep⟩
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

theorem linearMap_eq_cornerHeight_mul
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (l : E d →ₗ[ℝ] ℝ) (c : ℝ)
    (hconst : ∀ u : NeighborIndex P v, l u.val.val = c) (x : E d) :
    l (x - v.val) = cornerHeight P hP v hs x * (c - l v.val) := by
  let b := simpleVertexBasis P hP v hs
  rw [← b.sum_repr (x - v.val), map_sum]
  simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, hconst]
  rw [← Finset.sum_mul]
  simp only [cornerHeight, map_sub]

/-- The full-dimensionality assertion in Theorem 3, for every ambient
dimension and every simple vertex satisfying the paper's count hypothesis. -/
theorem deleteVertex_fullDim_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFullDim := by
  obtain ⟨x, hx, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
  let Q := deleteVertex P v.val hne
  let W := vectorSpan ℝ Q.toSet
  let b := simpleVertexBasis P hP v hs
  have hxQ : x ∈ Q.toSet :=
    subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hxv, hx⟩)
  have hheight := cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hxnot
  have htop : W = ⊤ := by
    by_contra hW
    obtain ⟨z, hz⟩ : ∃ z : E d, z ∉ W := by
      by_contra h
      push_neg at h
      apply hW
      exact top_unique (fun z _ => h z)
    obtain ⟨g, hgz, hgW⟩ := Submodule.exists_le_ker_of_notMem hz
    let c := g x
    have hconst : ∀ y ∈ Q.toSet, g y = c := by
      intro y hy
      have hzero : g (y - x) = 0 := hgW (vsub_mem_vectorSpan ℝ hy hxQ)
      simpa only [map_sub, sub_eq_zero] using hzero
    have hneighbors : ∀ u : NeighborIndex P v, g u.val.val = c :=
      fun u => hconst _ (neighbor_mem_deletion P v hne u)
    have hline := linearMap_eq_cornerHeight_mul P hP v hs g c hneighbors x
    rw [map_sub] at hline
    have hproduct : (cornerHeight P hP v hs x - 1) * (c - g v.val) = 0 := by
      dsimp only [c] at *
      nlinarith [hline]
    have hzero : c - g v.val = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr (ne_of_gt hheight))
    have hbzero : ∀ u, g (b u) = 0 := by
      intro u
      rw [show b u = u.val.val - v.val from simpleVertexBasis_apply P hP v hs u,
        map_sub, hneighbors u, hzero]
    have h := congrArg g (b.sum_repr z)
    simp only [map_sum, map_smul, hbzero, smul_zero, Finset.sum_const_zero] at h
    exact hgz h.symm
  change finrank ℝ W = d
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

theorem simpleDeletion_nonempty
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    (P.vertices.erase v.val).Nonempty := by
  obtain ⟨x, hx, hxv, _⟩ := exists_vertex_outside_corner P hP v hs hcard
  exact ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩⟩

end Papers.Polytopes

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/SimpleDeletionFacet.lean -/




@[expose] public section

/-!
# The new simplex facet after deleting a simple vertex

The new face is the convex hull of precisely the actual neighbors. Its
supporting equation and its dimension are derived from the edge basis.
No combinatorial truncation operation is assumed in the statement.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem neighborIndex_nonempty_of_vertex_count
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    Nonempty (NeighborIndex P v) := by
  rcases isEmpty_or_nonempty (NeighborIndex P v) with he | hn
  · letI := he
    obtain ⟨x, hx, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
    have h := cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hxnot
    simp [cornerHeight] at h
    linarith
  · exact hn

theorem neighborVertices_coe (P : ConvexPolytope d) (v : VertexType P) :
    (neighborVertices P v : Set (E d)) =
      Set.range (fun u : NeighborIndex P v => u.val.val) := by
  ext x
  simp [neighborVertices]

theorem simple_neighbors_affineIndependent
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) :
    AffineIndependent ℝ (fun u : NeighborIndex P v => u.val.val) := by
  have h := (simple_neighbor_directions_independent P hP v hs).affineIndependent
  convert h.vadd (v := v.val) using 1
  funext u
  change u.val.val = v.val + (u.val.val - v.val)
  abel

def deletionFacetSet (P : ConvexPolytope d) (v : VertexType P) : Set (E d) :=
  convexHull ℝ (neighborVertices P v : Set (E d))

theorem deletionFacetSet_dimension
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    faceDim (deletionFacetSet P v) + 1 = d := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  have h := (simple_neighbors_affineIndependent P hP v hs).finrank_vectorSpan_add_one
  rw [card_neighbors_of_simple P hP v hs, finrank_euclideanSpace_fin] at h
  change finrank ℝ (vectorSpan ℝ (convexHull ℝ _)) + 1 = d
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan,
    neighborVertices_coe]
  exact h

/-- The cut hyperplane exposes exactly the neighbor simplex in the actual
deleted convex hull. -/
theorem deletionFacetSet_isFace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFace (deletionFacetSet P v) := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  let Q := deleteVertex P v.val hne
  let l : E d →L[ℝ] ℝ := (simpleVertexBasis P hP v hs).sumCoords.toContinuousLinearMap
  have hformula (x : E d) : cornerHeight P hP v hs x = l x - l v.val :=
    cornerHeight_eq_linear P hP v hs x
  have hbound : ∀ x ∈ Q.vertices, 1 + l v.val ≤ l x := by
    intro x hx
    have hh := cornerHeight_ge_one_of_ne P hP v hs
      (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    rw [hformula] at hh
    linarith
  have hattained : ∃ x ∈ Q.vertices, l x = 1 + l v.val := by
    let u : NeighborIndex P v := Classical.choice inferInstance
    refine ⟨u.val.val, ?_, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm, u.val.property⟩
    · have h := cornerHeight_neighbor P hP v hs u
      rw [hformula] at h
      linarith
  have hF := minimumFace_isFace Q l (1 + l v.val) hbound hattained
  have hvertices : Q.vertices.filter (fun x => x ∈ minimumFace Q l (1 + l v.val)) =
      neighborVertices P v := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, _, heq⟩ := Finset.mem_filter.mp hx
      have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
      have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
      have hstep : GeneralVertexStep P v.val x := by
        by_contra hnot
        have hgt := cornerHeight_gt_one_of_non_neighbor P hP v hs hxP hxv hnot
        rw [hformula, heq] at hgt
        linarith
      let u : NeighborIndex P v :=
        ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · intro hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      have huQ : u.val.val ∈ Q.vertices := Finset.mem_erase.mpr
        ⟨((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm, u.val.property⟩
      refine Finset.mem_filter.mpr ⟨huQ, vertex_mem_body Q huQ, ?_⟩
      have h := cornerHeight_neighbor P hP v hs u
      rw [hformula] at h
      linarith
  have hset : minimumFace Q l (1 + l v.val) = deletionFacetSet P v := by
    rw [face_eq_hull_vertices Q hF, hvertices]
    rfl
  exact hset ▸ hF

end Papers.Polytopes

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/SimpleDeletionFaces.lean -/



@[expose] public section

/-!
# The complete face dictionary for simple-vertex deletion

Every old face retains the convex hull of its remaining vertices. The only
other faces are the nonempty subsets of the neighbor simplex. This statement
uses actual exposed faces and actual vertices throughout; in particular, it
does not assume an abstract truncation or a combinatorial face dictionary.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem face_inter_subpolytope (P Q : ConvexPolytope d)
    (hQP : Q.toSet ⊆ P.toSet) {F : Set (E d)} (hF : P.IsFace F)
    (hne : (F ∩ Q.toSet).Nonempty) : Q.IsFace (F ∩ Q.toSet) := by
  obtain ⟨w, hwF, hwQ⟩ := hne
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hwmax : ∀ x ∈ P.toSet, l x ≤ l w := by
    have h : w ∈ P.toSet ∧ ∀ x ∈ P.toSet, l x ≤ l w := by
      have hw' := hwF
      rw [hl] at hw'
      exact hw'
    exact h.2
  refine ⟨?_, ⟨w, hwF, hwQ⟩⟩
  intro _
  refine ⟨l, ?_⟩
  ext x
  constructor
  · rintro ⟨hxF, hxQ⟩
    rw [hl] at hxF
    exact ⟨hxQ, fun y hy => hxF.2 y (hQP hy)⟩
  · rintro ⟨hxQ, hxmax⟩
    refine ⟨?_, hxQ⟩
    rw [hl]
    exact ⟨hQP hxQ, fun y hy => (hwmax y hy).trans (hxmax w hwQ)⟩

/-- An old nonempty face survives by erasing just the deleted vertex,
provided at least one of its vertices remains. -/
theorem old_face_after_vertex_deletion (P : ConvexPolytope d)
    (v : VertexType P) (hne : (P.vertices.erase v.val).Nonempty)
    {F : Set (E d)} (hF : P.IsFace F)
    (hremain : ((P.vertices.filter (· ∈ F)).erase v.val).Nonempty) :
    (deleteVertex P v.val hne).IsFace
      (convexHull ℝ (((P.vertices.filter (· ∈ F)).erase v.val : Finset (E d)) : Set (E d))) := by
  let Q := deleteVertex P v.val hne
  obtain ⟨w, hw⟩ := hremain
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨hwP, hwF⟩ := Finset.mem_filter.mp hw
  have hwQ : w ∈ Q.toSet :=
    vertex_mem_body Q (Finset.mem_erase.mpr ⟨hwv, hwP⟩)
  have h := face_inter_subpolytope P Q
    (vertexSubset_body_subset P _ hne (Finset.erase_subset _ _)) hF
    ⟨w, hwF, hwQ⟩
  have heq : F ∩ Q.toSet =
      convexHull ℝ (((P.vertices.filter (· ∈ F)).erase v.val : Finset (E d)) : Set (E d)) := by
    rw [face_eq_hull_vertices Q h]
    apply congrArg (convexHull ℝ)
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    change (x ∈ P.vertices.erase v.val ∧ x ∈ F ∧ x ∈ Q.toSet) ↔
      x ∈ (P.vertices.filter (· ∈ F)).erase v.val
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxv, hxP⟩, hxF, _⟩
      exact ⟨hxv, hxP, hxF⟩
    · rintro ⟨hxv, hxP, hxF⟩
      exact ⟨⟨hxv, hxP⟩, hxF,
        vertex_mem_body Q (Finset.mem_erase.mpr ⟨hxv, hxP⟩)⟩
  exact heq ▸ h

/-- Every nonempty subset of the neighbor simplex is a genuine exposed
face of the deletion. The exposing functional comes from the edge basis. -/
theorem neighbor_subset_isFace
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (S : Finset (E d)) (hS : S.Nonempty) (hsub : S ⊆ neighborVertices P v) :
    (deleteVertex P v.val hne).IsFace (convexHull ℝ (S : Set (E d))) := by
  let b := simpleVertexBasis P hP v hs
  let l : E d →L[ℝ] ℝ :=
    (b.constr ℝ (fun u => if u.val.val ∈ S then (1 : ℝ) else 0)).toContinuousLinearMap
  have hvalue (u : NeighborIndex P v) :
      l u.val.val - l v.val = if u.val.val ∈ S then 1 else 0 := by
    rw [← map_sub, ← simpleVertexBasis_apply P hP v hs u]
    exact b.constr_basis ℝ _ u
  have hbound : ∀ x ∈ neighborVertices P v, l x ≤ l v.val + 1 := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have h := hvalue u
    split_ifs at h <;> linarith
  have hiff : ∀ x ∈ neighborVertices P v,
      l x = l v.val + 1 ↔ x ∈ S := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have h := hvalue u
    split_ifs at h with hu
    · exact ⟨fun _ => hu, fun _ => by linarith⟩
    · constructor
      · intro h'
        linarith
      · exact fun h' => (hu h').elim
  have hglobal : ∀ x ∈ deletionFacetSet P v, l x ≤ l v.val + 1 :=
    convexHull_min hbound (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) _)
  have hSconstant : ∀ x ∈ convexHull ℝ (S : Set (E d)), l x = l v.val + 1 := by
    apply convexHull_min ?_ (convex_hyperplane (LinearMap.isLinear l.toLinearMap) _)
    intro x hx
    exact (hiff x (hsub hx)).mpr hx
  have hST : convexHull ℝ (S : Set (E d)) ⊆ deletionFacetSet P v :=
    convexHull_mono hsub
  obtain ⟨w, hw⟩ := hS
  have hwHull : w ∈ convexHull ℝ (S : Set (E d)) := subset_convexHull ℝ _ hw
  have hex : IsExposed ℝ (deletionFacetSet P v) (convexHull ℝ (S : Set (E d))) := by
    intro _
    refine ⟨l, ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨hST hx, ?_⟩
      intro y hy
      rw [hSconstant x hx]
      exact hglobal y hy
    · rintro ⟨hxT, hxmax⟩
      have hxeq : l x = l v.val + 1 :=
        le_antisymm (hglobal x hxT) (by
          have h := hxmax w (hST hwHull)
          rw [hSconstant w hwHull] at h
          exact h)
      have hxHull := PlatoniciL3.faccia_argmax (neighborVertices P v) l hxT hxmax
      apply convexHull_mono (s := {y ∈ (neighborVertices P v : Set (E d)) | l y = l x}) ?_ hxHull
      rintro y ⟨hy, hyl⟩
      exact (hiff y hy).mp (hyl.trans hxeq)
  exact isFace_of_isExposed_isFace _
    (deletionFacetSet_isFace P hP v hs hcard hne) hex ⟨w, hwHull⟩

/-- A functional strictly larger at the removed corner cannot attain its
maximum over the deletion at an old nonneighbor. -/
theorem nonneighbor_strict_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (l : E d →L[ℝ] ℝ) (M : ℝ)
    (hbound : ∀ u : NeighborIndex P v, l u.val.val ≤ M) (hv : M < l v.val)
    {x : E d} (hx : x ∈ P.vertices) (hxv : x ≠ v.val)
    (hnot : ¬GeneralVertexStep P v.val x) : l x < M := by
  let b := simpleVertexBasis P hP v hs
  let c : NeighborIndex P v → ℝ := fun i => b.repr (x - v.val) i
  have hc : ∀ i, 0 ≤ c i :=
    simpleVertexBasis_coordinates_nonneg P hP v hs x (vertex_mem_body P hx)
  have hrep : l x - l v.val = ∑ i, c i * (l i.val.val - l v.val) := by
    rw [← map_sub, ← b.sum_repr (x - v.val), map_sum]
    simp only [map_smul, smul_eq_mul, b, simpleVertexBasis_apply, map_sub, c]
  have hsbound : (∑ i, c i * (l i.val.val - l v.val)) ≤
      (∑ i, c i) * (M - l v.val) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hbound i) _) (hc i)
  have hsum : 1 < ∑ i, c i :=
    cornerHeight_gt_one_of_non_neighbor P hP v hs hx hxv hnot
  have hprod := mul_lt_mul_of_neg_right hsum (sub_neg.mpr hv)
  rw [one_mul] at hprod
  linarith

/-- The full geometric face dictionary. Neither branch assumes that the
candidate hull is a face of the deletion. -/
theorem simpleDeletion_face_iff
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (F : Set (E d)) :
    (deleteVertex P v.val hne).IsFace F ↔
      (∃ G : Set (E d), P.IsFace G ∧
        ((P.vertices.filter (· ∈ G)).erase v.val).Nonempty ∧
        F = convexHull ℝ (((P.vertices.filter (· ∈ G)).erase v.val : Finset (E d)) : Set (E d))) ∨
      (∃ S : Finset (E d), S.Nonempty ∧ S ⊆ neighborVertices P v ∧
        F = convexHull ℝ (S : Set (E d))) := by
  let Q := deleteVertex P v.val hne
  constructor
  · intro hF
    obtain ⟨w, hw⟩ := (facePolytope Q hF).vertices_nonempty
    obtain ⟨hwQ, hwF⟩ := Finset.mem_filter.mp hw
    obtain ⟨l, hl⟩ := hF.1 hF.2
    have hwm : w ∈ Q.toSet ∧ ∀ x ∈ Q.toSet, l x ≤ l w := by
      have hw' := hwF
      rw [hl] at hw'
      exact hw'
    have hFiff (x : E d) (hx : x ∈ Q.toSet) : x ∈ F ↔ l x = l w := by
      rw [hl]
      constructor
      · rintro ⟨_, hxmax⟩
        exact le_antisymm (hwm.2 x hx) (hxmax w hwm.1)
      · intro heq
        exact ⟨hx, fun y hy => by rw [heq]; exact hwm.2 y hy⟩
    by_cases hv : l v.val ≤ l w
    · left
      let G := minimumFace P (-l) (-l w)
      have hG : P.IsFace G := by
        apply minimumFace_isFace
        · intro x hx
          change -l w ≤ -l x
          apply neg_le_neg
          by_cases hxv : x = v.val
          · simpa only [hxv] using hv
          · exact hwm.2 x (vertex_mem_body Q (Finset.mem_erase.mpr ⟨hxv, hx⟩))
        · exact ⟨w, Finset.mem_of_mem_erase hwQ, rfl⟩
      have hvertices : Q.vertices.filter (· ∈ F) = (P.vertices.filter (· ∈ G)).erase v.val := by
        ext x
        constructor
        · rintro hx
          obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hxQ,
            Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hxQ, ?_⟩⟩
          exact ⟨vertex_mem_body P (Finset.mem_of_mem_erase hxQ),
            congrArg Neg.neg ((hFiff x (vertex_mem_body Q hxQ)).mp hxF)⟩
        · intro hx
          obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
          obtain ⟨hxP, hxG⟩ := Finset.mem_filter.mp hx
          have hxQ : x ∈ Q.vertices := Finset.mem_erase.mpr ⟨hxv, hxP⟩
          refine Finset.mem_filter.mpr ⟨hxQ, (hFiff x (vertex_mem_body Q hxQ)).mpr ?_⟩
          exact neg_injective hxG.2
      refine ⟨G, hG, ?_, ?_⟩
      · rw [← hvertices]
        exact ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwF⟩⟩
      · rw [face_eq_hull_vertices Q hF, hvertices]
    · right
      refine ⟨Q.vertices.filter (· ∈ F), ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwF⟩⟩,
        ?_, face_eq_hull_vertices Q hF⟩
      intro x hx
      obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
      have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
      have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
      have hstep : GeneralVertexStep P v.val x := by
        by_contra hnot
        have hlt := nonneighbor_strict_bound P hP v hs l (l w)
          (fun u => hwm.2 _ (neighbor_mem_deletion P v hne u))
          (lt_of_not_ge hv) hxP hxv hnot
        rw [(hFiff x (vertex_mem_body Q hxQ)).mp hxF] at hlt
        exact lt_irrefl _ hlt
      let u : NeighborIndex P v :=
        ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  · rintro (⟨G, hG, hr, rfl⟩ | ⟨S, hS, hsub, rfl⟩)
    · exact old_face_after_vertex_deletion P v hne hG hr
    · exact neighbor_subset_isFace P hP v hs hcard hne S hS hsub

end Papers.Polytopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/FaceVertexDictionary.lean -/



@[expose] public section

/-!
# Recovering the ordinary face order from vertex incidences

This is a geometric equivalence, derived from the convex-hull theorem for
actual faces. It is used to turn the simple-deletion face dictionary into
an order isomorphism, rather than weakening combinatorial equivalence to
an assumed list of incidences.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem vertex_mem_hull_vertexSubset_iff (P : ConvexPolytope d)
    (S : Finset (E d)) (hsub : S ⊆ P.vertices) (v : VertexType P) :
    v.val ∈ convexHull ℝ (S : Set (E d)) ↔ v.val ∈ S := by
  constructor
  · intro hv
    have hext : v.val ∈ (convexHull ℝ (S : Set (E d))).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hsub)
        ⟨hv, vertex_is_extreme P v.property⟩
    exact extremePoints_convexHull_subset hext
  · exact fun hv => subset_convexHull ℝ (S : Set (E d)) hv

/-- Map a finite subset of actual vertices through an arbitrary vertex
bijection. Nonvertices in the input are deliberately irrelevant. -/
def mapVertexFinset (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) : Finset (E e) :=
  (Finset.univ.filter (fun v : VertexType P => v.val ∈ S)).image (fun v => (b v).val)

theorem mapVertexFinset_mem_iff (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) (v : VertexType P) :
    (b v).val ∈ mapVertexFinset P Q b S ↔ v.val ∈ S := by
  simp only [mapVertexFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, heq⟩
    have h : w = v := b.injective (Subtype.ext heq)
    simpa only [h] using hw
  · exact fun h => ⟨v, h, rfl⟩

theorem mapVertexFinset_subset (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d)) :
    mapVertexFinset P Q b S ⊆ Q.vertices := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact (b v).property

theorem mapVertexFinset_nonempty (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q) (S : Finset (E d))
    (hS : S.Nonempty) (hsub : S ⊆ P.vertices) :
    (mapVertexFinset P Q b S).Nonempty := by
  obtain ⟨v, hv⟩ := hS
  exact ⟨(b ⟨v, hsub hv⟩).val, (mapVertexFinset_mem_iff P Q b S ⟨v, hsub hv⟩).mpr hv⟩

theorem face_le_iff_vertex_incidence (P : ConvexPolytope d) (F G : FaceType P) :
    F ≤ G ↔ ∀ v : VertexType P, v.val ∈ F.val → v.val ∈ G.val := by
  constructor
  · exact fun h v hv => h hv
  · intro h
    change F.val ⊆ G.val
    rw [face_eq_hull_vertices P F.property]
    apply convexHull_min ?_ (G.property.1.convex (convex_convexHull ℝ _))
    intro x hx
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    exact h ⟨x, hxP⟩ hxF

theorem face_eq_of_vertex_incidence (P : ConvexPolytope d) (F G : FaceType P)
    (h : ∀ v : VertexType P, v.val ∈ F.val ↔ v.val ∈ G.val) : F = G := by
  apply le_antisymm
  · exact (face_le_iff_vertex_incidence P F G).mpr (fun v => (h v).mp)
  · exact (face_le_iff_vertex_incidence P G F).mpr (fun v => (h v).mpr)

/-- A bijection preserving exactly the full families of actual face-vertex
sets induces an ordinary face-poset order isomorphism. Both coverage
directions are required. -/
def faceOrderIsoOfVertexIncidence (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, ∃ G : FaceType Q,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, ∃ F : FaceType P,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val) :
    FaceType P ≃o FaceType Q := by
  let f : FaceType P → FaceType Q := fun F => Classical.choose (hforward F)
  let g : FaceType Q → FaceType P := fun G => Classical.choose (hbackward G)
  have hf (F : FaceType P) (v : VertexType P) :
      (b v).val ∈ (f F).val ↔ v.val ∈ F.val :=
    Classical.choose_spec (hforward F) v
  have hg (G : FaceType Q) (v : VertexType P) :
      (b v).val ∈ G.val ↔ v.val ∈ (g G).val :=
    Classical.choose_spec (hbackward G) v
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro F
    apply face_eq_of_vertex_incidence P
    intro v
    exact (hg (f F) v).symm.trans (hf F v)
  · intro G
    apply face_eq_of_vertex_incidence Q
    intro w
    obtain ⟨v, rfl⟩ := b.surjective w
    exact (hf (g G) v).trans (hg G v).symm
  · intro F G
    rw [face_le_iff_vertex_incidence Q, face_le_iff_vertex_incidence P]
    constructor
    · intro h v hv
      exact (hf G v).mp (h (b v) ((hf F v).mpr hv))
    · intro h w hw
      obtain ⟨v, rfl⟩ := b.surjective w
      exact (hf G v).mpr (h v ((hf F v).mp hw))

theorem imageVertex_adj_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (u v : VertexType P) :
    (polytopeGraph Q).Adj (imageVertex φ u) (imageVertex φ v) ↔
      (polytopeGraph P).Adj u v := by
  constructor
  · rintro ⟨hne, F, hF, hdim, huF, hvF⟩
    let G : FaceType P := φ.symm ⟨F, hF⟩
    have hφG : φ G = ⟨F, hF⟩ := φ.apply_symm_apply _
    refine ⟨fun h => hne (congrArg (imageVertex φ) h), G.val, G.property, ?_, ?_, ?_⟩
    · have h := faceOrderIso_dimension φ G
      rw [hφG] at h
      exact h.symm.trans hdim
    · apply (imageVertex_mem_iff φ u G).mp
      simpa only [hφG] using huF
    · apply (imageVertex_mem_iff φ v G).mp
      simpa only [hφG] using hvF
  · rintro ⟨hne, F, hF, hdim, huF, hvF⟩
    let G : FaceType P := ⟨F, hF⟩
    refine ⟨fun h => hne ((vertexEquivOfFaceOrder φ).injective h),
      (φ G).val, (φ G).property, ?_, ?_, ?_⟩
    · exact (faceOrderIso_dimension φ G).trans hdim
    · exact (imageVertex_mem_iff φ u G).mpr huF
    · exact (imageVertex_mem_iff φ v G).mpr hvF

/-- Edge adjacency, and hence the actual neighbor set of a deleted simple
vertex, is determined by the face order. -/
def vertexGraphIsoOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : polytopeGraph P ≃g polytopeGraph Q where
  toEquiv := vertexEquivOfFaceOrder φ
  map_rel_iff' := by
    intro u v
    exact imageVertex_adj_iff φ u v

end Papers.Polytopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/SimpleDeletionIntrinsic.lean -/




@[expose] public section

/-!
# The intrinsic combinatorial type of simple-vertex deletion

The bijection on remaining vertices is induced by the original ordinary
face-order isomorphism. The complete geometric face dictionary supplies
both directions of face coverage; the vertex-incidence theorem then
constructs the required ordinary face-order isomorphism.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem mem_neighborVertices_iff_adj (P : ConvexPolytope d)
    (v u : VertexType P) :
    u.val ∈ neighborVertices P v ↔ (polytopeGraph P).Adj v u := by
  constructor
  · intro hu
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hu
    have heq : w.val = u := Subtype.ext hw
    exact heq ▸ w.property
  · intro hu
    exact Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩

def deleteVertexEquiv {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty) :
    VertexType (deleteVertex P v.val hneP) ≃ VertexType (deleteVertex Q w.val hneQ) where
  toFun x := ⟨(b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).val,
    Finset.mem_erase.mpr ⟨by
      intro heq
      have h : b ⟨x.val, Finset.mem_of_mem_erase x.property⟩ = b v :=
        (Subtype.ext heq).trans hb.symm
      exact (Finset.ne_of_mem_erase x.property) (congrArg Subtype.val (b.injective h)),
      (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).property⟩⟩
  invFun y := ⟨(b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩).val,
    Finset.mem_erase.mpr ⟨by
      intro heq
      have h : b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩ = v := Subtype.ext heq
      have h' := congrArg b h
      rw [b.apply_symm_apply, hb] at h'
      exact (Finset.ne_of_mem_erase y.property) (congrArg Subtype.val h'),
      (b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
    rw [b.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    change (b (b.symm ⟨y.val, Finset.mem_of_mem_erase y.property⟩)).val = y.val
    rw [b.apply_symm_apply]

@[simp] theorem deleteVertexEquiv_apply_val {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (x : VertexType (deleteVertex P v.val hneP)) :
    (deleteVertexEquiv b v w hb hneP hneQ x).val =
      (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩).val := rfl

theorem deleteVertexEquiv_inverse {P Q : ConvexPolytope d}
    (b : VertexType P ≃ VertexType Q) (v : VertexType P) (w : VertexType Q)
    (hb : b v = w) (hb' : b.symm w = v)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (x : VertexType (deleteVertex P v.val hneP)) :
    deleteVertexEquiv b.symm w v hb' hneQ hneP
      (deleteVertexEquiv b v w hb hneP hneQ x) = x := by
  apply Subtype.ext
  change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
  rw [b.symm_apply_apply]

theorem isSimple_imageVertex {P Q : ConvexPolytope d}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P)
    (hs : IsSimpleVertex P v) : IsSimpleVertex Q (imageVertex φ v) := by
  change (polytopeGraph Q).degree ((vertexGraphIsoOfFaceOrder φ) v) = Q.dim
  rw [(vertexGraphIsoOfFaceOrder φ).degree_eq, faceOrderIso_polytope_dim φ]
  exact hs

theorem vertex_mem_remaining_face_hull_iff (P : ConvexPolytope d)
    (v x : VertexType P) (hxv : x ≠ v) (G : Set (E d)) :
    x.val ∈ convexHull ℝ
      (((P.vertices.filter (· ∈ G)).erase v.val : Finset (E d)) : Set (E d)) ↔ x.val ∈ G := by
  rw [vertex_mem_hull_vertexSubset_iff P _
    (fun _ h => (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1) x]
  have hxne : x.val ≠ v.val := fun h => hxv (Subtype.ext h)
  constructor
  · intro h
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2
  · intro hxG
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_filter.mpr ⟨x.property, hxG⟩⟩

theorem deletion_face_forward {P Q : ConvexPolytope d}
    (φ : FaceType P ≃o FaceType Q) (hP : P.IsFullDim)
    (v : VertexType P) (w : VertexType Q) (hvw : imageVertex φ v = w)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase w.val).Nonempty)
    (F : FaceType (deleteVertex P v.val hneP)) :
    ∃ G : FaceType (deleteVertex Q w.val hneQ),
      ∀ x : VertexType (deleteVertex P v.val hneP),
        (deleteVertexEquiv (vertexEquivOfFaceOrder φ) v w hvw hneP hneQ x).val ∈ G.val ↔
          x.val ∈ F.val := by
  let b := vertexEquivOfFaceOrder φ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q w := hvw ▸ isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  rcases (simpleDeletion_face_iff P hP v hs hcard hneP F.val).mp F.property with
    ⟨H, hH, hremain, hF⟩ | ⟨S, hS, hsub, hF⟩
  · let H' : FaceType Q := φ ⟨H, hH⟩
    have hremainQ : ((Q.vertices.filter (· ∈ H'.val)).erase w.val).Nonempty := by
      obtain ⟨x, hx⟩ := hremain
      obtain ⟨hxv, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxP, hxH⟩ := Finset.mem_filter.mp hx
      let u : VertexType P := ⟨x, hxP⟩
      refine ⟨(b u).val, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨(b u).property, ?_⟩⟩⟩
      · intro heq
        have h : b u = b v := (Subtype.ext heq).trans hvw.symm
        exact hxv (congrArg Subtype.val (b.injective h))
      · exact (imageVertex_mem_iff φ u ⟨H, hH⟩).mpr hxH
    let G : FaceType (deleteVertex Q w.val hneQ) :=
      ⟨_, old_face_after_vertex_deletion Q w hneQ H'.property hremainQ⟩
    refine ⟨G, ?_⟩
    intro x
    let u : VertexType P := ⟨x.val, Finset.mem_of_mem_erase x.property⟩
    have huv : u ≠ v := fun h => (Finset.ne_of_mem_erase x.property) (congrArg Subtype.val h)
    have hbu : b u ≠ w := by
      intro h
      exact huv (b.injective (h.trans hvw.symm))
    change (b u).val ∈ G.val ↔ u.val ∈ F.val
    rw [hF]
    change (b u).val ∈ convexHull ℝ
      (((Q.vertices.filter (· ∈ H'.val)).erase w.val : Finset (E d)) : Set (E d)) ↔ _
    rw [vertex_mem_remaining_face_hull_iff Q w (b u) hbu H'.val,
      vertex_mem_remaining_face_hull_iff P v u huv H]
    exact imageVertex_mem_iff φ u ⟨H, hH⟩
  · let S' := mapVertexFinset P Q b S
    have hSvertices : S ⊆ P.vertices := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hsub hx)
      exact u.val.property
    have hS' : S'.Nonempty := mapVertexFinset_nonempty P Q b S hS hSvertices
    have hsub' : S' ⊆ neighborVertices Q w := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      have huS : u.val ∈ S := (Finset.mem_filter.mp hu).2
      have hadj := (mem_neighborVertices_iff_adj P v u).mp (hsub huS)
      apply (mem_neighborVertices_iff_adj Q w (b u)).mpr
      rw [← hvw]
      exact (imageVertex_adj_iff φ v u).mpr hadj
    let G : FaceType (deleteVertex Q w.val hneQ) :=
      ⟨_, neighbor_subset_isFace Q hQ w hsQ hcardQ hneQ S' hS' hsub'⟩
    refine ⟨G, ?_⟩
    intro x
    let u : VertexType P := ⟨x.val, Finset.mem_of_mem_erase x.property⟩
    change (b u).val ∈ convexHull ℝ (S' : Set (E d)) ↔ u.val ∈ F.val
    rw [hF, vertex_mem_hull_vertexSubset_iff Q S' (mapVertexFinset_subset P Q b S) (b u),
      vertex_mem_hull_vertexSubset_iff P S hSvertices u]
    exact mapVertexFinset_mem_iff P Q b S u

/-- Simple-vertex deletion has a combinatorially determined face poset.
The input is the ordinary original face-order isomorphism, with no
additional rank, incidence, or deletion-compatibility hypothesis. -/
theorem simpleDeletion_combinatoriallyEquivalent
    {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hneP : (P.vertices.erase v.val).Nonempty)
    (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty) :
    CombinatoriallyEquivalent (deleteVertex P v.val hneP)
      (deleteVertex Q (imageVertex φ v).val hneQ) := by
  let w := imageVertex φ v
  let b := vertexEquivOfFaceOrder φ
  let b' := deleteVertexEquiv b v w rfl hneP hneQ
  have hbback : imageVertex φ.symm w = v := b.symm_apply_apply v
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q w := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  refine ⟨faceOrderIsoOfVertexIncidence _ _ b'
    (deletion_face_forward φ hP v w rfl hs hcard hneP hneQ) ?_⟩
  intro G
  obtain ⟨F, hF⟩ := deletion_face_forward φ.symm hQ w v hbback hsQ hcardQ hneQ hneP G
  refine ⟨F, ?_⟩
  intro x
  have h := (hF (b' x)).symm
  have heq : deleteVertexEquiv (vertexEquivOfFaceOrder φ.symm) w v hbback hneQ hneP (b' x) = x := by
    apply Subtype.ext
    change (b.symm (b ⟨x.val, Finset.mem_of_mem_erase x.property⟩)).val = x.val
    rw [b.symm_apply_apply]
  simpa only [heq] using h

/-- The geometric and combinatorial clauses of the deletion theorem,
including the existence of a nonempty, full-dimensional deleted hull. -/
theorem simpleDeletion_geometry
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) :
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      ∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ) := by
  let hne := simpleDeletion_nonempty P hP v hs hcard
  exact ⟨hne, deleteVertex_fullDim_of_simple P hP v hs hcard hne,
    fun _ φ hneQ => simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneQ⟩

/-- Deletion carries every realization over K to a realization of the
intrinsic deleted type over the same K. The reverse implication requires
the separate restoration theorem. -/
theorem RealizableOver.delete_of_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ)
    (hPK : RealizableOver P K) : RealizableOver (deleteVertex P v.val hne) K := by
  obtain ⟨Q, ⟨φ⟩, hQK⟩ := hPK
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hsQ : IsSimpleVertex Q (imageVertex φ v) := isSimple_imageVertex φ v hs
  have hcardQ : d + 1 < Q.vertices.card := by
    rw [← faceOrderIso_vertex_card φ]
    exact hcard
  let hneQ := simpleDeletion_nonempty Q hQ (imageVertex φ v) hsQ hcardQ
  exact ⟨deleteVertex Q (imageVertex φ v).val hneQ,
    simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneQ,
    deleteVertex_coordinates Q K hQK (imageVertex φ v).val hneQ⟩

end Papers.Polytopes

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/IncidenceCoreGeometry.lean -/




@[expose] public section

/-!
# Actual faces retained by an incidence core

These lemmas concern ordinary convex hulls and exposed faces.  They justify
replacing a selected set of vertices by its convex hull in the three-dimensional
point--facet incidence peeling argument.
-/

noncomputable section

namespace Papers.IncidenceCoreGeometry

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

variable {d : ℕ}

theorem dimension_mono {A B : Set (E d)} (h : A ⊆ B) :
    faceDim A ≤ faceDim B :=
  Submodule.finrank_mono (vectorSpan_mono ℝ h)

/-- Any set containing three distinct actual extreme vertices has affine
dimension at least two. No independent-frame hypothesis is supplied. -/
theorem three_vertices_dimension_of_subset (P : ConvexPolytope d)
    (S : Finset (E d)) (hSP : S ⊆ P.vertices) (A : Set (E d))
    (hSA : ∀ x∈S, x∈A) (hcard : 3 ≤ S.card) :
    2 ≤ faceDim A := by
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2<S.card by omega)
  by_contra hd
  have hcol : Collinear ℝ A :=
    collinear_iff_finrank_le_one.mpr (show finrank ℝ (vectorSpan ℝ A)≤1 by
      change faceDim A≤1
      omega)
  have hsub : ({x,y,z} : Set (E d))⊆A := by
    intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hSA _ hx
    · exact hSA _ hy
    · exact hSA _ hz
  exact vertices_not_collinear P (hSP hx) (hSP hy) (hSP hz)
    hxy hxz hyz (hcol.subset hsub)

theorem three_vertices_dimension (P : ConvexPolytope d) (A : Set (E d))
    (hcard : 3 ≤ (P.vertices.filter (· ∈ A)).card) :
    2 ≤ faceDim A :=
  three_vertices_dimension_of_subset P _ (Finset.filter_subset _ _) A
    (fun _ h => (Finset.mem_filter.mp h).2) hcard

/-- Equal-dimensional exposed faces which contain a set spanning their full
dimension coincide. This uses the strict dimension increase of actual faces. -/
theorem faces_eq_of_full_dim_common_subset (P : ConvexPolytope d)
    {F G A : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hA : A.Nonempty) (hAF : A⊆F) (hAG : A⊆G)
    (hFd : faceDim F≤faceDim A) (hGd : faceDim G≤faceDim A) : F=G := by
  have hAI : A⊆F∩G := fun x hx => ⟨hAF hx,hAG hx⟩
  have hI : P.IsFace (F∩G) := isFace_inter P hF hG (hA.mono hAI)
  have hd := dimension_mono hAI
  have hIF : F∩G=F := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P hI hF
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,hne⟩)
    omega
  have hIG : F∩G=G := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P hI hG
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    omega
  exact hIF.symm.trans hIG

/-- A two-face containing at least three retained vertices remains a
two-face of the smaller actual convex hull. -/
theorem retained_two_face (P Q : ConvexPolytope d)
    (hQP : Q.toSet⊆P.toSet) {F : Set (E d)}
    (hF : P.IsFace F) (hdF : faceDim F=2)
    (hcard : 3≤(Q.vertices.filter (· ∈ F)).card) :
    Q.IsFace (F∩Q.toSet) ∧ faceDim (F∩Q.toSet)=2 := by
  have hdim : 2≤faceDim (F∩Q.toSet) :=
    three_vertices_dimension_of_subset Q (Q.vertices.filter (·∈F))
      (Finset.filter_subset _ _) (F∩Q.toSet) (by
        intro x hx
        obtain ⟨hxQ,hxF⟩ := Finset.mem_filter.mp hx
        exact ⟨hxF,vertex_mem_body Q hxQ⟩) hcard
  have hle : faceDim (F∩Q.toSet)≤2 := by
    simpa only [hdF] using (dimension_mono (A:=F∩Q.toSet) Set.inter_subset_left)
  have hne : (F∩Q.toSet).Nonempty := by
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(Q.vertices.filter (· ∈ F)).card by omega)
    obtain ⟨hxQ,hxF⟩ := Finset.mem_filter.mp hx
    exact ⟨x,hxF,vertex_mem_body Q hxQ⟩
  exact ⟨face_inter_subpolytope P Q hQP hF hne,le_antisymm hle hdim⟩

/-- Two different retained old facets force the active vertex hull to retain
dimension three. This excludes the lower-dimensional incidence-core case. -/
theorem dimension_three_of_two_retained_faces (P Q : ConvexPolytope d)
    (hdP : P.dim=3) (hQP : Q.toSet⊆P.toSet)
    {F G : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F=2) (hdG : faceDim G=2) (hFG : F≠G)
    (hFc : 3≤(Q.vertices.filter (· ∈ F)).card)
    (hGc : 3≤(Q.vertices.filter (· ∈ G)).card) : Q.dim=3 := by
  obtain ⟨hRF,hdRF⟩ := retained_two_face P Q hQP hF hdF hFc
  obtain ⟨hRG,hdRG⟩ := retained_two_face P Q hQP hG hdG hGc
  have htop : Q.dim≤3 := by
    have hh := dimension_mono hQP
    change Q.dim≤P.dim at hh
    simpa only [hdP] using hh
  by_contra hdim
  have hQd : Q.dim≤2 := by omega
  have hQnonempty : Q.toSet.Nonempty := by
    obtain ⟨v,hv⟩ := Q.vertices_nonempty
    exact ⟨v,vertex_mem_body Q hv⟩
  have hRFeq : F∩Q.toSet=Q.toSet := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset Q hRF (toSet_isFace Q)
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    change faceDim (F∩Q.toSet)<Q.dim at hlt
    omega
  have hRGeq : G∩Q.toSet=Q.toSet := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset Q hRG (toSet_isFace Q)
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    change faceDim (G∩Q.toSet)<Q.dim at hlt
    omega
  apply hFG
  apply faces_eq_of_full_dim_common_subset P hF hG hQnonempty
  · intro x hx
    rw [←hRFeq] at hx
    exact hx.1
  · intro x hx
    rw [←hRGeq] at hx
    exact hx.1
  · rw [hdF,←hRFeq,hdRF]
  · rw [hdG,←hRGeq,hdRG]

end Papers.IncidenceCoreGeometry

end
end
end BundlePart18

section BundlePart19
/- Source: Papers/BipartiteIncidencePeeling.lean -/






@[expose] public section

noncomputable section

namespace Papers.BipartiteIncidencePeeling

open scoped BigOperators

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

def pointDegree (R : V → F → Prop) [DecidableRel R]
    (T : Finset F) (v : V) : ℕ := (T.filter (R v)).card

def faceDegree (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (f : F) : ℕ := (S.filter (fun v => R v f)).card

theorem sum_degrees (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (T : Finset F) :
    (∑ v ∈ S, pointDegree R T v) = ∑ f ∈ T, faceDegree R S f := by
  simp only [pointDegree,faceDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- The Euler incidence bound forces an eliminable point or face. This
lemma is purely finite counting; the geometric incidence bound is supplied
separately by the actual three-dimensional polytope argument. -/
theorem exists_degree_le_three
    (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (T : Finset F)
    (hbound : (∑ v ∈ S, (pointDegree R T v : ℤ)) <
      2*((S.card : ℤ)+T.card)) :
    (∃ v ∈ S, pointDegree R T v ≤ 3) ∨
      (∃ f ∈ T, faceDegree R S f ≤ 3) := by
  by_contra h
  have hv : ∀ v ∈ S, 4 ≤ pointDegree R T v := by
    intro v hv
    by_contra hd
    exact h (Or.inl ⟨v,hv,by omega⟩)
  have hf : ∀ f ∈ T, 4 ≤ faceDegree R S f := by
    intro f hf
    by_contra hd
    exact h (Or.inr ⟨f,hf,by omega⟩)
  have hleft : 4*(S.card : ℤ) ≤ ∑ v ∈ S, (pointDegree R T v : ℤ) := by
    calc
      4*(S.card : ℤ) = ∑ _v ∈ S, (4 : ℤ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, (pointDegree R T v : ℤ) :=
        Finset.sum_le_sum (fun v hvS => by exact_mod_cast hv v hvS)
  have hright : 4*(T.card : ℤ) ≤ ∑ f ∈ T, (faceDegree R S f : ℤ) := by
    calc
      4*(T.card : ℤ) = ∑ _f ∈ T, (4 : ℤ) := by simp [mul_comm]
      _ ≤ ∑ f ∈ T, (faceDegree R S f : ℤ) :=
        Finset.sum_le_sum (fun f hfT => by exact_mod_cast hf f hfT)
  have hsum : (∑ v ∈ S, (pointDegree R T v : ℤ)) =
      ∑ f ∈ T, (faceDegree R S f : ℤ) := by
    exact_mod_cast sum_degrees R S T
  linarith

end Papers.BipartiteIncidencePeeling

end
end
end BundlePart19

section BundlePart20
/- Source: Papers/PolytopeThreeIncidences.lean -/






@[expose] public section

/-!
# Three-dimensional vertex--facet incidence counts

Euler's formula and the actual ridge diamond give the exact total number
of vertex--facet incidences.  Removing any collection of facets only
strengthens the strict bipartite incidence bound used for rational peeling.
-/

noncomputable section
namespace Papers.PolytopeThreeIncidences

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeEulerThree
open Papers.IncidenceCoreGeometry

variable {d : ℕ}

def facetEdgeIncidenceEquiv (P : ConvexPolytope d) :
    (Σ F : Face P 2, FaceBelow P F.val.carrier 1) ≃
      (Σ E : Face P 1, Coface P E.val.carrier 2) where
  toFun x := ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  invFun x := ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem total_vertex_facet_incidences
    (P : ConvexPolytope d) (hdim : P.dim=3) :
    ∑ F : Face P 2, (Nat.card (VerticesOn P F.val.carrier) : ℤ) =
      2*((P.vertices.card : ℤ)+Nat.card (Face P 2)-2) := by
  classical
  letI : Fintype (Face P 1) := Fintype.ofFinite _
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  have hsum : (∑ F : Face P 2, Nat.card (VerticesOn P F.val.carrier)) =
      2*Nat.card (Face P 1) := by
    simp_rw [two_face_vertices_eq_edges]
    rw [← Nat.card_sigma,Nat.card_congr (facetEdgeIncidenceEquiv P),Nat.card_sigma]
    simp only [ridge_coface_card P 1 (by simpa using hdim)]
    simp [Nat.card_eq_fintype_card,mul_comm]
  have hsumZ : (∑ F : Face P 2, (Nat.card (VerticesOn P F.val.carrier) : ℤ)) =
      2*(Nat.card (Face P 1) : ℤ) := by exact_mod_cast hsum
  have heuler := euler_three P hdim
  linarith

theorem face_vertex_card_gt_dimension (P : ConvexPolytope d)
    (k : ℕ) (F : Face P k) : k<Nat.card (VerticesOn P F.val.carrier) := by
  have h := actual_vertices_card_gt_dim (facePolytope P F.val.isFace)
  have hd : (facePolytope P F.val.isFace).dim=k := by
    change faceDim (facePolytope P F.val.isFace).toSet=k
    rw [facePolytope_toSet,F.property]
  rw [hd] at h
  have hh : k<Nat.card (facePolytope P F.val.isFace).vertices := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using h
  rw [← Nat.card_congr (faceVerticesEquiv P F.val.isFace)] at hh
  exact hh

/-- Deleting unselected actual facets removes at least three incidences
per facet.  The remaining incidence count is strictly below twice the
number of remaining point and facet nodes. -/
theorem selected_facet_incidence_bound
    (P : ConvexPolytope d) (hdim : P.dim=3) (T : Finset (Face P 2)) :
    ∑ F∈T, (Nat.card (VerticesOn P F.val.carrier) : ℤ) <
      2*((P.vertices.card : ℤ)+T.card) := by
  classical
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  let w : Face P 2 → ℤ := fun F => Nat.card (VerticesOn P F.val.carrier)
  have hmin : ∀ F, 3≤w F := by
    intro F
    have h := face_vertex_card_gt_dimension P 2 F
    change (3:ℤ) ≤ (Nat.card (VerticesOn P F.val.carrier):ℤ)
    exact_mod_cast (show 3≤Nat.card (VerticesOn P F.val.carrier) by omega)
  have houtside : 3*((Finset.univ\T).card : ℤ) ≤ ∑ F∈Finset.univ\T,w F := by
    calc
      3*((Finset.univ\T).card : ℤ) = ∑ _F∈Finset.univ\T,(3:ℤ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun F _ => hmin F
  have hsplit : (∑ F∈T,w F)+(∑ F∈Finset.univ\T,w F)=∑ F,w F :=
    Finset.sum_add_sum_compl T w
  have hcard : T.card+(Finset.univ\T).card=Nat.card (Face P 2) := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_add_card_compl T
  have htotal := total_vertex_facet_incidences P hdim
  change (∑ F,w F)=_ at htotal
  have hcardZ : (T.card:ℤ)+(Finset.univ\T).card=Nat.card (Face P 2) := by
    exact_mod_cast hcard
  change (∑ F∈T,w F)<_
  have hn : (0:ℤ)≤(Finset.univ\T).card := by exact_mod_cast Nat.zero_le ((Finset.univ\T).card)
  linarith

end Papers.PolytopeThreeIncidences

end
end
end BundlePart20

section BundlePart21
/- Source: ActualVertexLinkWeights.lean -/





@[expose] public section

/-!
# Exact facet weights around an actual vertex

The facets containing a vertex form the facets of its genuine
three-dimensional vertex figure. The vertices of each figure facet are
exactly the original edges at the fixed vertex contained in that facet.
Applying the three-dimensional incidence formula therefore gives the
weighted identity used by graph-conditioned boundary growth.
-/

noncomputable section
namespace Papers.RationalityTen.ActualVertexLinkWeights

open Set Finset
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerFour Papers.PolytopeThreeIncidences

variable {d : ℕ}

/-- Actual edges at a fixed vertex that lie in the specified face. -/
abbrev EdgesAtVertexBelow (P : ConvexPolytope d) (v : E d) (A : Set (E d)) :=
  {e : IncidentFace P v 1 // e.val.val.carrier ⊆ A}

def edgesAtVertexBelowEquiv (P : ConvexPolytope d) (v : E d) (A : Set (E d)) :
    EdgesAtVertexBelow P v A ≃
      {e : Face P 1 // e.val.carrier ⊆ A ∧ v ∈ e.val.carrier} where
  toFun e := ⟨e.val.val, e.property, e.val.property⟩
  invFun e := ⟨⟨e.val, e.property.2⟩, e.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Zero-dimensional subfaces of an exposed face are its actual vertices. -/
def zeroFaceBelowVerticesEquiv (P : ConvexPolytope d) {A : Set (E d)}
    (hA : P.IsFace A) : FaceBelow P A 0 ≃ VerticesOn P A :=
  (faceBelowEquiv P hA 0).trans
    ((zeroFaceEquiv (facePolytope P hA)).symm.trans (faceVerticesEquiv P hA).symm)

/-- Restrict the full vertex-figure correspondence to the interval below
one incident facet. No additional incidence hypothesis is needed. -/
def incidentEdgesFigureVerticesEquiv {P : ConvexPolytope d} {v : E d}
    (D : VertexFigureGaloisData P P.toSet v) (F : IncidentFace P v 3) :
    EdgesAtVertexBelow P v F.val.val.carrier ≃
      VerticesOn D.figure ((incidentFigureEquiv D 2) F).val.carrier := by
  let e : EdgesAtVertexBelow P v F.val.val.carrier ≃
      FaceBelow D.figure ((incidentFigureEquiv D 2) F).val.carrier 0 :=
    Equiv.subtypeEquiv (incidentFigureEquiv D 0) fun a =>
      D.map_subset_iff (incidentStar P v 0 a) (incidentStar P v 2 F)
  exact e.trans (zeroFaceBelowVerticesEquiv D.figure
    ((incidentFigureEquiv D 2) F).val.isFace)

/-- The exact total of the degrees within all facets incident to a vertex. -/
theorem vertex_facet_degree_sum (P : ConvexPolytope d) (hP : P.dim = 4)
    (v : P.vertices) :
    (∑ F : IncidentFace P v.val 3,
      (Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) : ℤ)) =
      2 * ((Nat.card (IncidentFace P v.val 1) : ℤ) +
        Nat.card (IncidentFace P v.val 3) - 2) := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have hD : D.figure.dim = 3 := figure_dim D v.property 3 hP
  have hvertices : D.figure.vertices.card = Nat.card (IncidentFace P v.val 1) := by
    calc
      _ = Nat.card D.figure.vertices := by simp
      _ = Nat.card (Face D.figure 0) := Nat.card_congr (zeroFaceEquiv D.figure)
      _ = _ := (Nat.card_congr (incidentFigureEquiv D 0)).symm
  have hfacets : Nat.card (Face D.figure 2) = Nat.card (IncidentFace P v.val 3) :=
    (Nat.card_congr (incidentFigureEquiv D 2)).symm
  calc
    _ = ∑ F : IncidentFace P v.val 3,
        (Nat.card (VerticesOn D.figure ((incidentFigureEquiv D 2) F).val.carrier) : ℤ) := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Nat.card_congr (incidentEdgesFigureVerticesEquiv D F)]
    _ = ∑ F : Face D.figure 2,
        (Nat.card (VerticesOn D.figure F.val.carrier) : ℤ) :=
      Equiv.sum_comp (incidentFigureEquiv D 2)
        (fun F : Face D.figure 2 =>
          (Nat.card (VerticesOn D.figure F.val.carrier) : ℤ))
    _ = 2 * ((D.figure.vertices.card : ℤ) + Nat.card (Face D.figure 2) - 2) :=
      total_vertex_facet_incidences D.figure hD
    _ = _ := by rw [hvertices, hfacets]

/-- Every incident facet contributes at least three original edges at the
fixed vertex, because its corresponding polygon has at least three vertices. -/
theorem incident_facet_degree_ge_three (P : ConvexPolytope d) (hP : P.dim = 4)
    (v : P.vertices) (F : IncidentFace P v.val 3) :
    3 ≤ Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  rw [Nat.card_congr (incidentEdgesFigureVerticesEquiv D F)]
  have h := face_vertex_card_gt_dimension D.figure 2 ((incidentFigureEquiv D 2) F)
  omega

/-- Euler's formula for the actual vertex link, in integer form. -/
theorem vertex_link_weight_identity (P : ConvexPolytope d) (hP : P.dim = 4)
    (v : P.vertices) :
    (∑ F : IncidentFace P v.val 3,
      ((Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) : ℤ) - 2)) =
      2 * (Nat.card (IncidentFace P v.val 1) : ℤ) - 4 := by
  have h := vertex_facet_degree_sum P hP v
  have hsum : (∑ F : IncidentFace P v.val 3,
      ((Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) : ℤ) - 2)) =
      (∑ F : IncidentFace P v.val 3,
        (Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) : ℤ)) -
        2 * (Nat.card (IncidentFace P v.val 3) : ℤ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
    ring
  rw [hsum]
  linarith

/-- A natural-number form suited to exact finite certificate arithmetic.
The added four avoids any truncation in the degree on the right. -/
theorem vertex_link_weight_identity_nat (P : ConvexPolytope d) (hP : P.dim = 4)
    (v : P.vertices) :
    (∑ F : IncidentFace P v.val 3,
      (Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) - 2)) + 4 =
      2 * Nat.card (IncidentFace P v.val 1) := by
  have hcast : ((∑ F : IncidentFace P v.val 3,
      (Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) - 2) : ℕ) : ℤ) =
      ∑ F : IncidentFace P v.val 3,
        ((Nat.card (EdgesAtVertexBelow P v.val F.val.val.carrier) : ℤ) - 2) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro F _
    exact Nat.cast_sub (by
      have h := incident_facet_degree_ge_three P hP v F
      omega)
  have h := vertex_link_weight_identity P hP v
  rw [← hcast] at h
  omega

end Papers.RationalityTen.ActualVertexLinkWeights

end
end
end BundlePart21
