module

public import Unimodular.CubicalFan
public import Unimodular.PolytopeFaces

@[expose] public section

noncomputable section

namespace Unimodular

attribute [local instance] Classical.propDecidable

/-- Labels covering all listed vertices and all supporting normals. Injectivity is
unnecessary for the face-lattice theorem; no faces are included as assumptions. -/
structure IncidenceLabeling {n : ℕ} (P : SmoothReflexivePresentation n)
    (V F : Type*) where
  vertex : V → Lattice n
  normal : F → Lattice n
  vertex_mem : ∀ v, vertex v ∈ P.vertices
  vertices_surj : ∀ v ∈ P.vertices, ∃ a, vertex a = v
  normal_mem : ∀ f, normal f ∈ P.normals
  normals_surj : ∀ u ∈ P.normals, ∃ f, normal f = u

namespace IncidenceLabeling

open SmoothReflexivePresentation

variable {n m : ℕ} {P : SmoothReflexivePresentation n}
  {Q : SmoothReflexivePresentation m} {V F : Type*}
  (A : IncidenceLabeling P V F) (B : IncidenceLabeling Q V F)

theorem face_le_iff (E G : P.GeometricFace) :
    E ≤ G ↔ ∀ v, embed (A.vertex v) ∈ E.val → embed (A.vertex v) ∈ G.val := by
  change E.val ⊆ G.val ↔ ∀ v, embed (A.vertex v) ∈ E.val → embed (A.vertex v) ∈ G.val
  rw [P.face_subset_iff_vertices]
  constructor
  · exact fun h v => h (A.vertex v) (A.vertex_mem v)
  · intro h v hv
    obtain ⟨a, rfl⟩ := A.vertices_surj v hv
    exact h a

def transportedNormals (E : P.GeometricFace) : Set (Lattice m) :=
  B.normal '' {f | ∀ x ∈ E.val, pairing x (A.normal f) = 1}

theorem transportedNormals_subset (E : P.GeometricFace) :
    A.transportedNormals B E ⊆ (Q.normals : Set (Lattice m)) := by
  rintro u ⟨f, hf, rfl⟩
  exact B.normal_mem f

/-- The corresponding actual face is the intersection of the corresponding
supporting facets; the empty face is handled separately, including dimension zero. -/
def transport (E : P.GeometricFace) : Q.GeometricFace :=
  if h : E.val.Nonempty then
    ⟨Q.normalIntersection (A.transportedNormals B E),
      Q.normalIntersection_convex _,
      Q.normalIntersection_extreme _ (A.transportedNormals_subset B E)⟩
  else
    ⟨∅, convex_empty, ⟨Set.empty_subset _, by intro x hx y hy z hz; exact hz.elim⟩⟩

/-- Transport preserves the complete vertex-incidence relation. This is derived
from the actual facet-intersection theorem, not stipulated for the transported face. -/
theorem transport_vertex (hinc : ∀ v f,
  pairing (embed (A.vertex v)) (A.normal f) = 1 ↔
    pairing (embed (B.vertex v)) (B.normal f) = 1) (E : P.GeometricFace) (v : V) :
    embed (B.vertex v) ∈ (A.transport B E).val ↔ embed (A.vertex v) ∈ E.val := by
  unfold transport
  split_ifs with hne
  · change embed (B.vertex v) ∈ Q.normalIntersection (A.transportedNormals B E) ↔
      embed (A.vertex v) ∈ E.val
    constructor
    · rintro ⟨hv, hcommon⟩
      rw [P.face_eq_normalIntersection E.property.1 E.property.2 hne]
      refine ⟨P.vertex_mem ⟨A.vertex v, A.vertex_mem v⟩, ?_⟩
      intro u hu
      obtain ⟨f, rfl⟩ := A.normals_surj u hu.1
      apply (hinc v f).2
      exact hcommon _ ⟨f, hu.2, rfl⟩
    · intro hv
      refine ⟨Q.vertex_mem ⟨B.vertex v, B.vertex_mem v⟩, ?_⟩
      rintro u ⟨f, hf, rfl⟩
      exact (hinc v f).1 (hf _ hv)
  · change embed (B.vertex v) ∈ (∅ : Set (Ambient m)) ↔ embed (A.vertex v) ∈ E.val
    simp only [Set.mem_empty_iff_false, false_iff]
    exact fun hv => hne ⟨embed (A.vertex v),hv⟩

/-- Equal vertex/facet incidence yields an order isomorphism of the actual convex
face lattices. Completeness of the vertex and facet descriptions is proved in
`PolytopeFaces`, so this theorem retains all geometric faces. -/
def faceOrderIso (hinc : ∀ v f,
  pairing (embed (A.vertex v)) (A.normal f) = 1 ↔
    pairing (embed (B.vertex v)) (B.normal f) = 1) : P.GeometricFace ≃o Q.GeometricFace where
  toFun := A.transport B
  invFun := B.transport A
  left_inv E := by
    apply Subtype.ext
    apply Set.Subset.antisymm
    · apply (A.face_le_iff _ _).2
      intro v hv
      exact (A.transport_vertex B hinc E v).1
        ((B.transport_vertex A (fun v f => (hinc v f).symm) (A.transport B E) v).1 hv)
    · apply (A.face_le_iff _ _).2
      intro v hv
      exact (B.transport_vertex A (fun v f => (hinc v f).symm) (A.transport B E) v).2
        ((A.transport_vertex B hinc E v).2 hv)
  right_inv E := by
    apply Subtype.ext
    apply Set.Subset.antisymm
    · apply (B.face_le_iff _ _).2
      intro v hv
      exact (B.transport_vertex A (fun v f => (hinc v f).symm) E v).1
        ((A.transport_vertex B hinc (B.transport A E) v).1 hv)
    · apply (B.face_le_iff _ _).2
      intro v hv
      exact (A.transport_vertex B hinc (B.transport A E) v).2
        ((B.transport_vertex A (fun v f => (hinc v f).symm) E v).2 hv)
  map_rel_iff' := by
    intro E G
    constructor
    · intro h
      apply (A.face_le_iff E G).2
      intro v hv
      apply (A.transport_vertex B hinc G v).1
      apply h
      exact (A.transport_vertex B hinc E v).2 hv
    · intro h
      apply (B.face_le_iff (A.transport B E) (A.transport B G)).2
      intro v hv
      exact (A.transport_vertex B hinc G v).2
        (h ((A.transport_vertex B hinc E v).1 hv))

end IncidenceLabeling

namespace CubicalFan

variable {n : ℕ} {fan : SmoothCompleteFan n} (C : CubicalFan fan)

/-- All cube labels refer to the literal polar vertices and primitive normal rays. -/
def polarLabeling (hfan : fan.PositiveCoordinateCriterion) :
    IncidenceLabeling (fan.polarPresentation hfan) (Fin n → Bool) (Fin n × Bool) where
  vertex ε := latticeDualVertex (C.basis ε)
  normal p := C.ray p.1 p.2
  vertex_mem ε := Finset.mem_image.2 ⟨C.basis ε, C.basis_mem ε, rfl⟩
  vertices_surj v hv := C.polar_vertices_surj v hv
  normal_mem p := (fan.mem_rayFinset _).2 (C.ray_mem p.1 p.2)
  normals_surj u hu := by
    have hur := (fan.mem_rayFinset u).1 hu
    rw [C.rays_eq] at hur
    exact hur

/-- An order isomorphism of all actual faces, obtained from the exact Boolean
vertex/facet incidence and the independently proved finite-inequality face theorem. -/
def faceOrderIso_coordinateCube (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).GeometricFace ≃o
      (coordinateCubePresentation n).GeometricFace :=
  (C.polarLabeling hfan).faceOrderIso
    ((coordinateCubeFan_cubical n).polarLabeling (coordinateCubeFan_criterion n))
    (by
      intro ε p
      exact (C.polar_incidence hfan ε p.1 p.2).trans
        ((coordinateCubeFan_cubical n).polar_incidence
          (coordinateCubeFan_criterion n) ε p.1 p.2).symm)

end CubicalFan

/-- The face poset of the literal real coordinate cube, ordered by set inclusion. -/
abbrev CubeFace (n : ℕ) :=
  {E : Set (Ambient n) // Convex ℝ E ∧
    IsExtreme ℝ {x : Ambient n | ∀ i, -1 ≤ x i ∧ x i ≤ 1} E}

instance (n : ℕ) : PartialOrder (CubeFace n) := inferInstanceAs
  (PartialOrder {E : Set (Ambient n) // Convex ℝ E ∧
    IsExtreme ℝ {x : Ambient n | ∀ i, -1 ≤ x i ∧ x i ≤ 1} E})

def coordinateCubeFaceOrderIso (n : ℕ) :
    (coordinateCubePresentation n).GeometricFace ≃o CubeFace n where
  toFun E := ⟨E.val, E.property.1, by
    rw [← coordinateCubePresentation_carrier n]
    exact E.property.2⟩
  invFun E := ⟨E.val, E.property.1, by
    rw [coordinateCubePresentation_carrier n]
    exact E.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Combinatorial cubicality means an isomorphism with the actual face lattice of
`[-1,1]^n`; it is not inferred merely from numbers of vertices or facets. -/
def SmoothReflexivePresentation.IsCombinatorialCube {n : ℕ}
    (P : SmoothReflexivePresentation n) : Prop :=
  Nonempty (P.GeometricFace ≃o CubeFace n)

theorem CubicalFan.polar_isCombinatorialCube {n : ℕ} {fan : SmoothCompleteFan n}
    (C : CubicalFan fan) (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).IsCombinatorialCube :=
  ⟨(C.faceOrderIso_coordinateCube hfan).trans (coordinateCubeFaceOrderIso n)⟩

end Unimodular

end
