module

public import Continuation.Geometry.OriginalLatticePolar
public import Unimodular.Extensions
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Smooth reflexive polytopes in their original integral lattice

The input consists of original integral vertices and integral characters,
their actual evaluation pairing, smooth active bases, and equality of the
convex hull with the unit supporting halfspaces. Coordinates are constructed
from this data. No deep-monotonicity or matroid conclusion is an input field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open TauCeti.Toric PaperVerification.OriginalLatticeCharts
open scoped Classical BigOperators

universe u v

namespace Unimodular

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]

/-- A smooth reflexive polytope presented in the original lattice `N`.
The normals belong to the actual integral dual `N →+ ℤ`; the ambient real
pairing is their unique scalar extension along the integral lattice map.
The rank equality records the dimension, not a selected coordinate basis. -/
structure OriginalSmoothReflexivePresentation (n : ℕ) (ι : N →+ V) where
  lattice : IsIntegralLattice ι
  rank_eq : Module.finrank ℤ N = n
  vertices : Finset N
  normals : Finset (N →+ ℤ)
  vertices_nonempty : vertices.Nonempty
  basis : {v // v ∈ vertices} → Module.Basis (Fin n) ℤ (N →+ ℤ)
  basis_mem : ∀ v i, basis v i ∈ normals
  basis_active : ∀ v i, basis v i v.val = 1
  active_subset : ∀ v m, m ∈ normals → m v.val = 1 → ∃ i, basis v i = m
  normals_occur : ∀ m ∈ normals, ∃ v i, basis v i = m
  hull_eq : convexHull ℝ (ι '' (vertices : Set N)) =
    {x : V | ∀ m ∈ normals, lattice.realCharacter m x ≤ 1}

namespace OriginalSmoothReflexivePresentation

variable {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- Choosing the active bases from the ordinary existence statement of
smoothness constructs the presentation. This requires no global basis of
`N`, no coordinate model, and no deep-monotonicity hypothesis. The incidence
condition says that each of the listed supporting facets meets a vertex. -/
def ofActiveBases (hi : IsIntegralLattice ι) (hrank : Module.finrank ℤ N = n)
    (vertices : Finset N) (normals : Finset (N →+ ℤ))
    (hne : vertices.Nonempty)
    (hsmooth : ∀ v : {v // v ∈ vertices},
      ∃ c : Module.Basis (Fin n) ℤ (N →+ ℤ),
        (∀ i, c i ∈ normals ∧ c i v.val = 1) ∧
        (∀ m ∈ normals, m v.val = 1 → ∃ i, c i = m))
    (hoccur : ∀ m ∈ normals, ∃ v : {v // v ∈ vertices}, m v.val = 1)
    (hhull : convexHull ℝ (ι '' (vertices : Set N)) =
      {x : V | ∀ m ∈ normals, hi.realCharacter m x ≤ 1}) :
    OriginalSmoothReflexivePresentation n ι := by
  let c (v : {v // v ∈ vertices}) := Classical.choose (hsmooth v)
  have hc (v : {v // v ∈ vertices}) := Classical.choose_spec (hsmooth v)
  refine
    { lattice := hi
      rank_eq := hrank
      vertices := vertices
      normals := normals
      vertices_nonempty := hne
      basis := c
      basis_mem := fun v i => ((hc v).1 i).1
      basis_active := fun v i => ((hc v).1 i).2
      active_subset := fun v => (hc v).2
      normals_occur := ?_
      hull_eq := hhull }
  intro m hm
  obtain ⟨v, hv⟩ := hoccur m hm
  obtain ⟨i, hi⟩ := (hc v).2 m hm hv
  exact ⟨v, i, hi⟩

/-- The actual real convex hull in the original ambient vector space. -/
def carrier : Set V := convexHull ℝ (ι '' (P.vertices : Set N))

theorem mem_carrier_iff (x : V) :
    x ∈ P.carrier ↔ ∀ m ∈ P.normals, P.lattice.realCharacter m x ≤ 1 := by
  rw [carrier, P.hull_eq]
  rfl

theorem vertex_mem (v : {v // v ∈ P.vertices}) : ι v.val ∈ P.carrier :=
  subset_convexHull ℝ _ ⟨v.val, v.property, rfl⟩

/-- Primitivity of every listed normal follows from its occurrence in an
actual integral active basis. -/
theorem normal_primitive (m : N →+ ℤ) (hm : m ∈ P.normals) :
    TauCeti.IsPrimitive m := by
  obtain ⟨v, i, rfl⟩ := P.normals_occur m hm
  exact (P.basis v).isPrimitive i

/-- Finite freeness belongs to the original integral-lattice hypothesis,
so choosing coordinates adds no basis-existence premise. -/
def coordinateBasis : Module.Basis (Fin n) ℤ N := by
  letI : Module.Free ℤ N := P.lattice.free
  letI : Module.Finite ℤ N := P.lattice.finite
  exact Module.finBasisOfFinrankEq ℤ N P.rank_eq

include P

theorem coordinates_exist : Nonempty (Module.Basis (Fin n) ℤ N) :=
  ⟨P.coordinateBasis⟩

/-- The scalar-extension lattice condition identifies the original real
ambient dimension with the stated integral rank. -/
theorem ambient_finrank_eq : Module.finrank ℝ V = n :=
  P.lattice.finrank_eq.symm.trans P.rank_eq

variable (b : Module.Basis (Fin n) ℤ N)

/-- Scalar extension of the chosen integral basis in the actual original
ambient space. This name distinguishes it from standard-lattice basis coordinates. -/
abbrev ambientCoordinates : V ≃ₗ[ℝ] Ambient n :=
  PaperVerification.OriginalLatticeCharts.realCoordinates b P.lattice

/-- The original real pairing, using dual coordinates from the same basis. -/
theorem coordinate_pairing (x : V) (m : N →+ ℤ) :
    pairing (P.ambientCoordinates b x) (characterCoordinates b m) =
      P.lattice.realCharacter m x := by
  have h := realCharacterCoordinates_pairing b P.lattice
    (P.lattice.realCharacter m) x
  rw [realCharacterCoordinates_lattice] at h
  exact h

theorem coordinate_pairing_integral (x : N) (m : N →+ ℤ) :
    pairing (embed (b.equivFun x)) (characterCoordinates b m) = (m x : ℝ) := by
  change pairing (fun i => (b.equivFun x i : ℝ)) (characterCoordinates b m) = _
  have h := P.coordinate_pairing b (ι x) m
  simpa only [realCoordinates_lattice, IsIntegralLattice.realCharacter_apply,
    PaperVerification.ToricGeometry.embed, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using h

/-- An original vertex, retaining its original label, in integral coordinates. -/
def mappedVertex (v : {v // v ∈ P.vertices}) :
    {w : Lattice n // w ∈ P.vertices.image b.equivFun} :=
  ⟨b.equivFun v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩

/-- The inverse vertex map is the inverse integral basis equivalence. -/
def originalVertex (v : {w : Lattice n // w ∈ P.vertices.image b.equivFun}) :
    {w : N // w ∈ P.vertices} :=
  ⟨b.equivFun.symm v.val, by
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp v.property
    rw [← he, b.equivFun.symm_apply_apply]
    exact hw⟩

@[simp] theorem originalVertex_mappedVertex (v : {v // v ∈ P.vertices}) :
    P.originalVertex b (P.mappedVertex b v) = v := by
  apply Subtype.ext
  exact b.equivFun.symm_apply_apply v.val

@[simp] theorem mappedVertex_originalVertex
    (v : {w : Lattice n // w ∈ P.vertices.image b.equivFun}) :
    P.mappedVertex b (P.originalVertex b v) = v := by
  apply Subtype.ext
  exact b.equivFun.apply_symm_apply v.val

@[simp] theorem originalVertex_coordinates
    (v : {w : Lattice n // w ∈ P.vertices.image b.equivFun}) :
    b.equivFun (P.originalVertex b v).val = v.val :=
  b.equivFun.apply_symm_apply v.val

theorem coordinate_pairing_vertex
    (v : {w : Lattice n // w ∈ P.vertices.image b.equivFun}) (m : N →+ ℤ) :
    pairing (embed v.val) (characterCoordinates b m) =
      (m (P.originalVertex b v).val : ℝ) := by
  rw [← P.originalVertex_coordinates b v]
  exact P.coordinate_pairing_integral b _ m

/-- Equality of actual convex hulls, not just their integral points. -/
theorem carrier_coordinate_image :
    P.ambientCoordinates b '' P.carrier =
      convexHull ℝ (embed '' (P.vertices.image b.equivFun : Set (Lattice n))) :=
  originalRayHull_coordinate_image b P.lattice P.vertices

/-- The standard-coordinate presentation is constructed solely from the
original geometric presentation. Both primal and integral-dual maps are used. -/
def coordinatePresentation : SmoothReflexivePresentation n where
  vertices := P.vertices.image b.equivFun
  normals := P.normals.image (characterCoordinates b)
  vertices_nonempty := P.vertices_nonempty.image b.equivFun
  basis v := (P.basis (P.originalVertex b v)).map (characterCoordinates b)
  basis_mem v i := by
    change characterCoordinates b (P.basis (P.originalVertex b v) i) ∈
      P.normals.image (characterCoordinates b)
    exact Finset.mem_image.mpr ⟨_, P.basis_mem (P.originalVertex b v) i, rfl⟩
  basis_active v i := by
    change pairing (embed v.val)
      (characterCoordinates b (P.basis (P.originalVertex b v) i)) = 1
    rw [P.coordinate_pairing_vertex]
    exact_mod_cast P.basis_active (P.originalVertex b v) i
  active_subset v m hm hactive := by
    obtain ⟨m, hm0, rfl⟩ := Finset.mem_image.mp hm
    have hv : m (P.originalVertex b v).val = 1 := by
      rw [P.coordinate_pairing_vertex] at hactive
      exact_mod_cast hactive
    obtain ⟨i, hi⟩ := P.active_subset (P.originalVertex b v) m hm0 hv
    exact ⟨i, congrArg (characterCoordinates b) hi⟩
  normals_occur m hm := by
    obtain ⟨m, hm0, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨v, i, hi⟩ := P.normals_occur m hm0
    refine ⟨P.mappedVertex b v, i, ?_⟩
    change characterCoordinates b
      (P.basis (P.originalVertex b (P.mappedVertex b v)) i) = characterCoordinates b m
    rw [P.originalVertex_mappedVertex, hi]
  hull_eq := by
    rw [← P.carrier_coordinate_image b, carrier, P.hull_eq]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ m hm
      obtain ⟨m, hm0, rfl⟩ := Finset.mem_image.mp hm
      rw [P.coordinate_pairing]
      exact hx m hm0
    · intro hy
      refine ⟨(P.ambientCoordinates b).symm y, ?_,
        (P.ambientCoordinates b).apply_symm_apply y⟩
      intro m hm
      rw [← P.coordinate_pairing b]
      simpa only [LinearEquiv.apply_symm_apply] using
        hy (characterCoordinates b m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

@[simp] theorem coordinatePresentation_vertices :
    (P.coordinatePresentation b).vertices = P.vertices.image b.equivFun := rfl

@[simp] theorem coordinatePresentation_normals :
    (P.coordinatePresentation b).normals = P.normals.image (characterCoordinates b) := rfl

theorem coordinatePresentation_carrier :
    (P.coordinatePresentation b).carrier = P.ambientCoordinates b '' P.carrier :=
  (P.carrier_coordinate_image b).symm

@[simp] theorem mem_coordinatePresentation_carrier (x : V) :
    P.ambientCoordinates b x ∈ (P.coordinatePresentation b).carrier ↔
      x ∈ P.carrier := by
  rw [P.coordinatePresentation_carrier]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (P.ambientCoordinates b).injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The full real polar is transported with the original dual pairing. -/
theorem coordinatePresentation_polar :
    realCharacterCoordinates b P.lattice '' originalDualPolar P.carrier =
      coordinateDualPolar (P.coordinatePresentation b).carrier := by
  rw [originalDualPolar_coordinate_image, P.coordinatePresentation_carrier]

end OriginalSmoothReflexivePresentation
end Unimodular
