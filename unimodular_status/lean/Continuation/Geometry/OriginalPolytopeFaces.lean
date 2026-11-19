module

public import Continuation.Geometry.OriginalPolytopeTransport
public import Continuation.Geometry.OriginalLatticeInterior

/-! # Original vertices and primitive geometric facet normals -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open TauCeti.Toric PaperVerification.OriginalLatticeCharts
open Unimodular.OriginalPolytopeTransport
open scoped Classical

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- The supporting face in the original ambient real space. -/
def normalFace (m : N →+ ℤ) : Set V :=
  {x | x ∈ P.carrier ∧ P.lattice.realCharacter m x = 1}

/-- Facets are literal nonempty maximal proper convex faces. -/
def IsFacet (F : Set V) : Prop := IsGeometricFacet P.carrier F

/-- The geometric primitive facet normals use the original integral dual,
the actual real supporting inequality, and the actual face. -/
def geometricFacetNormals : Set (N →+ ℤ) :=
  {m | TauCeti.IsPrimitive m ∧
    (∀ x ∈ P.carrier, P.lattice.realCharacter m x ≤ 1) ∧ P.IsFacet (P.normalFace m)}

variable (b : Module.Basis (Fin n) ℤ N)

/-- No original extreme point is lost or artificially added by the finite list. -/
theorem extremePoints_eq_vertices :
    P.carrier.extremePoints ℝ = ι '' (P.vertices : Set N) := by
  let b := P.coordinateBasis
  exact originalRayHull_extremePoints b P.lattice P.vertices
    (P.coordinatePresentation b).extremePoints_eq_vertices

@[simp] theorem mem_coordinate_normals (m : N →+ ℤ) :
    characterCoordinates b m ∈ (P.coordinatePresentation b).normals ↔ m ∈ P.normals := by
  change characterCoordinates b m ∈ P.normals.image (characterCoordinates b) ↔ _
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Finset.mem_image.mp h
    exact (characterCoordinates b).injective he ▸ hm'
  · intro hm
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

/-- The coordinate supporting face is the image of precisely the original face. -/
theorem normalFace_coordinate_image (m : N →+ ℤ) :
    P.ambientCoordinates b '' P.normalFace m =
      (P.coordinatePresentation b).normalFace (characterCoordinates b m) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(P.mem_coordinatePresentation_carrier b x).mpr hx.1, ?_⟩
    rw [P.coordinate_pairing]
    exact hx.2
  · intro hy
    refine ⟨(P.ambientCoordinates b).symm y, ?_,
      (P.ambientCoordinates b).apply_symm_apply y⟩
    constructor
    · apply (P.mem_coordinatePresentation_carrier b _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hy.1
    · rw [← P.coordinate_pairing b]
      simpa only [LinearEquiv.apply_symm_apply] using hy.2

/-- Maximality among proper faces is preserved in both directions. -/
theorem coordinate_facet_iff (F : Set V) :
    (P.coordinatePresentation b).IsFacet (P.ambientCoordinates b '' F) ↔
      P.IsFacet F := by
  change IsGeometricFacet (P.coordinatePresentation b).carrier
    (P.ambientCoordinates b '' F) ↔ IsGeometricFacet P.carrier F
  rw [P.coordinatePresentation_carrier]
  exact facet_image_iff (P.ambientCoordinates b) P.carrier F

/-- The divisor notion of primitive coordinate vector agrees with the
intrinsic integral-functional notion before taking coordinates. -/
theorem primitive_normal_coordinate_iff (m : N →+ ℤ) :
    PrimitiveLatticeVector (characterCoordinates b m) ↔ TauCeti.IsPrimitive m :=
  (primitiveLatticeVector_iff_isPrimitive _).trans (characterCoordinates b).isPrimitive_iff

/-- Both supporting geometry and integral primitivity are retained. -/
theorem geometricFacetNormals_coordinate_iff (m : N →+ ℤ) :
    characterCoordinates b m ∈ (P.coordinatePresentation b).geometricFacetNormals ↔
      m ∈ P.geometricFacetNormals := by
  constructor
  · rintro ⟨hprim, hbound, hfacet⟩
    refine ⟨(primitive_normal_coordinate_iff b m).mp hprim, ?_, ?_⟩
    · intro x hx
      have h := hbound (P.ambientCoordinates b x)
        ((P.mem_coordinatePresentation_carrier b x).mpr hx)
      rwa [P.coordinate_pairing] at h
    · rw [← P.normalFace_coordinate_image b m] at hfacet
      exact (P.coordinate_facet_iff b (P.normalFace m)).mp hfacet
  · rintro ⟨hprim, hbound, hfacet⟩
    refine ⟨(primitive_normal_coordinate_iff b m).mpr hprim, ?_, ?_⟩
    · intro y hy
      have hx : (P.ambientCoordinates b).symm y ∈ P.carrier := by
        apply (P.mem_coordinatePresentation_carrier b _).mp
        simpa only [LinearEquiv.apply_symm_apply] using hy
      have h := hbound _ hx
      rw [← P.coordinate_pairing b] at h
      simpa only [LinearEquiv.apply_symm_apply] using h
    · rw [← P.normalFace_coordinate_image b m]
      exact (P.coordinate_facet_iff b (P.normalFace m)).mpr hfacet

/-- The original input normal list is exactly the actual primitive facet
normal set; this conclusion is proved rather than included in the structure. -/
theorem geometricFacetNormals_eq_normals :
    P.geometricFacetNormals = (P.normals : Set (N →+ ℤ)) := by
  let b := P.coordinateBasis
  ext m
  rw [← P.geometricFacetNormals_coordinate_iff b m,
    (P.coordinatePresentation b).geometricFacetNormals_eq_normals]
  exact P.mem_coordinate_normals b m

/-- Smoothness concerns precisely all geometric facet normals active at
the original vertex. The active basis is therefore geometric data, not a
coordinate assumption or a selected subset of the incident facets. -/
theorem activeFacetNormals_eq_range (v : {v // v ∈ P.vertices}) :
    {m : N →+ ℤ | m ∈ P.geometricFacetNormals ∧
      P.lattice.realCharacter m (ι v.val) = 1} = Set.range (P.basis v) := by
  ext m
  constructor
  · rintro ⟨hm, hactive⟩
    have hm' : m ∈ P.normals := by
      simpa only [P.geometricFacetNormals_eq_normals, Finset.mem_coe] using hm
    have hv : m v.val = 1 := by
      rw [IsIntegralLattice.realCharacter_apply] at hactive
      exact_mod_cast hactive
    exact P.active_subset v m hm' hv
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [P.geometricFacetNormals_eq_normals]
      exact P.basis_mem v i
    · rw [IsIntegralLattice.realCharacter_apply]
      exact_mod_cast P.basis_active v i

/-- Equality of whole original and coordinate geometric-normal sets. -/
theorem geometricFacetNormals_coordinate_image :
    characterCoordinates b '' P.geometricFacetNormals =
      (P.coordinatePresentation b).geometricFacetNormals := by
  ext m
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (P.geometricFacetNormals_coordinate_iff b m).mpr hm
  · intro hm
    refine ⟨(characterCoordinates b).symm m, ?_,
      (characterCoordinates b).apply_symm_apply m⟩
    apply (P.geometricFacetNormals_coordinate_iff b _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hm

end Unimodular.OriginalSmoothReflexivePresentation
