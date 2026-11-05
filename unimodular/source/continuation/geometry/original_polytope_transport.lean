module

public import Continuation.Geometry.OriginalPolytopeBasic

/-!
# Linear transport of literal faces and primitive edges

These lemmas concern subsets of the actual real ambient spaces. The edge
predicate includes its convex extreme face, affine dimension, primitive
integral direction, and a positive segment from the original vertex.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open PaperVerification.OriginalLatticeCharts
open scoped Classical

namespace Unimodular.OriginalPolytopeTransport

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]

@[simp] theorem inverse_image_image (e : V ≃ₗ[ℝ] W) (S : Set V) :
    e.symm '' (e '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
    rw [e.symm_apply_apply] at he
    exact he ▸ hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

@[simp] theorem image_inverse_image (e : V ≃ₗ[ℝ] W) (S : Set W) :
    e '' (e.symm '' S) = S := by
  simpa only [LinearEquiv.symm_symm] using inverse_image_image e.symm S

theorem convex_image_iff (e : V ≃ₗ[ℝ] W) (S : Set V) :
    Convex ℝ (e '' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have h' := h.linear_image e.symm.toLinearMap
    change Convex ℝ (e.symm '' (e '' S)) at h'
    rw [inverse_image_image] at h'
    exact h'
  · intro h
    exact h.linear_image e.toLinearMap

theorem extreme_image_iff (e : V ≃ₗ[ℝ] W) (Q S : Set V) :
    IsExtreme ℝ (e '' Q) (e '' S) ↔ IsExtreme ℝ Q S := by
  constructor
  · intro h
    have h' := isExtreme_image_linearEquiv e.symm h
    rw [inverse_image_image, inverse_image_image] at h'
    exact h'
  · exact isExtreme_image_linearEquiv e

/-- Affine dimension is unchanged, including empty and lower-dimensional
faces. No full-dimensionality assumption is used in this transport. -/
theorem finrank_vectorSpan_image (e : V ≃ₗ[ℝ] W) (S : Set V) :
    Module.finrank ℝ (vectorSpan ℝ (e '' S)) =
      Module.finrank ℝ (vectorSpan ℝ S) := by
  change Module.finrank ℝ (vectorSpan ℝ (e.toLinearMap.toAffineMap '' S)) = _
  rw [← e.toLinearMap.toAffineMap.map_vectorSpan]
  exact e.finrank_map_eq (vectorSpan ℝ S)

/-- A facet is a nonempty maximal proper convex extreme face. -/
def IsGeometricFacet (Q S : Set V) : Prop :=
  S.Nonempty ∧ Convex ℝ S ∧ IsExtreme ℝ Q S ∧ S ≠ Q ∧
    ∀ F : Set V, Convex ℝ F → IsExtreme ℝ Q F →
      F ≠ Q → S ⊆ F → F = S

theorem facet_image (e : V ≃ₗ[ℝ] W) {Q S : Set V}
    (h : IsGeometricFacet Q S) : IsGeometricFacet (e '' Q) (e '' S) := by
  obtain ⟨hne, hconv, hext, hproper, hmax⟩ := h
  refine ⟨hne.image e, hconv.linear_image e.toLinearMap,
    isExtreme_image_linearEquiv e hext, ?_, ?_⟩
  · intro he
    exact hproper (e.injective.image_injective he)
  · intro F hFconv hFext hFproper hSF
    have hpreext : IsExtreme ℝ Q (e.symm '' F) := by
      have h' := isExtreme_image_linearEquiv e.symm hFext
      rw [inverse_image_image] at h'
      exact h'
    have hpreproper : e.symm '' F ≠ Q := by
      intro he
      have h' := congrArg (fun A : Set V => e '' A) he
      rw [image_inverse_image] at h'
      exact hFproper h'
    have hsub : S ⊆ e.symm '' F := by
      intro x hx
      exact ⟨e x, hSF ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have he := hmax (e.symm '' F) (hFconv.linear_image e.symm.toLinearMap)
      hpreext hpreproper hsub
    have h' := congrArg (fun A : Set V => e '' A) he
    simpa only [image_inverse_image] using h'

theorem facet_image_iff (e : V ≃ₗ[ℝ] W) (Q S : Set V) :
    IsGeometricFacet (e '' Q) (e '' S) ↔ IsGeometricFacet Q S := by
  constructor
  · intro h
    have h' := facet_image e.symm h
    rw [inverse_image_image, inverse_image_image] at h'
    exact h'
  · exact facet_image e

variable {N M : Type*} [AddCommGroup N] [AddCommGroup M]

/-- A primitive inward edge direction in the original lattice. Its face and
positive segment are actual subsets and points of the original real space. -/
def IsPrimitiveEdgeDirection (ι : N →+ V) (Q : Set V) (v d : N) : Prop :=
  TauCeti.IsPrimitive d ∧ ∃ F : Set V,
    Convex ℝ F ∧ IsExtreme ℝ Q F ∧ ι v ∈ F ∧
    Module.finrank ℝ (vectorSpan ℝ F) = 1 ∧
    ∃ t : ℝ, 0 < t ∧ ι v + t • ι d ∈ F

/-- Integral and real equivalences compatible with the lattice embeddings
transport the full geometric edge witness. -/
theorem primitiveEdge_image {ι : N →+ V} {κ : M →+ W}
    (e : N ≃ₗ[ℤ] M) (f : V ≃ₗ[ℝ] W)
    (hcomp : ∀ x : N, f (ι x) = κ (e x))
    {Q : Set V} {v d : N} (h : IsPrimitiveEdgeDirection ι Q v d) :
    IsPrimitiveEdgeDirection κ (f '' Q) (e v) (e d) := by
  obtain ⟨hd, F, hconv, hext, hv, hdim, t, ht, hstep⟩ := h
  refine ⟨e.isPrimitive_iff.mpr hd, f '' F,
    hconv.linear_image f.toLinearMap, isExtreme_image_linearEquiv f hext,
    ⟨ι v, hv, hcomp v⟩, ?_, t, ht, ?_⟩
  · rw [finrank_vectorSpan_image, hdim]
  · refine ⟨ι v + t • ι d, hstep, ?_⟩
    rw [map_add, map_smul, hcomp, hcomp]

theorem primitiveEdge_image_iff {ι : N →+ V} {κ : M →+ W}
    (e : N ≃ₗ[ℤ] M) (f : V ≃ₗ[ℝ] W)
    (hcomp : ∀ x : N, f (ι x) = κ (e x))
    (Q : Set V) (v d : N) :
    IsPrimitiveEdgeDirection κ (f '' Q) (e v) (e d) ↔
      IsPrimitiveEdgeDirection ι Q v d := by
  constructor
  · intro h
    have hinv (x : M) : f.symm (κ x) = ι (e.symm x) := by
      apply f.injective
      rw [f.apply_symm_apply, hcomp, e.apply_symm_apply]
    have h' := primitiveEdge_image e.symm f.symm hinv h
    simpa only [inverse_image_image, LinearEquiv.symm_apply_apply] using h'
  · exact primitiveEdge_image e f hcomp

end Unimodular.OriginalPolytopeTransport
