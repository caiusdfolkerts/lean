module

public import Continuation.Geometry.OriginalLatticeInputs
public import Continuation.Geometry.OriginalLatticeSubdivision
public import Mathlib.Analysis.Convex.Extreme

@[expose] public section

/-!
# The literal original ray hull and its canonical face fan

Linear coordinate changes preserve the actual convex hull, every convex
extreme face, and the pointed cone on that face.  These identities identify
the transported canonical seed with the proper-face fan of the original
ray hull, not merely a fan having the same ray count.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical NNReal

namespace PaperVerification.OriginalLatticeCharts

private theorem inverse_image_image {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (S : Set A) :
    e.symm '' (e '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
    rw [e.symm_apply_apply] at he
    exact he ▸ hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

private theorem image_inverse_image {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (S : Set B) :
    e '' (e.symm '' S) = S := by
  simpa only [LinearEquiv.symm_symm] using inverse_image_image e.symm S

/-- Extreme subsets, including nonsimplicial faces, are preserved. -/
theorem isExtreme_image_linearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B)
    {P S : Set A} (h : IsExtreme ℝ P S) :
    IsExtreme ℝ (e '' P) (e '' S) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro x ⟨x', hx, rfl⟩ y ⟨y', hy, rfl⟩ z ⟨z', hz, rfl⟩ hs
  have hm : e z' ∈ e '' openSegment ℝ x' y' := by
    change e.toLinearMap.toAffineMap z' ∈
      e.toLinearMap.toAffineMap '' openSegment ℝ x' y'
    rw [image_openSegment ℝ]
    exact hs
  obtain ⟨w, hw, he⟩ := hm
  have hwz : w = z' := e.injective he
  exact ⟨x', h.left_mem_of_mem_openSegment hx hy hz (hwz ▸ hw), rfl⟩

private theorem pointedHull_map_linearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (S : Set A) :
    (PointedCone.hull ℝ S).map e.toLinearMap = PointedCone.hull ℝ (e '' S) := by
  change Submodule.map (e.toLinearMap.restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 S) = Submodule.span ℝ≥0 (e '' S)
  rw [Submodule.map_span]
  rfl

universe u v

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

/-- The actual ray hull in the original ambient real space. -/
def originalRayHull (U : Finset N) : Set V :=
  convexHull ℝ (ι '' (U : Set N))

theorem originalRayHull_coordinate_image (U : Finset N) :
    realCoordinates b hi '' originalRayHull (ι := ι) U =
      convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n))) := by
  rw [originalRayHull]
  change (realCoordinates b hi).toLinearMap '' convexHull ℝ (ι '' (U : Set N)) = _
  rw [(realCoordinates b hi).toLinearMap.image_convexHull]
  rw [Finset.coe_image]
  simp only [Set.image_image]
  congr 1
  apply congrArg (fun f : N → Ambient n => f '' (U : Set N))
  funext x
  exact realCoordinates_lattice b hi x

theorem coordinateRayHull_inverse_image (U : Finset N) :
    (realCoordinates b hi).symm ''
      convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n))) = originalRayHull (ι := ι) U := by
  rw [← originalRayHull_coordinate_image b hi U, inverse_image_image]

theorem mem_originalRayHull_iff (U : Finset N) (x : V) :
    x ∈ originalRayHull (ι := ι) U ↔
      realCoordinates b hi x ∈
        convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
          (U.image b.equivFun : Set (Lattice n))) := by
  rw [← originalRayHull_coordinate_image b hi U]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact (realCoordinates b hi).injective he ▸ hy

include hi in
/-- Terminality retains every original integral point, not a finite test
of a selected box or a replacement lattice. -/
theorem originalRayHull_lattice_points (U : Finset N)
    (h : ∀ y : Lattice n,
      PaperVerification.ToricGeometry.embed n y ∈
        convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
          (U.image b.equivFun : Set (Lattice n))) ↔
        y = 0 ∨ y ∈ U.image b.equivFun) (x : N) :
    ι x ∈ originalRayHull (ι := ι) U ↔ x = 0 ∨ x ∈ U := by
  rw [mem_originalRayHull_iff b hi, realCoordinates_lattice, h]
  constructor
  · rintro (hx | hx)
    · exact Or.inl (b.equivFun.injective (hx.trans (map_zero b.equivFun).symm))
    · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact Or.inr (b.equivFun.injective he ▸ hy)
  · rintro (rfl | hx)
    · exact Or.inl (map_zero b.equivFun)
    · exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- The entire proper-face cone characterization is transported, with no
simpliciality, projectivity or dimension assumption. -/
theorem transportFan_cones_proper_faces
    (Ψ : Fan (Unimodular.FanBridge.standardEmbedding n)) (Q : Set (Ambient n))
    (hΨ : ∀ C, C ∈ Ψ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
      IsExtreme ℝ Q E ∧ E ≠ Q ∧ C = PointedCone.hull ℝ E) :
    ∀ C, C ∈ (transportFan b hi Ψ).cones ↔ ∃ E : Set V, Convex ℝ E ∧
      IsExtreme ℝ ((realCoordinates b hi).symm '' Q) E ∧
      E ≠ (realCoordinates b hi).symm '' Q ∧ C = PointedCone.hull ℝ E := by
  intro C
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨E, hconv, hext, hne, rfl⟩ := (hΨ D).mp hD
    refine ⟨(realCoordinates b hi).symm '' E,
      hconv.linear_image (realCoordinates b hi).symm.toLinearMap,
      isExtreme_image_linearEquiv (realCoordinates b hi).symm hext, ?_, ?_⟩
    · intro h
      apply hne
      have hh := congrArg (fun S => realCoordinates b hi '' S) h
      simpa only [image_inverse_image] using hh
    · exact pointedHull_map_linearEquiv (realCoordinates b hi).symm E
  · rintro ⟨E, hconv, hext, hne, rfl⟩
    have hext' : IsExtreme ℝ Q (realCoordinates b hi '' E) := by
      have h := isExtreme_image_linearEquiv (realCoordinates b hi) hext
      simpa only [image_inverse_image] using h
    have hne' : realCoordinates b hi '' E ≠ Q := by
      intro h
      apply hne
      have hh := congrArg (fun S => (realCoordinates b hi).symm '' S) h
      simpa only [inverse_image_image] using hh
    refine ⟨PointedCone.hull ℝ (realCoordinates b hi '' E),
      (hΨ _).mpr ⟨realCoordinates b hi '' E,
        hconv.linear_image (realCoordinates b hi).toLinearMap, hext', hne', rfl⟩, ?_⟩
    change (PointedCone.hull ℝ (realCoordinates b hi '' E)).map
      (realCoordinates b hi).symm.toLinearMap = PointedCone.hull ℝ E
    rw [pointedHull_map_linearEquiv, inverse_image_image]

/-- Consequently the transported canonical seed is precisely the face
fan of the literal original ray hull. -/
theorem transported_seed_cones
    (U : Finset N) (Ψ : Fan (Unimodular.FanBridge.standardEmbedding n))
    (hΨ : ∀ C, C ∈ Ψ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
      IsExtreme ℝ (convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n)))) E ∧
      E ≠ convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n))) ∧ C = PointedCone.hull ℝ E) :
    ∀ C, C ∈ (transportFan b hi Ψ).cones ↔ ∃ E : Set V, Convex ℝ E ∧
      IsExtreme ℝ (originalRayHull (ι := ι) U) E ∧
      E ≠ originalRayHull (ι := ι) U ∧ C = PointedCone.hull ℝ E := by
  have h := transportFan_cones_proper_faces b hi Ψ _ hΨ
  rw [coordinateRayHull_inverse_image] at h
  exact h

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalRayHull_lattice_points
#print axioms PaperVerification.OriginalLatticeCharts.transported_seed_cones
