module

public import Continuation.Geometry.OriginalLatticeConvexity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-! # Interior and extreme points in the original ambient space -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical

namespace PaperVerification.OriginalLatticeCharts

/-- The extreme-point set itself is transported exactly. -/
theorem extremePoints_image_linearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (Q : Set A) :
    e '' Q.extremePoints ℝ = (e '' Q).extremePoints ℝ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := isExtreme_image_linearEquiv e (isExtreme_singleton.mpr hx)
    rw [Set.image_singleton] at h
    exact isExtreme_singleton.mp h
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := isExtreme_image_linearEquiv e.symm (isExtreme_singleton.mpr hy)
    have hQ : e.symm '' (e '' Q) = Q := e.toEquiv.symm_image_image Q
    rw [hQ, Set.image_singleton, LinearEquiv.symm_apply_apply] at h
    exact ⟨x, isExtreme_singleton.mp h, rfl⟩

universe u v

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

include hi in
theorem originalRayHull_extremePoints (U : Finset N)
    (h : (convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n)))).extremePoints ℝ =
      PaperVerification.ToricGeometry.embed n '' (U.image b.equivFun : Set (Lattice n))) :
    (originalRayHull (ι := ι) U).extremePoints ℝ = ι '' (U : Set N) := by
  apply Set.image_injective.mpr (realCoordinates b hi).injective
  rw [extremePoints_image_linearEquiv, originalRayHull_coordinate_image, h]
  rw [Finset.coe_image]
  simp only [Set.image_image]
  apply congrArg (fun f : N → Ambient n => f '' (U : Set N))
  funext x
  exact (realCoordinates_lattice b hi x).symm

section Interior

variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {j : N →+ W} (hj : IsIntegralLattice j)

include hj in
/-- Zero is an interior point in the actual original finite-dimensional
real space. Continuity follows from the scalar-extended finite basis. -/
theorem originalRayHull_zero_interior (U : Finset N)
    (h : (0 : Ambient n) ∈ interior
      (convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n))))) :
    (0 : W) ∈ interior (originalRayHull (ι := j) U) := by
  letI : FiniteDimensional ℝ W := Module.Finite.of_basis (hj.isBaseChange.basis b)
  let e := (realCoordinates b hj).toContinuousLinearEquiv
  have himage := e.toHomeomorph.image_interior (originalRayHull (ι := j) U)
  change realCoordinates b hj '' interior (originalRayHull (ι := j) U) =
    interior (realCoordinates b hj '' originalRayHull (ι := j) U) at himage
  rw [originalRayHull_coordinate_image] at himage
  have hm : (0 : Ambient n) ∈
      realCoordinates b hj '' interior (originalRayHull (ι := j) U) := himage.symm ▸ h
  obtain ⟨x, hx, he⟩ := hm
  have hx0 : x = 0 := (realCoordinates b hj).injective
    (he.trans (map_zero (realCoordinates b hj)).symm)
  exact hx0 ▸ hx

end Interior

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalRayHull_extremePoints
#print axioms PaperVerification.OriginalLatticeCharts.originalRayHull_zero_interior
