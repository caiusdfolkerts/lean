module

public import Continuation.Geometry.OriginalLatticeConvexity

@[expose] public section

/-!
# Reflexivity in the literal original dual lattice

Integral characters are the actual additive homomorphisms N → ℤ. Their
real extensions are compared with dual-basis coordinates. The complete
polar, including every real functional, is transported to the coordinate
polar. A coordinate lattice-polytope certificate therefore gives an
actual lattice polytope in the original dual lattice.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical BigOperators

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

/-- Coordinates on the full real algebraic dual, in the dual of the same
scalar-extended integral basis. -/
def realCharacterCoordinates : Module.Dual ℝ V ≃ₗ[ℝ] Ambient n :=
  (hi.isBaseChange.basis b).dualBasis.equivFun

/-- The actual original dual-lattice embedding is preserved. -/
theorem realCharacterCoordinates_lattice (m : N →+ ℤ) :
    realCharacterCoordinates b hi (hi.realCharacter m) =
      PaperVerification.ToricGeometry.embed n (characterCoordinates b m) := by
  ext i
  change (hi.isBaseChange.basis b).dualBasis.equivFun (hi.realCharacter m) i =
    (characterCoordinates b m i : ℝ)
  rw [Module.Basis.dualBasis_equivFun, hi.isBaseChange.basis_apply b i]
  change (hi.realCharacter m) (ι (b i)) = (characterCoordinates b m i : ℝ)
  rw [hi.realCharacter_apply, characterCoordinates_apply]

/-- Evaluation is the original real pairing, not an independently chosen
bilinear form or a change of the dual lattice. -/
theorem realCharacterCoordinates_pairing (m : Module.Dual ℝ V) (x : V) :
    (∑ i : Fin n, realCoordinates b hi x i * realCharacterCoordinates b hi m i) = m x := by
  change (∑ i : Fin n, (hi.isBaseChange.basis b).equivFun x i *
    (hi.isBaseChange.basis b).dualBasis.equivFun m i) = m x
  simp only [Module.Basis.dualBasis_equivFun, Module.Basis.equivFun_apply]
  have h := congrArg m ((hi.isBaseChange.basis b).sum_repr x)
  simpa only [map_sum, map_smul, smul_eq_mul] using h

/-- The ordinary polar in the original real dual space. -/
def originalDualPolar (Q : Set V) : Set (Module.Dual ℝ V) :=
  {m | ∀ x ∈ Q, m x ≤ 1}

/-- The ordinary dot-product coordinate polar. -/
def coordinateDualPolar (Q : Set (Ambient n)) : Set (Ambient n) :=
  {m | ∀ x ∈ Q, (∑ i : Fin n, x i * m i) ≤ 1}

/-- Equality of whole polar sets; the quantifier ranges over every real
functional and every real point of the hull. -/
theorem originalDualPolar_coordinate_image (Q : Set V) :
    realCharacterCoordinates b hi '' originalDualPolar Q =
      coordinateDualPolar (realCoordinates b hi '' Q) := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩ x ⟨z, hz, rfl⟩
    rw [realCharacterCoordinates_pairing]
    exact hm z hz
  · intro hy
    refine ⟨(realCharacterCoordinates b hi).symm y, ?_,
      (realCharacterCoordinates b hi).apply_symm_apply y⟩
    intro x hx
    have h := hy (realCoordinates b hi x) ⟨x, hx, rfl⟩
    rw [← realCharacterCoordinates_pairing b hi
      ((realCharacterCoordinates b hi).symm y) x]
    simpa only [LinearEquiv.apply_symm_apply] using h

/-- The original dual polar is a genuine lattice polytope whenever the
coordinate polar is. The vertices are transported by the inverse integral
dual-basis equivalence, not by rational rescaling. -/
theorem originalDualPolar_latticePolytope
    (U : Finset N) (W : Finset (Lattice n))
    (hW : coordinateDualPolar
      (convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n)))) =
      convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (W : Set (Lattice n)))) :
    ∃ W' : Finset (N →+ ℤ),
      originalDualPolar (originalRayHull (ι := ι) U) =
        convexHull ℝ (hi.realCharacter '' (W' : Set (N →+ ℤ))) := by
  let W' := W.image (characterCoordinates b).symm
  refine ⟨W', ?_⟩
  apply Set.image_injective.mpr (realCharacterCoordinates b hi).injective
  rw [originalDualPolar_coordinate_image, originalRayHull_coordinate_image, hW]
  change convexHull ℝ (PaperVerification.ToricGeometry.embed n '' (W : Set (Lattice n))) =
    (realCharacterCoordinates b hi).toLinearMap ''
      convexHull ℝ (hi.realCharacter '' (W' : Set (N →+ ℤ)))
  rw [(realCharacterCoordinates b hi).toLinearMap.image_convexHull]
  have hfun : (fun m : Lattice n => realCharacterCoordinates b hi
      (hi.realCharacter ((characterCoordinates b).symm m))) =
      PaperVerification.ToricGeometry.embed n := by
    funext m
    rw [realCharacterCoordinates_lattice, LinearEquiv.apply_symm_apply]
  have himage : realCharacterCoordinates b hi ''
      (hi.realCharacter '' (W' : Set (N →+ ℤ))) =
      PaperVerification.ToricGeometry.embed n '' (W : Set (Lattice n)) := by
    dsimp only [W']
    rw [Finset.coe_image]
    simp only [Set.image_image]
    rw [hfun]
  change convexHull ℝ (PaperVerification.ToricGeometry.embed n '' (W : Set (Lattice n))) =
    convexHull ℝ (realCharacterCoordinates b hi ''
      (hi.realCharacter '' (W' : Set (N →+ ℤ))))
  rw [himage]

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalDualPolar_coordinate_image
#print axioms PaperVerification.OriginalLatticeCharts.originalDualPolar_latticePolytope
