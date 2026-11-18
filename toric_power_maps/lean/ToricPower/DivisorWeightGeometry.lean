module

public import ToricPower.DivisorWeightFaces
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Identification with actual affine toric charts

An integral basis of the character lattice converts the intrinsic ray pairings
to the integer matrix used in the divisor-module calculation.  The resulting
coordinate ring isomorphism is proved from the dual-semigroup criterion.  On a
regular cone, every coefficient vector has a Cartier character, including cones
of dimension smaller than the rank of the lattice.
-/

@[expose] public noncomputable section

namespace ToricPower

open TauCeti.Toric MonoidAlgebra
open scoped BigOperators

variable {N V κ : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} [Fintype κ]

/-- Characters are determined freely by their values on an integral lattice
basis; this constructs their coordinates without assuming an extra basis. -/
def latticeCharacterCoordinates (basis : Module.Basis κ ℤ N) :
    (N →+ ℤ) ≃+ (κ → ℤ) where
  toFun m := fun j => m (basis j)
  invFun u := (basis.constr ℤ u).toAddMonoidHom
  left_inv m := by
    apply AddMonoidHom.toIntLinearMap_injective
    apply basis.ext
    intro j
    exact basis.constr_basis ℤ (fun k => m (basis k)) j
  right_inv u := by
    funext j
    exact basis.constr_basis ℤ u j
  map_add' _ _ := rfl

def characterBasisOfLatticeBasis (basis : Module.Basis κ ℤ N) :
    Module.Basis κ ℤ (N →+ ℤ) :=
  (Pi.basisFun ℤ κ).map (latticeCharacterCoordinates basis).symm.toIntLinearEquiv

/-- Every lattice in the actual toric development supplies a finite integral
character basis, so coordinate choice adds no hypothesis to the chart result. -/
def latticeCharacterBasis (hi : IsIntegralLattice i) :
    Module.Basis (Fin (Module.finrank ℤ N)) ℤ (N →+ ℤ) := by
  letI := hi.free
  letI := hi.finite
  exact characterBasisOfLatticeBasis (Module.finBasis ℤ N)

def characterRayMatrix (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) : ToricRay σ → κ → ℤ :=
  fun ρ j => basis j (primitiveGenerator hi hσ ρ)

theorem characterRayMatrix_symm_apply (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (u : κ → ℤ) (ρ : ToricRay σ) :
    rayMap (characterRayMatrix hi hσ basis) u ρ =
      basis.equivFun.symm u (primitiveGenerator hi hσ ρ) := by
  simp [characterRayMatrix, rayMap, Module.Basis.equivFun_symm_apply,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm]

@[simp] theorem characterRayMatrix_apply (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (m : N →+ ℤ) (ρ : ToricRay σ) :
    rayMap (characterRayMatrix hi hσ basis) (basis.equivFun m) ρ =
      m (primitiveGenerator hi hσ ρ) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    characterRayMatrix_symm_apply hi hσ basis (basis.equivFun m) ρ

/-- The actual dual semigroup is the nonnegative ray-weight monoid in lattice
coordinates.  The proof uses the generating-ray theorem for toric cones. -/
def dualSemigroupRayCoordinates (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) :
    dualSemigroup hi σ ≃+ rayWeightMonoid (characterRayMatrix hi hσ basis) where
  toFun m := ⟨basis.equivFun m.1, by
    intro ρ
    rw [characterRayMatrix_apply]
    exact (mem_dualSemigroup_iff_primitiveGenerator hi hσ m.1).mp m.2 ρ⟩
  invFun u := ⟨basis.equivFun.symm u.1, by
    rw [mem_dualSemigroup_iff_primitiveGenerator hi hσ]
    intro ρ
    rw [← characterRayMatrix_symm_apply hi hσ basis u.1 ρ]
    exact u.2 ρ⟩
  left_inv m := by
    apply Subtype.ext
    exact basis.equivFun.symm_apply_apply m.1
  right_inv u := by
    apply Subtype.ext
    exact basis.equivFun.apply_symm_apply u.1
  map_add' m n := by
    apply Subtype.ext
    exact basis.equivFun.map_add m.1 n.1

/-- The module calculation uses the actual affine toric coordinate ring, up to
this explicitly proved change of lattice coordinates. -/
def affineToricRayChartRingEquiv (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) :
    affineCoordinateRing hi σ ≃+* RayChartRing ℂ (characterRayMatrix hi hσ basis) :=
  mapDomainRingEquiv ℂ (dualSemigroupRayCoordinates hi hσ basis).toMultiplicative

@[simp] theorem affineToricRayChartRingEquiv_single (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (m : dualSemigroup hi σ) (z : ℂ) :
    affineToricRayChartRingEquiv hi hσ basis (single (Multiplicative.ofAdd m) z) =
      single (Multiplicative.ofAdd (dualSemigroupRayCoordinates hi hσ basis m)) z := by
  simp [affineToricRayChartRingEquiv]

/-- The intrinsic admissible characters of an invariant divisor on a toric
chart. -/
abbrev ToricDivisorWeight (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (b : ToricRay σ → ℤ) :=
  {m : N →+ ℤ // ∀ ρ, 0 ≤ b ρ + m (primitiveGenerator hi hσ ρ)}

def toricDivisorWeightCoordinates (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : ToricRay σ → ℤ) :
    ToricDivisorWeight hi hσ b ≃ DivisorWeight (characterRayMatrix hi hσ basis) b where
  toFun m := ⟨basis.equivFun m.1, by
    intro ρ
    simpa only [characterRayMatrix_apply] using m.2 ρ⟩
  invFun u := ⟨basis.equivFun.symm u.1, by
    intro ρ
    rw [← characterRayMatrix_symm_apply hi hσ basis u.1 ρ]
    exact u.2 ρ⟩
  left_inv m := by
    apply Subtype.ext
    exact basis.equivFun.symm_apply_apply m.1
  right_inv u := by
    apply Subtype.ext
    exact basis.equivFun.apply_symm_apply u.1

/-- Every ray coefficient vector on a smooth cone has an integral local Cartier
character.  The complementary lattice coordinates are assigned zero. -/
theorem regularCone_exists_divisorCharacter (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (b : ToricRay σ → ℤ) :
    ∃ q : N →+ ℤ, ∀ ρ, q (primitiveGenerator hi hσ.toIsToricCone ρ) = b ρ := by
  obtain ⟨l, e, he⟩ := hσ.exists_basis_sum
  let q : N →+ ℤ := (e.constr ℤ (Sum.elim b (fun _ : Fin l => 0))).toAddMonoidHom
  refine ⟨q, fun ρ => ?_⟩
  rw [← (he ρ).eq_primitiveGenerator hi hσ.toIsToricCone]
  simp [q]

/-- Local Cartier solvability in the coordinates of any chosen character basis. -/
theorem regularCone_rayMap_surjective (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (basis : Module.Basis κ ℤ (N →+ ℤ)) :
    Function.Surjective (rayMap (characterRayMatrix hi hσ.toIsToricCone basis)) := by
  intro b
  obtain ⟨q, hq⟩ := regularCone_exists_divisorCharacter hi hσ b
  refine ⟨basis.equivFun q, ?_⟩
  funext ρ
  rw [characterRayMatrix_apply, hq]

/-- Every invariant divisor module on a regular cone is genuinely free of rank
one over its chart coordinate ring. -/
def regularConeDivisorTrivialization (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : ToricRay σ → ℤ) :
    RayChartRing ℂ (characterRayMatrix hi hσ.toIsToricCone basis) ≃ₗ[
      RayChartRing ℂ (characterRayMatrix hi hσ.toIsToricCone basis)]
      DivisorSectionModule ℂ (characterRayMatrix hi hσ.toIsToricCone basis) b 1 := by
  let hq := regularCone_rayMap_surjective hi hσ basis b
  exact divisorCartierTrivialization ℂ _ b (Classical.choose hq) (Classical.choose_spec hq).symm

end ToricPower
