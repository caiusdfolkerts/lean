module

public import ToricPower.DivisorWeightMonomialMaps

/-!
# The arithmetic divisor-class quotient and actual Cartier sheaves

Equality modulo integral characters gives an explicit isomorphism of the
actual invariant Cartier sheaves, by multiplication by that character.
The finite residue family in the geometric splitting has exactly the
arithmetic class set `frobeniusClasses`.  Neither assertion requires an
identification of the entire Picard group or a uniqueness theorem for
decompositions into summands.

Development source: compilation of the current source is required before
any theorem here is reported as verified.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open scoped BigOperators

namespace ToricPower

universe u v w

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- A principal difference gives the actual isomorphism of divisor sheaves.
The forward map is multiplication by χᵐ and its inverse by χ⁻ᵐ. -/
def toricInvariantCartierSheafIso_of_principal (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (m : N →+ ℤ)
    (principal : ∀ ρ, b ρ - c ρ = m (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf ≅
      (invariantCartierDivisor fan nonempty regular c).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  have forward : ∀ ρ, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ) := by
    intro ρ
    rw [← principal ρ]
    omega
  have backward : ∀ ρ, 0 ≤ b ρ - c ρ + (-m) (fanRayPrimitiveGenerator fan ρ) := by
    intro ρ
    simp only [AddMonoidHom.neg_apply]
    rw [← principal ρ]
    omega
  exact {
    hom := toricCartierMonomialMap fan nonempty regular b c m forward
    inv := toricCartierMonomialMap fan nonempty regular c b (-m) backward
    hom_inv_id := by
      rw [toricCartierMonomialMap_comp]
      simpa only [add_neg_cancel] using toricCartierMonomialMap_id fan nonempty regular b
    inv_hom_id := by
      rw [toricCartierMonomialMap_comp]
      simpa only [neg_add_cancel] using toricCartierMonomialMap_id fan nonempty regular c }

section CharacterCoordinates

variable {κ : Type w} [Fintype κ]

/-- The global ray matrix in an arbitrary integral character basis. -/
def fanCharacterRayMatrix (fan : Fan i) (basis : Module.Basis κ ℤ (N →+ ℤ)) :
    fan.Ray → κ → ℤ :=
  fun ρ j => basis j (fanRayPrimitiveGenerator fan ρ)

theorem fanCharacterRayMatrix_symm_apply (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (u : κ → ℤ) (ρ : fan.Ray) :
    rayMap (fanCharacterRayMatrix fan basis) u ρ =
      basis.equivFun.symm u (fanRayPrimitiveGenerator fan ρ) := by
  simp [fanCharacterRayMatrix, rayMap, Module.Basis.equivFun_symm_apply,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm]

@[simp] theorem fanCharacterRayMatrix_apply (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (m : N →+ ℤ) (ρ : fan.Ray) :
    rayMap (fanCharacterRayMatrix fan basis) (basis.equivFun m) ρ =
      m (fanRayPrimitiveGenerator fan ρ) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    fanCharacterRayMatrix_symm_apply fan basis (basis.equivFun m) ρ

/-- Equality in the literal integral cokernel induces an isomorphism of
the actual sheaves, including any torsion in that cokernel. -/
def toricInvariantCartierSheafIso_of_class_eq (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b c : fan.Ray → ℤ)
    (same : divisorClass (fanCharacterRayMatrix fan basis) b =
      divisorClass (fanCharacterRayMatrix fan basis) c) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf ≅
      (invariantCartierDivisor fan nonempty regular c).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  have difference : b - c ∈ LinearMap.range (rayMap (fanCharacterRayMatrix fan basis)) :=
    (Submodule.Quotient.eq _).mp same
  let u := Classical.choose difference
  have hu := Classical.choose_spec difference
  refine toricInvariantCartierSheafIso_of_principal fan nonempty regular b c
    (basis.equivFun.symm u) ?_
  intro ρ
  rw [← fanCharacterRayMatrix_symm_apply]
  exact (congrFun hu ρ).symm

/-- The geometric residue divisor and the arithmetic floor vector agree
coordinate by coordinate, before passing to any quotient. -/
theorem toricResidueCoefficients_eq_powerCoefficient (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (u : κ → ℤ) :
    toricResidueCoefficients fan b ell (basis.equivFun.symm u) =
      powerCoefficient (fanCharacterRayMatrix fan basis) b (ell : ℤ) u := by
  funext ρ
  simp only [toricResidueCoefficients, powerCoefficient,
    fanCharacterRayMatrix_symm_apply]

end CharacterCoordinates

section FiniteResidueClasses

variable {ι : Type v} {κ : Type w} [Fintype κ]

/-- The full integral class set is exactly the class range of the finite
half-open residue cube used in the actual splitting. -/
theorem frobeniusClasses_eq_finiteResidueRange (A : ι → κ → ℤ)
    (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    frobeniusClasses A b (ell : ℤ) =
      Set.range (fun residue : LatticeResidues κ ell =>
        divisorClass A (powerCoefficient A b (ell : ℤ)
          (latticeResidueRepresentative residue))) := by
  ext a
  constructor
  · intro member
    obtain ⟨u, bounded, represents⟩ :=
      (frobeniusClasses_iff_bounded A b (ell : ℤ) (by exact_mod_cast hell) a).mp member
    let residue : LatticeResidues κ ell := fun j =>
      ⟨(u j).toNat, by have h := bounded j; omega⟩
    have representative : latticeResidueRepresentative residue = u := by
      funext j
      change ((u j).toNat : ℤ) = u j
      exact Int.toNat_of_nonneg (bounded j).1
    refine ⟨residue, ?_⟩
    exact (congrArg (fun u => divisorClass A (powerCoefficient A b (ell : ℤ) u))
      representative).trans represents
  · rintro ⟨residue, rfl⟩
    exact ⟨latticeResidueRepresentative residue, rfl⟩

/-- Equality of arithmetic class sets is equality of the class ranges of
the actual, finite residue-indexed coefficient families. -/
theorem finiteResidueClassRanges_eq_of_frobeniusClasses_eq (A : ι → κ → ℤ)
    (b c : ι → ℤ) (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k)
    (same : frobeniusClasses A b (ell : ℤ) = frobeniusClasses A c (k : ℤ)) :
    Set.range (fun residue : LatticeResidues κ ell =>
      divisorClass A (powerCoefficient A b (ell : ℤ)
        (latticeResidueRepresentative residue))) =
    Set.range (fun residue : LatticeResidues κ k =>
      divisorClass A (powerCoefficient A c (k : ℤ)
        (latticeResidueRepresentative residue))) := by
  rw [← frobeniusClasses_eq_finiteResidueRange A b ell hell,
    ← frobeniusClasses_eq_finiteResidueRange A c k hk]
  exact same

end FiniteResidueClasses

section GeometricResidueClasses

variable {κ : Type u} [Fintype κ]

theorem toricResidueClassRange (fan : Fan i)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) :
    Set.range (fun residue : LatticeResidues κ ell =>
      divisorClass (fanCharacterRayMatrix fan basis)
        (toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue)))) =
      frobeniusClasses (fanCharacterRayMatrix fan basis) b (ell : ℤ) := by
  simp only [toricResidueCoefficients_eq_powerCoefficient]
  exact (frobeniusClasses_eq_finiteResidueRange _ b ell hell).symm

/-- Every class-set member is realized by an actual residue summand
isomorphic to the invariant Cartier sheaf with that coefficient vector. -/
theorem toricResidueSheaf_exists_iso_of_class_mem (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b c : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell)
    (member : divisorClass (fanCharacterRayMatrix fan basis) c ∈
      frobeniusClasses (fanCharacterRayMatrix fan basis) b (ell : ℤ)) :
    letI := toricSchemeIntegral fan nonempty
    ∃ residue : LatticeResidues κ ell,
      Nonempty ((invariantCartierDivisor fan nonempty regular c).sheaf ≅
        toricResidueSheafFamily fan nonempty regular basis b ell residue) := by
  letI := toricSchemeIntegral fan nonempty
  rw [← toricResidueClassRange fan basis b ell hell] at member
  obtain ⟨residue, same⟩ := member
  refine ⟨residue, ⟨?_⟩⟩
  exact toricInvariantCartierSheafIso_of_class_eq fan nonempty regular basis c _ same.symm

end GeometricResidueClasses

section EnumeratedRays

variable {s n : ℕ}

/-- The literal finite matrix to which the effective arithmetic endpoints
apply, for an explicit enumeration of rays and an integral character basis. -/
def enumeratedFanRayMatrix (fan : Fan i) (rays : Fin s ≃ fan.Ray)
    (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) : Matrix (Fin s) (Fin n) ℤ :=
  fun ρ j => basis j (fanRayPrimitiveGenerator fan (rays ρ))

theorem enumeratedFanRayMatrix_symm_apply (fan : Fan i)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
    (u : Fin n → ℤ) (ρ : Fin s) :
    rayMap (enumeratedFanRayMatrix fan rays basis) u ρ =
      basis.equivFun.symm u (fanRayPrimitiveGenerator fan (rays ρ)) := by
  exact fanCharacterRayMatrix_symm_apply fan basis u (rays ρ)

/-- Equal classes for the exact finite ray matrix induce actual sheaf
isomorphisms after transporting the coefficient vectors along the enumeration. -/
def toricInvariantCartierSheafIso_of_enumerated_class_eq (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
    (b c : Fin s → ℤ)
    (same : divisorClass (enumeratedFanRayMatrix fan rays basis) b =
      divisorClass (enumeratedFanRayMatrix fan rays basis) c) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular (b ∘ rays.symm)).sheaf ≅
      (invariantCartierDivisor fan nonempty regular (c ∘ rays.symm)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  have difference : b - c ∈ LinearMap.range
      (rayMap (enumeratedFanRayMatrix fan rays basis)) :=
    (Submodule.Quotient.eq _).mp same
  let u := Classical.choose difference
  have hu := Classical.choose_spec difference
  refine toricInvariantCartierSheafIso_of_principal fan nonempty regular
    (b ∘ rays.symm) (c ∘ rays.symm) (basis.equivFun.symm u) ?_
  intro ρ
  have h := congrFun hu (rays.symm ρ)
  rw [enumeratedFanRayMatrix_symm_apply] at h
  simpa only [Function.comp_apply, Pi.sub_apply, Equiv.apply_symm_apply] using h.symm

variable {κ : Type u} [Fintype κ]

/-- Reindexing the basis and coordinates leaves the actual character
unchanged. This also handles a lattice living in a larger universe. -/
theorem characterBasis_reindex_symm_apply
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (coordinates : Fin n ≃ κ) (u : κ → ℤ) :
    (basis.reindex coordinates.symm).equivFun.symm (u ∘ coordinates) =
      basis.equivFun.symm u := by
  apply (basis.reindex coordinates.symm).equivFun.injective
  funext j
  simp only [LinearEquiv.apply_symm_apply, Function.comp_apply,
    Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/-- The actual ray coefficients in a geometric residue summand, expressed
in the finite row and column enumerations used by the arithmetic theorem. -/
theorem toricResidueCoefficients_enumerated (fan : Fan i)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ)
    (residue : LatticeResidues κ ell) :
    (toricResidueCoefficients fan b ell
      (basis.equivFun.symm (latticeResidueRepresentative residue))) ∘ rays =
    powerCoefficient (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
      (b ∘ rays) (ell : ℤ) (latticeResidueRepresentative (residue ∘ coordinates)) := by
  funext ρ
  change (b (rays ρ) + basis.equivFun.symm (latticeResidueRepresentative residue)
      (fanRayPrimitiveGenerator fan (rays ρ))) / (ell : ℤ) = _
  rw [powerCoefficient, enumeratedFanRayMatrix_symm_apply]
  change _ = (b (rays ρ) + (basis.reindex coordinates.symm).equivFun.symm
    (latticeResidueRepresentative residue ∘ coordinates)
      (fanRayPrimitiveGenerator fan (rays ρ))) / (ell : ℤ)
  rw [characterBasis_reindex_symm_apply]

/-- The class range of the genuine finite geometric family is exactly the
class set for the explicit finite matrix, with no loss of torus coordinates. -/
theorem toricResidueClassRange_enumerated (fan : Fan i)
    (rays : Fin s ≃ fan.Ray) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (coordinates : Fin n ≃ κ) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) :
    Set.range (fun residue : LatticeResidues κ ell =>
      divisorClass (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        ((toricResidueCoefficients fan b ell
          (basis.equivFun.symm (latticeResidueRepresentative residue))) ∘ rays)) =
      frobeniusClasses
        (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))
        (b ∘ rays) (ell : ℤ) := by
  rw [frobeniusClasses_eq_finiteResidueRange _ _ ell hell]
  ext a
  constructor
  · rintro ⟨residue, rfl⟩
    refine ⟨residue ∘ coordinates, ?_⟩
    exact congrArg (divisorClass
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm)))
      (toricResidueCoefficients_enumerated fan rays basis coordinates b ell residue).symm
  · rintro ⟨residue, rfl⟩
    refine ⟨residue ∘ coordinates.symm, ?_⟩
    have hcoeff := toricResidueCoefficients_enumerated fan rays basis coordinates b ell
      (residue ∘ coordinates.symm)
    have reindexed : (residue ∘ coordinates.symm) ∘ coordinates = residue := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [reindexed] at hcoeff
    exact congrArg (divisorClass
      (enumeratedFanRayMatrix fan rays (basis.reindex coordinates.symm))) hcoeff

end EnumeratedRays

end ToricPower
