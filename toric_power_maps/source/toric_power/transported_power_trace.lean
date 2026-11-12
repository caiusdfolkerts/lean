module

public import ToricPower.RegularPowerAdjunction

/-!
# Perfect power traces in arbitrary regular monoid coordinates

Transporting a smooth cone's dual semigroup to polynomial--Laurent
coordinates retains the full residue basis and its multiplication matrix.
This file proves the trace pairing and the actual two-sided scalar-change
adjunction directly for the original monoid algebra.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory ModuleCat MonoidAlgebra Module
open scoped Classical

namespace ToricPower

variable {M : Type*} [AddCommMonoid M] (ell : ℕ) {α β : Type*}
  (positive : 0 < ell) (e : M ≃+ RegularExponents α β)

theorem transportedMonoidDecomposition_residue (u : RegularResidues ell α β) :
    transportedMonoidDecomposition ell positive e (u,1) =
      Multiplicative.ofAdd (e.symm (regularResidueExponent ell α β u)) := by
  rw [transportedMonoidDecomposition_apply, map_one,
    regularMonoidDecomposition_residue]
  rfl

variable (k : Type*) [CommRing k]

local notation "S" => MonoidAlgebra k (Multiplicative M)
local notation "φ" => mapDomainRingHom k (exponentPower ell M)

/-- The literal top coordinate in the transported power-module basis. -/
def transportedPowerTrace :
    letI := (φ).toModule
    Module.Dual S S := by
  letI := (φ).toModule
  exact (transportedPowerBasis k ell positive e).coord (regularTopResidue ell α β positive)

theorem transportedPowerBasis_monomial (u : RegularResidues ell α β) :
    letI := (φ).toModule
    transportedPowerBasis k ell positive e u =
      single (Multiplicative.ofAdd (e.symm (regularResidueExponent ell α β u))) 1 := by
  letI := (φ).toModule
  rw [transportedPowerBasis, monoidDecompositionBasis_apply,
    transportedMonoidDecomposition_residue]

/-- The actual original-coordinate matrix is the same complement permutation. -/
theorem transportedPowerTrace_basis_pairing (u v : RegularResidues ell α β) :
    letI := (φ).toModule
    transportedPowerTrace ell positive e k
        (transportedPowerBasis k ell positive e u * transportedPowerBasis k ell positive e v) =
      if regularComplementResidue ell α β u = v then 1 else 0 := by
  letI := (φ).toModule
  by_cases equal : regularComplementResidue ell α β u = v
  · subst v
    have product : transportedPowerBasis k ell positive e u *
        transportedPowerBasis k ell positive e (regularComplementResidue ell α β u) =
        transportedPowerBasis k ell positive e (regularTopResidue ell α β positive) := by
      rw [transportedPowerBasis_monomial, transportedPowerBasis_monomial,
        transportedPowerBasis_monomial, single_mul_single, mul_one]
      change single (Multiplicative.ofAdd
        (e.symm (regularResidueExponent ell α β u) +
          e.symm (regularResidueExponent ell α β (regularComplementResidue ell α β u)))) 1 = _
      apply congrArg (fun z => single (Multiplicative.ofAdd z) (1 : k))
      rw [← e.symm.map_add, regularResidueExponent_add_complement]
    rw [product]
    simp [transportedPowerTrace, Basis.coord_apply]
  · rw [if_neg equal, transportedPowerBasis_monomial, transportedPowerBasis_monomial,
      single_mul_single, mul_one]
    apply monoidDecompositionBasis_coord_single_of_ne
    intro top
    apply equal
    apply Eq.symm
    apply regular_product_top_residue_implies_complement ell α β positive u v
    change ((regularMonoidDecomposition ell α β positive).symm
      (e.toMultiplicative (Multiplicative.ofAdd
        (e.symm (regularResidueExponent ell α β u) +
          e.symm (regularResidueExponent ell α β v))))).1 = _ at top
    change ((regularMonoidDecomposition ell α β positive).symm
      (Multiplicative.ofAdd (e (e.symm (regularResidueExponent ell α β u) +
        e.symm (regularResidueExponent ell α β v))))).1 = _ at top
    simpa only [map_add, AddEquiv.apply_symm_apply] using top

variable [Fintype α] [Fintype β]

/-- Every regular dual-semigroup chart has a proved perfect trace pairing. -/
theorem transportedPowerTrace_perfect :
    letI : Algebra S S := (φ).toAlgebra
    Function.Bijective (multiplicationTracePairing
      (transportedPowerTrace ell positive e k)) := by
  letI : Algebra S S := (φ).toAlgebra
  let equivalence := multiplicationTraceEquivOfBasis
    (transportedPowerBasis k ell positive e) (regularComplementResidue ell α β)
    (transportedPowerTrace ell positive e k)
    (by
      intro u v
      by_cases equal : regularComplementResidue ell α β u = v
      · simpa only [if_pos equal] using transportedPowerTrace_basis_pairing ell positive e k u v
      · simpa only [if_neg equal] using transportedPowerTrace_basis_pairing ell positive e k u v)
  exact equivalence.bijective

section SameUniverse

universe u

variable {M' : Type u} {α' β' : Type*} [AddCommMonoid M'] [Fintype α'] [Fintype β']
  (k' : Type u) [CommRing k']
  (e' : M' ≃+ RegularExponents α' β')

/-- Extension and coextension are naturally isomorphic on the actual ring. -/
def transportedPowerExtendCoextendIso (positive : 0 < ell) :
    ModuleCat.extendScalars.{u} (mapDomainRingHom k' (exponentPower ell M')) ≅
      ModuleCat.coextendScalars (mapDomainRingHom k' (exponentPower ell M')) := by
  let R := MonoidAlgebra k' (Multiplicative M')
  let power := mapDomainRingHom k' (exponentPower ell M')
  letI : Algebra R R := power.toAlgebra
  letI : Module R R := power.toModule
  letI : Module.Finite R R := Module.Finite.of_basis (transportedPowerBasis k' ell positive e')
  letI : Module.Free R R := Module.Free.of_basis (transportedPowerBasis k' ell positive e')
  exact traceExtendCoextendIso (transportedPowerTrace ell positive e' k')
    (transportedPowerTrace_perfect ell positive e' k')

/-- Finite-duality adjunction in the original affine coordinate ring. -/
def transportedPowerRestrictExtendAdjunction (positive : 0 < ell) :
    ModuleCat.restrictScalars.{u} (mapDomainRingHom k' (exponentPower ell M')) ⊣
      ModuleCat.extendScalars (mapDomainRingHom k' (exponentPower ell M')) :=
  (ModuleCat.restrictCoextendScalarsAdj _).ofNatIsoRight
    (transportedPowerExtendCoextendIso ell k' e' positive).symm

end SameUniverse

end ToricPower

end
