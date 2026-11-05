module

public import PaperVerification.FermionQuotientFactor
public import PaperVerification.FermionFrobeniusExterior
public import PaperVerification.FermionHarmonicGrading
public import PaperVerification.FermionFiniteHarmonics

/-!
# The dual of the literal paired quotient injects into actual harmonics

The scalar quotient factor map is surjective. Pulling back a functional and
using the genuine ordinary/exterior Frobenius pairing gives its unique
exterior representative. The defining two-sided relations force precisely
the finite odd and mixed kernels, hence all polynomial current equations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators
open Exterior

variable {K : Type*} [Field K] {n : ℕ} [LinearOrder (OddIndex n)]
variable (β : Fin n → K) (φ a c : Fin n → PolynomialRing K n)
variable (J : Ideal (PolynomialRing K n))

local notation "A" => PolynomialRing K n ⧸ J
local notation "E" => ExteriorAlgebra A (OddModule A n)
local notation "Q" => PairedQuotient β φ a c

def pairedQuotientDualToExterior
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) : Module.Dual K Q →ₗ[K] E :=
  (exteriorFrobeniusDual (Pi.basisFun A (OddIndex n)) ε hε).symm.toLinearMap.comp
    (superQuotientFactor (pairedIdeal β φ a c) J hJ).toLinearMap.dualMap

theorem pairedQuotientDualToExterior_representation
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) (f : Module.Dual K Q) (x : E) :
    ε (coefficientPairing (Pi.basisFun A (OddIndex n)) x
      (pairedQuotientDualToExterior β φ a c J hJ ε hε f)) =
      f (superQuotientFactor (pairedIdeal β φ a c) J hJ x) := by
  exact exteriorFrobeniusDual_symm_apply (Pi.basisFun A (OddIndex n)) ε hε _ x

theorem pairedQuotientDualToExterior_injective
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) :
    Function.Injective (pairedQuotientDualToExterior β φ a c J hJ ε hε) := by
  apply (exteriorFrobeniusDual (Pi.basisFun A (OddIndex n)) ε hε).symm.injective.comp
  exact LinearMap.dualMap_injective_of_surjective
    (superQuotientFactor_surjective (pairedIdeal β φ a c) J hJ)

theorem pairedQuotientDualToExterior_current_zero
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0)
    (f : Module.Dual K Q) (z : E) (l : Module.End A E)
    (hz : superQuotientFactor (pairedIdeal β φ a c) J hJ z = 0)
    (hadjoint : ∀ x w : E,
      coefficientPairing (Pi.basisFun A (OddIndex n)) (z * x) w =
        coefficientPairing (Pi.basisFun A (OddIndex n)) x (l w)) :
    l (pairedQuotientDualToExterior β φ a c J hJ ε hε f) = 0 := by
  apply exteriorFrobeniusPairing_separatingRight (Pi.basisFun A (OddIndex n)) ε hε
  intro x
  change ε (coefficientPairing (Pi.basisFun A (OddIndex n)) x
    (l (pairedQuotientDualToExterior β φ a c J hJ ε hε f))) = 0
  rw [← hadjoint, pairedQuotientDualToExterior_representation,
    map_mul, hz, zero_mul, map_zero]

/-- Every represented quotient functional lies in the literal simultaneous
kernel of all polynomial odd and mixed currents. -/
theorem pairedQuotientDualToExterior_harmonic
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) (f : Module.Dual K Q) :
    IsHarmonic (Pi.basisFun A (OddIndex n))
      (fun i ↦ Ideal.Quotient.mk J (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ Ideal.Quotient.mk J (a i)) (fun i ↦ Ideal.Quotient.mk J (c i))
      (pairedQuotientDualToExterior β φ a c J hJ ε hε f) := by
  let q := Ideal.Quotient.mkₐ K J
  let b := Pi.basisFun A (OddIndex n)
  apply (isHarmonic_iff_finite b _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j
    apply pairedQuotientDualToExterior_current_zero β φ a c J hJ ε hε f
      (thetaRelation b (fun i ↦ q (φ i)) (fun i ↦ q (c i)) (Polynomial.X ^ (j : ℕ)))
      (thetaCurrent b (fun i ↦ q (φ i)) (fun i ↦ q (c i)) (Polynomial.X ^ (j : ℕ)))
    · rw [← superSpecialization_paired_theta q β φ a c j, superQuotientFactor_apply]
      apply (pairedIdeal β φ a c).ringCon.eq.mpr
      exact TwoSidedIdeal.subset_span ⟨(.theta, (j : ℕ)), rfl⟩
    · exact thetaRelation_adjoint b _ _ _
  · intro j
    apply pairedQuotientDualToExterior_current_zero β φ a c J hJ ε hε f
      (xiRelation b (fun i ↦ q (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun i ↦ q (a i)) (Polynomial.X ^ (j : ℕ)))
      (xiCurrent b (fun i ↦ q (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun i ↦ q (a i)) (Polynomial.X ^ (j : ℕ)))
    · rw [← superSpecialization_paired_xi q β φ a c j, superQuotientFactor_apply]
      apply (pairedIdeal β φ a c).ringCon.eq.mpr
      exact TwoSidedIdeal.subset_span ⟨(.xi, (j : ℕ)), rfl⟩
    · exact xiRelation_adjoint b _ _ _ _
  · intro j
    apply pairedQuotientDualToExterior_current_zero β φ a c J hJ ε hε f
      (mixedRelation b (fun i ↦ q (φ i)) (Polynomial.X ^ (j : ℕ)))
      (mixedCurrent b (fun i ↦ q (φ i)) (Polynomial.X ^ (j : ℕ)))
    · rw [← superSpecialization_paired_mixed q β φ a c j, superQuotientFactor_apply]
      apply (pairedIdeal β φ a c).ringCon.eq.mpr
      exact TwoSidedIdeal.subset_span ⟨(.mixed, (j : ℕ)), rfl⟩
    · exact mixedRelation_adjoint b _ _

def pairedQuotientDualToHarmonics
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) : Module.Dual K Q →ₗ[K]
    (harmonicSubmodule (Pi.basisFun A (OddIndex n))
      (fun i ↦ Ideal.Quotient.mk J (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ Ideal.Quotient.mk J (a i)) (fun i ↦ Ideal.Quotient.mk J (c i))).restrictScalars K :=
  (pairedQuotientDualToExterior β φ a c J hJ ε hε).codRestrict _
    (pairedQuotientDualToExterior_harmonic β φ a c J hJ ε hε)

theorem pairedQuotientDualToHarmonics_injective
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) :
    Function.Injective (pairedQuotientDualToHarmonics β φ a c J hJ ε hε) := by
  intro f g hfg
  apply pairedQuotientDualToExterior_injective β φ a c J hJ ε hε
  exact congrArg Subtype.val hfg

/-- The literal paired quotient has dimension at most the actual harmonic
space. Its finiteness is derived from the surjective scalar-quotient factor
map, rather than included as a separate premise. -/
theorem pairedQuotient_finrank_le_harmonics
    [Module.Finite K (PolynomialRing K n ⧸ J)]
    (hJ : ∀ p ∈ J,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ pairedIdeal β φ a c)
    (ε : A →ₗ[K] K) (hε : ∀ x : A, (∀ y : A, ε (x * y) = 0) → x = 0) :
    Module.finrank K Q ≤ Module.finrank K
      ((harmonicSubmodule (Pi.basisFun A (OddIndex n))
        (fun i ↦ Ideal.Quotient.mk J (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun i ↦ Ideal.Quotient.mk J (a i)) (fun i ↦ Ideal.Quotient.mk J (c i))).restrictScalars K) := by
  letI : Module.Finite A E := Module.Finite.of_basis (Pi.basisFun A (OddIndex n)).ExteriorAlgebra
  letI : Module.Finite K E := Module.Finite.trans A E
  letI : Module.Finite K Q := Module.Finite.of_surjective
    (superQuotientFactor (pairedIdeal β φ a c) J hJ).toLinearMap
    (superQuotientFactor_surjective (pairedIdeal β φ a c) J hJ)
  have hh := LinearMap.finrank_le_finrank_of_injective
    (pairedQuotientDualToHarmonics_injective β φ a c J hJ ε hε)
  simpa only [Subspace.dual_finrank_eq] using hh

end PaperVerification.Fermion
