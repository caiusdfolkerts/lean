module
public import mixed_results.regular_substitution_tor_algebra

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionDerivedTor -/
section

/-! # The derived Tor computed by the regular-substitution Koszul algebras

The multiplicative comparison uses the original polynomial action on `A`
and the right polynomial action on the literal tensor product `A ⊗[SourceRing] TargetRing`.
These statements identify the homologically graded complexes with Mathlib's
actual derived Tor, and identify their differentials with those of the two
Koszul homology algebras. No flatness condition on `A` is required.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg CommAlg.Koszul CategoryTheory MvPolynomial
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
  [Fintype Y] [LinearOrder Y]
  [Algebra (MvPolynomial V K) (MvPolynomial Y K)]
  [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (A : Type u) [CommRing A] [Algebra (MvPolynomial V K) A]
  [Algebra K A] [IsScalarTower K (MvPolynomial V K) A]
local notation "SourceRing" => MvPolynomial V K
local notation "TargetRing" => MvPolynomial Y K
local notation "B" => A ⊗[SourceRing] TargetRing

/-- The target polynomial variables act on the actual right tensor factor. -/
local instance regularTargetPolynomialAlgebra : Algebra TargetRing B :=
  Algebra.TensorProduct.rightAlgebra

/-- The chosen right action agrees with the existing coefficient action. -/
local instance regularTargetPolynomialScalarTower : IsScalarTower K TargetRing B := by
  letI : IsScalarTower SourceRing TargetRing B := Algebra.TensorProduct.right_isScalarTower
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap K B c = algebraMap SourceRing B (algebraMap K SourceRing c) :=
      IsScalarTower.algebraMap_apply K SourceRing B c
    _ = algebraMap TargetRing B (algebraMap SourceRing TargetRing (algebraMap K SourceRing c)) :=
      IsScalarTower.algebraMap_apply SourceRing TargetRing B (algebraMap K SourceRing c)
    _ = algebraMap TargetRing B (algebraMap K TargetRing c) := by
      rw [IsScalarTower.algebraMap_apply K SourceRing TargetRing]

@[simp] theorem regularTargetPolynomialVariable (y : Y) :
    algebraMap TargetRing B (X y) = (1 : A) ⊗ₜ[SourceRing] (X y : TargetRing) := rfl

/-- The source algebra differential is exactly its polynomial-module action. -/
theorem regularSourceDifferential_eq_polynomial :
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun v : V => algebraMap SourceRing A (X v))).d =
        TensorExteriorKoszul.differential (K := K) (R := SourceRing) (M := A)
          (X : V → SourceRing) := by
  exact (TensorExteriorKoszul.differential_algebraMap
    (K := K) (R := SourceRing) (A := A) (X : V → SourceRing)).symm

/-- The target algebra differential is exactly the right polynomial action. -/
theorem regularTargetDifferential_eq_polynomial :
    (TensorExteriorKoszul.parityDifferential (K := K)
      (fun y : Y => (1 : A) ⊗ₜ[SourceRing] (X y : TargetRing))).d =
        TensorExteriorKoszul.differential (K := K) (R := TargetRing) (M := B)
          (X : Y → TargetRing) := by
  exact (TensorExteriorKoszul.differential_algebraMap
    (K := K) (R := TargetRing) (A := B) (X : Y → TargetRing)).symm

/-- The source complex is graded by the actual exterior cardinality. -/
abbrev RegularSourceKoszulComplex :=
  TensorExteriorKoszul.complex (K := K) (M := A) (X : V → SourceRing)

/-- The target complex uses the same literal coefficient tensor product as
`torAlgebraEquiv`. -/
abbrev RegularTargetKoszulComplex :=
  TensorExteriorKoszul.complex (K := K) (M := B) (X : Y → TargetRing)

theorem regularSourceKoszulComplex_differential_val (p : ℕ)
    (z : TensorExteriorKoszul.piece (K := K) (V := V) (M := A) (p + 1)) :
    (TensorExteriorKoszul.pieceDifferential (X : V → SourceRing) p z).val =
      (TensorExteriorKoszul.parityDifferential (K := K)
        (fun v : V => algebraMap SourceRing A (X v))).d z.val := by
  rw [TensorExteriorKoszul.pieceDifferential_val,
    regularSourceDifferential_eq_polynomial]

theorem regularTargetKoszulComplex_differential_val (p : ℕ)
    (z : TensorExteriorKoszul.piece (K := K) (V := Y) (M := B) (p + 1)) :
    (TensorExteriorKoszul.pieceDifferential (X : Y → TargetRing) p z).val =
      (TensorExteriorKoszul.parityDifferential (K := K)
        (fun y : Y => (1 : A) ⊗ₜ[SourceRing] (X y : TargetRing))).d z.val := by
  rw [TensorExteriorKoszul.pieceDifferential_val,
    regularTargetDifferential_eq_polynomial]

/-- Actual derived Tor of the source algebra for the original variable action. -/
def regularSourceDerivedTorIso (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K SourceRing)).obj
      (((Tor (ModuleCat SourceRing) p).obj (ModuleCat.of SourceRing A)).obj
        (residueCoefficientModule (V := V) (k := K))) ≅
      (RegularSourceKoszulComplex (V := V) A).homology p :=
  TensorExteriorKoszul.polynomialTorIso (K := K) (V := V) (M := A) p

/-- Actual derived Tor of the literal substituted coefficient algebra,
with evaluation-at-zero coefficients over the target polynomial ring. -/
def regularTargetDerivedTorIso (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K TargetRing)).obj
      (((Tor (ModuleCat TargetRing) p).obj (ModuleCat.of TargetRing B)).obj
        (residueCoefficientModule (V := Y) (k := K))) ≅
      (RegularTargetKoszulComplex (V := V) (Y := Y) A).homology p :=
  TensorExteriorKoszul.polynomialTorIso (K := K) (V := Y) (M := B) p

end FourPapers.PolynomialRegularSubstitution
end

end
end

end
