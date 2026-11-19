module

public import ToricPower.GeometricCore
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # Factorial coordinate rings for every regular cone

The complementary coordinates of a smooth affine chart are Laurent variables.
This proof does not enlarge the fan or choose a full-dimensional cone of it.
Consequently it applies to noncomplete fans and to all their lower-dimensional
cones. This source remains development work until its compiler record succeeds.
-/

@[expose] public noncomputable section

namespace ToricPower

open TauCeti.Toric

/-- Separate the first integral coordinate from the remaining coordinates. -/
def intFinSuccCoordinates (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  right_inv p := by
    rcases p with ⟨a, f⟩
    simp
  map_add' f g := rfl

/-- Adjoining the next invertible variable is an ordinary Laurent extension. -/
def laurentFinSuccRingEquiv (R : Type*) [CommRing R] (n : ℕ) :
    AddMonoidAlgebra R (Fin (n + 1) → ℤ) ≃+*
      LaurentPolynomial (AddMonoidAlgebra R (Fin n → ℤ)) :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (intFinSuccCoordinates n)).trans
    AddMonoidAlgebra.curryRingEquiv

/-- A finite iterated Laurent polynomial ring over a UFD is a UFD. -/
theorem laurentFin_uniqueFactorization (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (n : ℕ) :
    UniqueFactorizationMonoid (AddMonoidAlgebra R (Fin n → ℤ)) := by
  induction n with
  | zero =>
      exact (AddMonoidAlgebra.uniqueRingEquiv (R := R) (Fin 0 → ℤ)).symm.toMulEquiv
        |>.uniqueFactorizationMonoid inferInstance
  | succ n ih =>
      letI := ih
      let S := AddMonoidAlgebra R (Fin n → ℤ)
      letI : UniqueFactorizationMonoid (LaurentPolynomial S) :=
        UniqueFactorizationMonoid.of_isLocalization
          (Submonoid.powers (Polynomial.X : Polynomial S)) (LaurentPolynomial S)
      exact (laurentFinSuccRingEquiv R n).symm.toMulEquiv
        |>.uniqueFactorizationMonoid inferInstance

/-- Finitely supported integral coordinates give the same Laurent ring. -/
theorem laurentFinsuppFin_uniqueFactorization (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (n : ℕ) :
    UniqueFactorizationMonoid (AddMonoidAlgebra R (Fin n →₀ ℤ)) := by
  letI := laurentFin_uniqueFactorization R n
  exact (AddMonoidAlgebra.mapDomainRingEquiv R
    (Finsupp.linearEquivFunOnFinite ℕ ℤ (Fin n)).toAddEquiv).symm.toMulEquiv
      |>.uniqueFactorizationMonoid inferInstance

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- The coordinate ring of a regular cone is a polynomial ring over the
Laurent ring of the complementary lattice coordinates. -/
def regularAffinePolynomialLaurentEquiv (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) :
    affineCoordinateRing hi σ ≃+*
      MvPolynomial (ToricRay σ)
        (AddMonoidAlgebra ℂ
          (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)) →₀ ℤ)) :=
  (AddMonoidAlgebra.toMultiplicative ℂ (dualSemigroup hi σ)).symm.trans
    ((AddMonoidAlgebra.mapDomainRingEquiv ℂ
      (hσ.nonempty_dualSemigroup_addEquiv hi).some).trans
      AddMonoidAlgebra.curryRingEquiv)

/-- Smoothness alone makes every affine toric coordinate ring factorial. -/
theorem regular_affineCoordinateRing_uniqueFactorization (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) : UniqueFactorizationMonoid (affineCoordinateRing hi σ) := by
  letI := laurentFinsuppFin_uniqueFactorization ℂ
    (Module.finrank ℤ N - Nat.card (ToricRay σ))
  exact (regularAffinePolynomialLaurentEquiv hi hσ).symm.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

end ToricPower
