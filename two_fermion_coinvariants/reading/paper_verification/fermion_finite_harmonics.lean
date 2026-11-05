module

public import PaperVerification.FermionCreators

/-!
# Finite moment equations and polynomial exterior currents

The polynomial-current formulation used by the creation and Gauss identities
is exactly the finite moment formulation of the paper.  The proof applies over
every commutative coefficient ring and includes repeated moment parameters.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)
variable (φ β a c : Fin n → R)

local notation "E" => ExteriorAlgebra R V

theorem thetaCurrent_apply_eq_polynomial_moment (p : Polynomial R) (w : E) :
    thetaCurrent b φ c p w =
      ∑ i, p.eval (φ i) • (c i • annihilation (b.coord (.inl i)) w) := by
  rw [thetaCurrent_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_smul, mul_comm]

theorem xiCurrent_apply_eq_polynomial_moment (p : Polynomial R) (w : E) :
    xiCurrent b φ β a p w =
      ∑ i, p.eval (φ i) • ((β i * a i) • annihilation (b.coord (.inr i)) w) := by
  rw [xiCurrent_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_smul, mul_comm]

theorem mixedCurrent_apply_eq_polynomial_moment (p : Polynomial R) (w : E) :
    mixedCurrent b φ p w = ∑ i, p.eval (φ i) • pairLower b i w := by
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply]

theorem thetaCurrent_zero_iff_first (w : E) :
    (∀ p : Polynomial R, thetaCurrent b φ c p w = 0) ↔
      ∀ j : Fin n, thetaCurrent b φ c (Polynomial.X ^ (j : ℕ)) w = 0 := by
  simp only [thetaCurrent_apply_eq_polynomial_moment, Polynomial.eval_pow,
    Polynomial.eval_X]
  exact polynomial_moment_zero_iff_first φ
    (fun i ↦ c i • annihilation (b.coord (.inl i)) w)

theorem xiCurrent_zero_iff_first (w : E) :
    (∀ p : Polynomial R, xiCurrent b φ β a p w = 0) ↔
      ∀ j : Fin n, xiCurrent b φ β a (Polynomial.X ^ (j : ℕ)) w = 0 := by
  simp only [xiCurrent_apply_eq_polynomial_moment, Polynomial.eval_pow,
    Polynomial.eval_X]
  exact polynomial_moment_zero_iff_first φ
    (fun i ↦ (β i * a i) • annihilation (b.coord (.inr i)) w)

theorem mixedCurrent_zero_iff_first (w : E) :
    (∀ p : Polynomial R, mixedCurrent b φ p w = 0) ↔
      ∀ j : Fin n, mixedCurrent b φ (Polynomial.X ^ (j : ℕ)) w = 0 := by
  simp only [mixedCurrent_apply_eq_polynomial_moment, Polynomial.eval_pow,
    Polynomial.eval_X]
  exact polynomial_moment_zero_iff_first φ (fun i ↦ pairLower b i w)

/-- Literal finite simultaneous kernel, with the paper's complete range
`0, …, n - 1` for every odd and mixed moment family. -/
def IsFiniteHarmonic (w : E) : Prop :=
  (∀ j : Fin n, thetaCurrent b φ c (Polynomial.X ^ (j : ℕ)) w = 0) ∧
  (∀ j : Fin n, xiCurrent b φ β a (Polynomial.X ^ (j : ℕ)) w = 0) ∧
  ∀ j : Fin n, mixedCurrent b φ (Polynomial.X ^ (j : ℕ)) w = 0

/-- Polynomial indexing introduces no additional hypothesis into the harmonic
construction or the prefix identities. -/
theorem isHarmonic_iff_finite (w : E) :
    IsHarmonic b φ β a c w ↔ IsFiniteHarmonic b φ β a c w := by
  unfold IsHarmonic IsFiniteHarmonic
  rw [thetaCurrent_zero_iff_first, xiCurrent_zero_iff_first,
    mixedCurrent_zero_iff_first]

end PaperVerification.Fermion.Exterior
