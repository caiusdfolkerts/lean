module

public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Transporting a determinant factor through a perfect pairing

This elementary comparison records the exponent needed in relative
projective-line duality. A residue pairing of multiplier `δ⁻¹`, compared
with a degree-`d` binary pairing of multiplier `δ^d`, produces the multiplier
`δ^(-(d+1))`. The two pairings and the changes of frame remain explicit.
The geometric residue identity is a separate theorem, not an assumption
hidden in a definition of cohomology.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.PerfectPairingCovariance

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- Compare two actual perfect pairings with the same target dual. -/
def comparison (B : V ≃ₗ[R] Module.Dual R V)
    (C : U ≃ₗ[R] Module.Dual R V) : U ≃ₗ[R] V :=
  C.trans B.symm

/-- The two covariance laws determine the exact determinant exponent of the
comparison. The statement holds over every commutative coefficient ring. -/
theorem comparison_covariant
    (B : V ≃ₗ[R] Module.Dual R V) (C : U ≃ₗ[R] Module.Dual R V)
    (gV : V ≃ₗ[R] V) (gU : U →ₗ[R] U) (δ : Rˣ) (d : ℕ)
    (hB : ∀ x y, B (gV x) (gV y) = (δ : R)^d * B x y)
    (hC : ∀ x y, C (gU x) (gV y) = (↑(δ⁻¹) : R) * C x y)
    (x : U) :
    comparison B C (gU x) =
      (↑(δ⁻¹) : R)^(d+1) • gV (comparison B C x) := by
  apply B.injective
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := gV.surjective y
  simp only [comparison, LinearEquiv.trans_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, LinearEquiv.apply_symm_apply]
  rw [hC, hB, LinearEquiv.apply_symm_apply]
  have hscalar : (↑(δ⁻¹) : R)^(d+1) * (δ : R)^d = (↑(δ⁻¹) : R) := by
    rw [pow_succ', mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  rw [← mul_assoc, hscalar]

end PaperVerification.PerfectPairingCovariance
