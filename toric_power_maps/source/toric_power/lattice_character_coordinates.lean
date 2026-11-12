module

public import ToricPower.IntegralDualLattice
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Genuine real coordinates of the full character lattice

An integral basis of characters gives a real linear equivalence with
the full dual space. Its dual is the actual normal-coordinate equivalence;
neither map passes to a finite-index lattice or a subspace of the dual.
-/

@[expose] public noncomputable section

open TauCeti.Toric Module

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (lattice : IsIntegralLattice i)
  {n : ℕ} (basis : Basis (Fin n) ℤ (N →+ ℤ))

/-- Real coordinates in the actual basis of extended integral characters. -/
def characterCoordinateEquiv : (Fin n → ℝ) ≃ₗ[ℝ] Module.Dual ℝ V :=
  ((integralLattice_realCharacter lattice).isBaseChange.basis basis).equivFun.symm

theorem characterCoordinateEquiv_apply (x : Fin n → ℝ) :
    characterCoordinateEquiv lattice basis x =
      ∑ j, x j • lattice.realCharacter (basis j) := by
  rw [characterCoordinateEquiv, Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (integralLattice_realCharacter lattice).isBaseChange.basis_apply basis j

theorem characterCoordinateEquiv_lattice (x : Fin n → ℝ) (v : N) :
    characterCoordinateEquiv lattice basis x (i v) =
      ∑ j, x j * (basis j v : ℝ) := by
  rw [characterCoordinateEquiv_apply]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
    IsIntegralLattice.realCharacter_apply]

/-- Evaluation duality transports actual normal vectors into the
dual of character-coordinate space. -/
def normalCoordinateEquiv : V ≃ₗ[ℝ] Module.Dual ℝ (Fin n → ℝ) := by
  letI := lattice.finiteDimensional
  exact (Module.evalEquiv ℝ V).trans (characterCoordinateEquiv lattice basis).dualMap

theorem normalCoordinateEquiv_apply (v : V) (x : Fin n → ℝ) :
    normalCoordinateEquiv lattice basis v x =
      characterCoordinateEquiv lattice basis x v := rfl

theorem normalCoordinateEquiv_lattice (v : N) (x : Fin n → ℝ) :
    normalCoordinateEquiv lattice basis (i v) x =
      ∑ j, x j * (basis j v : ℝ) :=
  characterCoordinateEquiv_lattice lattice basis x v

end ToricPower

end
