module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! # Faithful scalar extension of integral incidence maps

The standard Mathlib base-change theorem for integer-valued coordinate families
proves injectivity after extension to the reals. Arbitrary finite vertex sets,
including disconnected incidence graphs, are allowed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace Unimodular.CycleBounds
variable {n : ℕ} {V : Type*} [Finite V]

/-- Extend an integer-coordinate linear map to real coordinates. -/
def realExtension (f : (Fin n → ℤ) →ₗ[ℤ] (V → ℤ)) :
    (Fin n → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Fintype.linearCombination ℝ (fun i a ↦ (f (Pi.basisFun ℤ (Fin n) i) a : ℝ))

/-- The extension agrees with the original map on every lattice point. -/
theorem realExtension_intCast (f : (Fin n → ℤ) →ₗ[ℤ] (V → ℤ)) (z : Fin n → ℤ) :
    realExtension f (fun i ↦ (z i : ℝ)) = fun a ↦ (f z a : ℝ) := by
  classical
  have hz : f z = ∑ i, z i • f (Pi.basisFun ℤ (Fin n) i) := by
    calc
      f z = f (∑ i, z i • Pi.basisFun ℤ (Fin n) i) := by
        congr 1
        simpa using ((Pi.basisFun ℤ (Fin n)).sum_repr z).symm
      _ = _ := by simp only [map_sum, map_smul]
  ext a
  simp [realExtension, Fintype.linearCombination_apply, hz, Finset.sum_apply]

/-- Integral injectivity remains injectivity over the reals, by the actual
base-change theorem rather than an assumed determinant or rank comparison. -/
theorem realExtension_injective (f : (Fin n → ℤ) →ₗ[ℤ] (V → ℤ))
    (hf : Function.Injective f) : Function.Injective (realExtension f) := by
  have hi : LinearIndependent ℤ (fun i ↦ f (Pi.basisFun ℤ (Fin n) i)) :=
    (Pi.basisFun ℤ (Fin n)).linearIndependent.map_injOn f hf.injOn
  have hreal : LinearIndependent ℝ
      (fun i a ↦ (f (Pi.basisFun ℤ (Fin n) i) a : ℝ)) := by
    simpa [Function.comp_def] using
      (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)).mpr hi
  exact hreal.fintypeLinearCombination_injective

#print axioms realExtension_intCast
#print axioms realExtension_injective
end Unimodular.CycleBounds
