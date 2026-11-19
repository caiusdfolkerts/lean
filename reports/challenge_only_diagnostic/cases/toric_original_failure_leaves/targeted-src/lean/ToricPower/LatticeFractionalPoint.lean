module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import TauCeti.Algebra.Module.Primitive
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Integral points in a fundamental parallelepiped

A real basis consisting of lattice vectors fails to generate the entire
integer lattice precisely when its half-open fundamental parallelepiped
contains a nonzero lattice point. Subtracting the integer parts of the
coordinates constructs that point directly. Passing to its primitive
generator preserves the strict coordinate bounds needed for stellar
subdivision.
-/

@[expose] public noncomputable section
open TauCeti.Toric

namespace ToricPower.FanSubdivision

variable {N V κ : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} [Fintype κ]

/-- Subtracting integral coordinate floors gives a nonzero lattice point
in the half-open fundamental parallelepiped of any nonspanning integral
family which is a basis over the reals. -/
theorem exists_nonzero_integral_fractional_coordinates
    (realBasis : Module.Basis κ ℝ V) (vectors : κ → N)
    (image : ∀ k, realBasis k = i (vectors k))
    (notSpanning : Submodule.span ℤ (Set.range vectors) ≠ ⊤) :
    ∃ q : N, q ≠ 0 ∧ ∀ k,
      0 ≤ realBasis.repr (i q) k ∧ realBasis.repr (i q) k < 1 := by
  classical
  obtain ⟨n, outside⟩ : ∃ n : N, n ∉ Submodule.span ℤ (Set.range vectors) := by
    by_contra all
    push_neg at all
    exact notSpanning (top_unique fun n _ => all n)
  let correction : N := ∑ k, ⌊realBasis.repr (i n) k⌋ • vectors k
  have correction_mem : correction ∈ Submodule.span ℤ (Set.range vectors) := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have imageCorrection : i correction =
      ∑ k, (⌊realBasis.repr (i n) k⌋ : ℝ) • realBasis k := by
    simp only [correction, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro k _
    rw [image k]
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  refine ⟨n - correction, ?_, ?_⟩
  · intro zero
    exact outside ((sub_eq_zero.mp zero).symm ▸ correction_mem)
  · intro k
    have coordinate : realBasis.repr (i (n-correction)) k =
        Int.fract (realBasis.repr (i n) k) := by
      simp only [map_sub, Finsupp.sub_apply, imageCorrection,
        realBasis.repr_sum_self, Int.fract]
    rw [coordinate]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Primitive reduction of an integral fractional point does not enlarge
any nonnegative coordinate. No finite-index computation is needed. -/
theorem exists_primitive_integral_fractional_coordinates
    (lattice : IsIntegralLattice i) (realBasis : Module.Basis κ ℝ V)
    (vectors : κ → N) (image : ∀ k, realBasis k = i (vectors k))
    (notSpanning : Submodule.span ℤ (Set.range vectors) ≠ ⊤) :
    ∃ q : N, TauCeti.IsPrimitive q ∧ q ≠ 0 ∧ ∀ k,
      0 ≤ realBasis.repr (i q) k ∧ realBasis.repr (i q) k < 1 := by
  letI := lattice.free
  obtain ⟨v, nonzero, coordinates⟩ :=
    exists_nonzero_integral_fractional_coordinates realBasis vectors image notSpanning
  obtain ⟨d, q, positive, primitive, equation⟩ :=
    TauCeti.exists_eq_zsmul_isPrimitive nonzero
  refine ⟨q, primitive, primitive.ne_zero, ?_⟩
  intro k
  have value : realBasis.repr (i v) k = (d : ℝ) * realBasis.repr (i q) k := by
    rw [equation, map_zsmul, map_zsmul]
    simp only [Finsupp.smul_apply, zsmul_eq_mul]
  have positiveReal : (0 : ℝ) < d := by exact_mod_cast positive
  have atLeastOne : (1 : ℝ) ≤ d := by exact_mod_cast positive
  have nonnegative := (mul_nonneg_iff_of_pos_left positiveReal).mp
    (value ▸ (coordinates k).1)
  refine ⟨nonnegative, ?_⟩
  have bound := (coordinates k).2
  rw [value] at bound
  exact lt_of_le_of_lt (by nlinarith) bound

end ToricPower.FanSubdivision
end
