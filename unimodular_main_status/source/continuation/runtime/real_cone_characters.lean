module

public import Continuation.Runtime.SmoothChartPrimeCoordinates

/-!
# Real cones from the original character inequalities

A real cocharacter belongs to the cone on a subset of a dual lattice
basis exactly when it is nonnegative on every regular character of the
corresponding coordinate chart. Both signs of every Laurent direction
are present, so the omitted dual coordinates are forced to be zero.
The equivalence holds for all real vectors, not only rational ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ}

/-- Pair the original integral characters with an arbitrary real
cocharacter, using the fixed ambient lattice pairing. -/
def latticeRealWeight (x : Ambient n) : Lattice n →+ ℝ :=
  (dotProductEquiv ℝ (Fin n) x).toAddMonoidHom.comp (embed n)

@[simp] theorem latticeRealWeight_apply (x : Ambient n) (m : Lattice n) :
    latticeRealWeight x m = ∑ i, x i * (m i : ℝ) := rfl

theorem latticeRealWeight_basis (x : Ambient n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    latticeRealWeight x (b i) =
      (integralBasisReal (integralDualBasis b)).repr x i := by
  rw [integralDualBasis_real_repr, integralBasisReal_apply]
  rfl

/-- In a free coordinate both a basis character and its inverse are
regular in the actual coordinate-cone monoid. -/
theorem neg_basis_mem_coordinateConeMonoid
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (i : Fin n) (hi : i ∉ I) : -b i ∈ coordinateConeMonoid b I := by
  intro j hj
  have hij : i ≠ j := by
    rintro rfl
    exact hi hj
  simp [hij]

/-- The real cone and the nonnegativity conditions on every original
regular character are exactly equivalent, including lower-dimensional
cones with nontrivial torus factors. -/
theorem mem_dualBasisCone_iff_nonnegative_characters
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient n) :
    x ∈ latticeRayCone (I.image (integralDualBasis b)) ↔
      ∀ m ∈ coordinateConeMonoid b I, 0 ≤ latticeRealWeight x m := by
  rw [mem_latticeRayCone_basis_iff]
  constructor
  · rintro ⟨hpos, hzero⟩ m hm
    rw [← b.sum_repr m, map_sum]
    apply Finset.sum_nonneg
    intro i hi
    rw [map_zsmul, zsmul_eq_mul, latticeRealWeight_basis]
    by_cases hiI : i ∈ I
    · exact mul_nonneg (by exact_mod_cast hm i hiI) (hpos i)
    · rw [hzero i hiI, mul_zero]
  · intro h
    have hpos (i : Fin n) :
        0 ≤ (integralBasisReal (integralDualBasis b)).repr x i := by
      rw [← latticeRealWeight_basis]
      exact h (b i) (basis_mem_coordinateConeMonoid b I i)
    refine ⟨hpos, ?_⟩
    intro i hi
    apply le_antisymm _ (hpos i)
    have hneg := h (-b i) (neg_basis_mem_coordinateConeMonoid b I i hi)
    rw [map_neg, latticeRealWeight_basis, neg_nonneg] at hneg
    exact hneg

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.mem_dualBasisCone_iff_nonnegative_characters
