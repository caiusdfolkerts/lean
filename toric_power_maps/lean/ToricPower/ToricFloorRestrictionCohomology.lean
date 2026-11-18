module

public import ToricPower.ToricActualRestrictionCohomology
public import ToricPower.ToricFiniteCohomologyPatterns

/-!
# Vanishing survives every actual floor-residue restriction

If a negative-ray pattern occurs for the floor divisor
`floor((b + u(v))/ell)` at character `m`, exactly the same pattern occurs
for `b` at `u + ell • m`. Consequently, actual total nonvanishing of any
floor summand on any rational subspace implies nonvanishing of the
original line there. Equivalently, vanishing of the original restriction
kills every residue summand. The proof uses the literal pullback cohomology
and the full character lattices; it does not assume a finite base-change
or translation theorem for subtorus inclusions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.FiniteNegativePatterns
namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Integer floor division by a positive number preserves the exact
strict-negative pattern after the corresponding integral translation. -/
theorem floor_add_negative_iff (a translation denominator : ℤ) (positive : 0 < denominator) :
    a / denominator + translation < 0 ↔ a + denominator * translation < 0 := by
  have nonnegative := Int.ediv_nonneg_iff_of_pos
    (a := a + denominator * translation) positive
  rw [Int.add_mul_ediv_left a translation positive.ne'] at nonnegative
  simpa only [not_le] using not_congr nonnegative

/-- Exact equality of the finite negative sets, retaining the complete
integral characters rather than restricting them to any bounded region. -/
theorem toricFloorNegativePattern_eq (fan : Fan i) (b : fan.Ray → ℤ)
    (character weight : N →+ ℤ) (ell : ℕ) (positive : 0 < ell) :
    negativeSet (toricPatternValues fan
      (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ)) weight) =
    negativeSet (toricPatternValues fan b (character + (ell : ℤ) • weight)) := by
  ext ray
  rw [mem_negativeSet, mem_negativeSet]
  simpa only [toricPatternValues, AddMonoidHom.add_apply, AddMonoidHom.smul_apply,
    zsmul_eq_mul, Int.cast_natCast, add_assoc] using
    floor_add_negative_iff
      (b (toricFiniteRayEquiv fan ray) +
        character (fanRayPrimitiveGenerator fan (toricFiniteRayEquiv fan ray)))
      (weight (fanRayPrimitiveGenerator fan (toricFiniteRayEquiv fan ray)))
      (ell : ℤ) (by exact_mod_cast positive)

/-- Every successful finite pattern for a floor divisor is a successful
finite pattern for the original divisor. -/
theorem toricFlooredPatternCriterion_imp (fan : Fan i) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) (ell : ℕ) (positive : 0 < ell) :
    toricFiniteCohomologyPatternCriterion fan
      (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ)) →
      toricFiniteCohomologyPatternCriterion fan b := by
  rintro ⟨negative, finite, topological, feasible⟩
  refine ⟨negative, finite, topological, ?_⟩
  obtain ⟨weight, same⟩ := (latticeFeasible_iff _ negative).mp feasible
  apply (latticeFeasible_iff (toricPatternValues fan b) negative).mpr
  refine ⟨character + (ell : ℤ) • weight, ?_⟩
  exact (toricFloorNegativePattern_eq fan b character weight ell positive).symm.trans same

/-- Actual total cohomological nonvanishing of a floor divisor implies
actual total nonvanishing of the original divisor. -/
theorem toricFlooredCohomology_nonzero_imp (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) (ell : ℕ) (positive : 0 < ell) :
    (∃ degree, Nontrivial (invariantDivisorCohomology fan nonempty regular
      (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ)) degree)) →
    ∃ degree, Nontrivial (invariantDivisorCohomology fan nonempty regular b degree) := by
  intro nonzero
  apply (toricCartierCohomology_nonzero_iff_finitePattern fan nonempty regular b).mpr
  apply toricFlooredPatternCriterion_imp fan b character ell positive
  exact (toricCartierCohomology_nonzero_iff_finitePattern fan nonempty regular _).mp nonzero

/-- The same implication holds for the literal original-sheaf pullbacks
on every rational subspace, including noncomplete restrictions. -/
theorem toricFlooredSubspacePullback_nonzero_imp (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) (ell : ℕ) (positive : 0 < ell)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular
        (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ))).sheaf
      W hW degree)) →
    ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W hW degree) := by
  letI := toricSchemeIntegral fan nonempty
  let restrictedCharacter := character.comp (latticeTrace i W).subtype.toAddMonoidHom
  have coefficients : restrictedFanRayCoefficients fan W hW
      (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ)) =
    fun ray => (restrictedFanRayCoefficients fan W hW b ray +
      restrictedCharacter (fanRayPrimitiveGenerator (restrictedFan fan W hW) ray)) / (ell : ℤ) := by
    funext ray
    change (b _ + character (fanRayPrimitiveGenerator fan _)) / (ell : ℤ) =
      (b _ + character (fanRayPrimitiveGenerator (restrictedFan fan W hW) ray).val) / (ell : ℤ)
    rw [restrictedFan_primitive_value]
  intro nonzero
  have invariantNonzero :=
    (toricSubspacePullback_nonzero_iff_invariant fan nonempty regular W hW _).mp nonzero
  rw [coefficients] at invariantNonzero
  exact (toricSubspacePullback_nonzero_iff_invariant fan nonempty regular W hW b).mpr
    (toricFlooredCohomology_nonzero_imp (restrictedFan fan W hW)
      (restrictedFan_cones_nonempty fan nonempty W hW)
      (restrictedFan_isRegular fan regular W hW) (restrictedFanRayCoefficients fan W hW b)
      restrictedCharacter ell positive invariantNonzero)

/-- In the vanishing form used for the actual residue decomposition,
vanishing of the original restriction kills every floor summand in every
cohomological degree. -/
theorem toricFlooredSubspacePullback_subsingleton (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) (ell : ℕ) (positive : 0 < ell)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    letI := toricSchemeIntegral fan nonempty
    (∀ degree, Subsingleton (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W hW degree)) →
    ∀ degree, Subsingleton (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular
        (fun ray => (b ray + character (fanRayPrimitiveGenerator fan ray)) / (ell : ℤ))).sheaf
      W hW degree) := by
  letI := toricSchemeIntegral fan nonempty
  intro vanishes degree
  apply not_nontrivial_iff_subsingleton.mp
  intro nonzero
  obtain ⟨originalDegree, originalNonzero⟩ :=
    toricFlooredSubspacePullback_nonzero_imp fan nonempty regular b character ell positive W hW
      ⟨degree, nonzero⟩
  exact not_nontrivial_iff_subsingleton.mpr (vanishes originalDegree) originalNonzero

end ToricPower
