module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The actual lattice of integral characters in the real dual

Real extension identifies the character lattice with an integral lattice
in the real dual space. This is stronger than injectivity and is the
discreteness statement needed for finite sets of cohomology weights.
-/

@[expose] public noncomputable section

open TauCeti.Toric
open scoped TensorProduct

namespace ToricPower

variable {N V V' : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup V'] [Module ℝ V'] {i : N →+ V}

theorem integralLattice_postcompose_equiv (lattice : IsIntegralLattice i)
    (equivalence : V ≃ₗ[ℝ] V') :
    IsIntegralLattice (equivalence.toAddMonoidHom.comp i) := by
  refine ⟨lattice.free, lattice.finite, ?_⟩
  apply IsBaseChange.of_equiv (lattice.isBaseChange.equiv.trans equivalence)
  intro n
  change equivalence (lattice.isBaseChange.equiv (1 ⊗ₜ[ℤ] n)) = equivalence (i n)
  rw [IsBaseChange.equiv_tmul, one_smul]
  simp only [AddMonoidHom.coe_toIntLinearMap]

/-- The dual base-change theorem is applied to the entire integral
character module, with no finite-index replacement. -/
theorem integralLattice_realCharacter (lattice : IsIntegralLattice i) :
    IsIntegralLattice lattice.realCharacter := by
  letI := lattice.free
  letI := lattice.finite
  let equivalence : (N →+ ℤ) ≃ₗ[ℤ] Module.Dual ℤ N := addMonoidHomLequivInt ℤ
  refine ⟨Module.Free.of_equiv equivalence.symm,
    Module.Finite.equiv equivalence.symm, ?_⟩
  have maps : lattice.realCharacter.toIntLinearMap =
      lattice.isBaseChange.toDual.comp equivalence.toLinearMap := by
    apply LinearMap.ext
    intro m
    apply lattice.isBaseChange.algHom_ext
    intro n
    change lattice.realCharacter m (i n) = lattice.isBaseChange.toDual (m.toIntLinearMap) (i n)
    rw [lattice.realCharacter_apply]
    simpa only [AddMonoidHom.coe_toIntLinearMap, algebraMap_int_eq, Int.coe_castRingHom] using
      (lattice.isBaseChange.toDual_comp_apply m.toIntLinearMap n).symm
  rw [maps]
  exact IsBaseChange.comp_equiv equivalence _ lattice.isBaseChange.dual

section ContinuousDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {embedding : N →+ E}

/-- The same real character as an actual continuous linear functional. -/
def integralContinuousCharacter (lattice : IsIntegralLattice embedding) :
    (N →+ ℤ) →+ (E →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toAddMonoidHom.comp
    lattice.realCharacter

@[simp]
theorem integralContinuousCharacter_apply (lattice : IsIntegralLattice embedding)
    (m : N →+ ℤ) (x : E) :
    integralContinuousCharacter lattice m x = lattice.realCharacter m x := rfl

@[simp]
theorem integralContinuousCharacter_lattice_apply (lattice : IsIntegralLattice embedding)
    (m : N →+ ℤ) (n : N) :
    integralContinuousCharacter lattice m (embedding n) = (m n : ℝ) :=
  lattice.realCharacter_apply m n

theorem integralContinuousCharacter_isIntegralLattice (lattice : IsIntegralLattice embedding) :
    IsIntegralLattice (integralContinuousCharacter lattice) :=
  integralLattice_postcompose_equiv (integralLattice_realCharacter lattice)
    LinearMap.toContinuousLinearMap

end ContinuousDual
end ToricPower
