module

public import PaperVerification.ExteriorQuadraticDifferential
public import PaperVerification.ExteriorTwoFormEvaluation
public import Mathlib.Algebra.Lie.Basic

/-!
# The intrinsic Chevalley--Eilenberg exterior differential

For a finite-dimensional Lie algebra, the Chevalley--Eilenberg differential
is the odd derivation of the exterior algebra on its dual whose value on a
one-cochain is the negative bracket dual.  The predicate below spells out
that definition using the actual exterior pairing.  The uniqueness theorem
is proved from nondegeneracy of that pairing, not assumed.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.ChevalleyEilenbergExterior

open ExteriorQuadraticDifferential

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L]

/-- The intrinsic defining property of the ordinary CE exterior differential.
The quadratic value is an actual second exterior power of the dual. -/
def IsDifferential (D : Module.End K (ExteriorAlgebra K (Module.Dual K L))) : Prop :=
  IsOddDerivation D ∧ ∀ α : Module.Dual K L,
    ∃ ω : ⋀[K]^2 (Module.Dual K L),
      D (ExteriorAlgebra.ι K α) = (ω : ExteriorAlgebra K (Module.Dual K L)) ∧
      ∀ x y : L, exteriorPower.pairingDual K L 2 ω
        (exteriorPower.ιMulti K 2 ![x,y]) = -α ⁅x,y⁆

/-- The intrinsic defining equations specify a unique actual operator. -/
theorem differential_unique
    {D E : Module.End K (ExteriorAlgebra K (Module.Dual K L))}
    (hD : IsDifferential D) (hE : IsDifferential E) : D = E := by
  apply oddDerivation_ext hD.1 hE.1
  intro α
  obtain ⟨ω,hω,hωeval⟩ := hD.2 α
  obtain ⟨η,hη,hηeval⟩ := hE.2 α
  have heq : ω = η := ExteriorTwoFormEvaluation.pairingDual_injective_on_pairs ω η
    (fun x y ↦ (hωeval x y).trans (hηeval x y).symm)
  rw [hω,hη,heq]

end PaperVerification.ChevalleyEilenbergExterior
