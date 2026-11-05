module

public import Continuation.RegularMatroid.AllFieldsClosure
public import Continuation.Fano.SchemeRealizationClasses

/-!
# The Fano realization theorem with all-fields regularity

The regularity convention is connected by a proved equivalence to ordinary
representability over every field. The geometric realization and the minor
both retain all conclusions of the fan-scheme theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

open scoped Matroid

namespace Unimodular.SchemeRealizationClasses

open PaperVerification.ToricGeometry

/-- Corollary 5.2 with the literal all-fields definition of regularity. -/
theorem corollary_5_2_all_fields {E : Type*} (M : Matroid E) [M.Finite]
    (k : Type u) [Field k] :
    RegularRepresentation.RegularOnGround M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
        IsSmoothProjectiveFanoFan F k ∧
        IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays => v.val) ∧
        HasRayMinor M F :=
  (RegularRepresentation.regularOnGround_iff_rationalTU M).trans
    (corollary_5_2 M k)

/-- The stronger divisible and UT-free realization also holds for every
regular matroid in the all-fields convention and every natural `d ≥ 2`. -/
theorem regular_all_fields_exists_uniform_divisible_fan {E : Type*}
    (M : Matroid E) [M.Finite] (hM : RegularRepresentation.RegularOnGround M)
    (k : Type u) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      IsSmoothProjectiveFanoFan F k ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays => v.val) ∧
      HasRayMinor M F ∧ HasAnticanonicalTensorRoot F k d ∧
      AnticanonicalPolytopeUTFree F :=
  regular_exists_uniform_divisible_fan M
    ((RegularRepresentation.regularOnGround_iff_rationalTU M).mp hM) k d hd

end Unimodular.SchemeRealizationClasses

#print axioms Unimodular.SchemeRealizationClasses.corollary_5_2_all_fields
#print axioms Unimodular.SchemeRealizationClasses.regular_all_fields_exists_uniform_divisible_fan
