module

public import PaperVerification.ExteriorQuadraticDifferential
public import PaperVerification.TwoCentralExteriorDecomposition
public import PaperVerification.AlternatingFormsExteriorCentrality
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The central exterior differential in Koszul coordinates

The four-term exterior decomposition sends the literal operator
`f · contraction₀ + g · contraction₁` to the length-two Koszul differential.
The two coefficients are the original exterior two-forms, with their
original multiplication maps.  This is an equality of actual linear maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoCentralKoszulOperator

open TwoCentralExteriorDecomposition

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The original forms, included in the actual enlarged exterior algebra. -/
def operator (f g : ⋀[R]^2 M) : Module.End R (E R (N R M)) :=
  ExteriorQuadraticDifferential.differential
    (lift (f : E R M)) (lift (g : E R M)) (coordinate 0) (coordinate 1)

/-- The original first Koszul differential. -/
def first (f g : ⋀[R]^2 M) : (E R M × E R M) →ₗ[R] E R M :=
  (LinearMap.mulLeft R (f : E R M)).coprod (LinearMap.mulLeft R (g : E R M))

/-- The original second Koszul differential, with its usual sign. -/
def second (f g : ⋀[R]^2 M) : E R M →ₗ[R] (E R M × E R M) :=
  (-(LinearMap.mulLeft R (g : E R M))).prod (LinearMap.mulLeft R (f : E R M))

/-- Inclusion preserves the genuine quadratic degree and hence centrality. -/
theorem lift_twoForm_commute (f : ⋀[R]^2 M) (x : E R (N R M)) :
    Commute (lift (f : E R M)) x := by
  simpa only [exteriorPower.coe_map, lift] using
    AlternatingForms.twoForm_commute (exteriorPower.map 2 inc f) x

@[simp] theorem contract_zero_assemble (z : E R M × (E R M × (E R M × E R M))) :
    c 0 (assemble z) = lift z.2.1 + e 1 * lift z.2.2.2 := by
  simp [assemble, mul_assoc]

@[simp] theorem contract_one_assemble (z : E R M × (E R M × (E R M × E R M))) :
    c 1 (assemble z) = lift z.2.2.1 - e 0 * lift z.2.2.2 := by
  simp [assemble, mul_assoc]
  abel

/-- The actual exterior differential is precisely the two-form Koszul map
in the four explicit summands. -/
theorem operator_assemble (f g : ⋀[R]^2 M)
    (z : E R M × (E R M × (E R M × E R M))) :
    operator f g (assemble z) =
      assemble ((f : E R M) * z.2.1 + (g : E R M) * z.2.2.1,
        -((g : E R M) * z.2.2.2), (f : E R M) * z.2.2.2, 0) := by
  change lift (f : E R M) * c 0 (assemble z) + lift (g : E R M) * c 1 (assemble z) = _
  rw [contract_zero_assemble, contract_one_assemble]
  simp only [assemble, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_mul, map_neg, map_zero, mul_zero, add_zero,
    mul_add, mul_sub, mul_neg, ← mul_assoc]
  rw [(lift_twoForm_commute f (e 1)).eq, (lift_twoForm_commute g (e 0)).eq]
  abel

/-- The inverse-coordinate form of the same equality. -/
theorem coefficients_operator (f g : ⋀[R]^2 M) (x : E R (N R M)) :
    coefficients (operator f g x) =
      ((f : E R M) * (coefficients x).2.1 + (g : E R M) * (coefficients x).2.2.1,
        -((g : E R M) * (coefficients x).2.2.2),
          (f : E R M) * (coefficients x).2.2.2, 0) := by
  have h := congrArg coefficients (operator_assemble f g (coefficients x))
  simpa only [assemble_coefficients, coefficients_assemble] using h

/-- Group the two middle exterior summands into Koszul position one. -/
def regroup : (E R M × (E R M × (E R M × E R M))) ≃ₗ[R]
    E R M × ((E R M × E R M) × E R M) :=
  (LinearEquiv.refl R (E R M)).prodCongr
    (LinearEquiv.prodAssoc R (E R M) (E R M) (E R M)).symm

/-- The actual linear equivalence with the three Koszul positions. -/
def koszulCoordinates : E R (N R M) ≃ₗ[R] E R M × ((E R M × E R M) × E R M) :=
  decomposition.trans regroup

/-- Conjugation gives the literal folded Koszul differential. -/
theorem koszulCoordinates_operator (f g : ⋀[R]^2 M) (x : E R (N R M)) :
    koszulCoordinates (operator f g x) =
      (first f g (koszulCoordinates x).2.1,
        second f g (koszulCoordinates x).2.2, 0) := by
  change regroup (coefficients (operator f g x)) = _
  rw [coefficients_operator]
  rfl

end PaperVerification.TwoCentralKoszulOperator
