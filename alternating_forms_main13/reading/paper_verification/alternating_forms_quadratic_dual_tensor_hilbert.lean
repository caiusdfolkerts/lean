module

public import PaperVerification.AlternatingFormsQuadraticDualTensor
public import PaperVerification.AlternatingFormsQuadraticDualHilbert

/-!
# The original tensor-quotient grading and Hilbert series

The generator map here is the composite of Mathlib's tensor-algebra
inclusion with the actual annihilator quotient map.  The comparison with
free-generator coordinates preserves this linear map, its range, and
every power of that range.  Thus the Hilbert formula also holds for the
literal tensor-algebra definition of the quadratic dual.

This source is a candidate until its full closure has been checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.QuadraticDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

def tensorGeneratorMap : Module.Dual K (ν → K) →ₗ[K] TensorQuadraticDual f g :=
  (RingQuot.mkAlgHom K (TensorDualRelation f g)).toLinearMap.comp (TensorAlgebra.ι K)

def tensorWordPiece (d : ℕ) : Submodule K (TensorQuadraticDual f g) :=
  (tensorGeneratorMap f g).range ^ d

theorem tensorGeneratorMap_transport :
    (tensorDualEquiv f g).toLinearMap.comp (tensorGeneratorMap f g)=
      (generatorMap f g).comp (Pi.basisFun K ν).toDualEquiv.symm.toLinearMap := by
  apply (Pi.basisFun K ν).dualBasis.ext
  intro i
  change tensorDualEquiv f g
      (RingQuot.mkAlgHom K (TensorDualRelation f g)
        (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=
    generatorMap f g ((Pi.basisFun K ν).toDualEquiv.symm
      ((Pi.basisFun K ν).dualBasis i))
  rw [tensorDualEquiv_generator]
  simp only [Module.Basis.dualBasis,Module.Basis.map_apply,
    LinearEquiv.symm_apply_apply,generatorMap,Module.Basis.constr_basis]

theorem tensorWordPiece_transport (d : ℕ) :
    (tensorWordPiece f g d).map (tensorDualEquiv f g).toLinearMap=wordPiece f g d := by
  change ((tensorGeneratorMap f g).range ^ d).map
    (tensorDualEquiv f g).toAlgHom.toLinearMap=wordPiece f g d
  rw [Submodule.map_pow]
  change ((tensorGeneratorMap f g).range.map (tensorDualEquiv f g).toLinearMap)^d=_
  rw [←LinearMap.range_comp,tensorGeneratorMap_transport]
  rw [LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (Pi.basisFun K ν).toDualEquiv.symm.surjective,
    Submodule.map_top]
  rfl

def tensorDegreeEquiv (d : ℕ) : tensorWordPiece f g d ≃ₗ[K] wordPiece f g d :=
  (Submodule.equivMapOfInjective (tensorDualEquiv f g).toLinearMap
    (tensorDualEquiv f g).injective (tensorWordPiece f g d)).trans
      (LinearEquiv.ofEq _ _ (tensorWordPiece_transport f g d))

def tensorHilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (tensorWordPiece f g d) : ℤ))

theorem tensorHilbertSeries_eq : tensorHilbertSeries f g=hilbertSeries f g := by
  apply PowerSeries.ext
  intro d
  simp only [tensorHilbertSeries,hilbertSeries,PowerSeries.coeff_mk]
  exact congrArg (fun n : ℕ => (n : ℤ)) (tensorDegreeEquiv f g d).finrank_eq

theorem tensorHilbertSeries_mul_denominator_eq_one
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    tensorHilbertSeries f g*
      ((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [tensorHilbertSeries_eq]
  exact hilbertSeries_mul_denominator_eq_one f g hinj

end PaperVerification.AlternatingForms.QuadraticDual
