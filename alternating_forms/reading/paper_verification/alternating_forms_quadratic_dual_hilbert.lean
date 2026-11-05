module

public import PaperVerification.AlternatingFormsQuadraticDual
public import PaperVerification.TwoStepPBWHilbert

/-!
# The genuine quadratic-dual grading and its complete Hilbert series

The degree pieces are defined inside the annihilator-presented quadratic
dual as powers of the span of its original free generators.  The actual
enveloping-algebra isomorphism is proved to preserve those generators,
and hence every degree piece.  The weighted PBW count therefore computes
this quadratic dual's Hilbert series, rather than that of an unrelated
graded presentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.QuadraticDual

open TwoStepDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

def generatorMap : (ν → K) →ₗ[K] QuadraticDual f g :=
  (Pi.basisFun K ν).constr K
    (fun i => RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i))

def generatorSpace : Submodule K (QuadraticDual f g) := LinearMap.range (generatorMap f g)

/-- Exact degree in the original quadratic generators. -/
def wordPiece (d : ℕ) : Submodule K (QuadraticDual f g) := generatorSpace f g ^ d

variable (hinj : Function.Injective (orbitExteriorRelationMap f g 1))

theorem generatorMap_transport :
    (quadraticDualEnvelopingEquiv f g hinj).toLinearMap.comp (generatorMap f g)=
      TwoStepPBWGrading.generatorMap (bracketData f g) := by
  apply (Pi.basisFun K ν).ext
  intro i
  simp only [LinearMap.comp_apply,generatorMap,Module.Basis.constr_basis,
    AlgEquiv.toLinearMap_apply,quadraticDualEnvelopingEquiv_generator,
    TwoStepPBWGrading.generatorMap]
  rfl

theorem generatorSpace_transport :
    (generatorSpace f g).map (quadraticDualEnvelopingEquiv f g hinj).toLinearMap=
      TwoStepPBWGrading.generatorSpace (bracketData f g) := by
  rw [generatorSpace,←LinearMap.range_comp,generatorMap_transport]
  rfl

theorem wordPiece_transport (d : ℕ) :
    (wordPiece f g d).map (quadraticDualEnvelopingEquiv f g hinj).toLinearMap=
      TwoStepPBWGrading.wordPiece (bracketData f g) d := by
  change (generatorSpace f g ^ d).map
    (quadraticDualEnvelopingEquiv f g hinj).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((generatorSpace f g).map
    (quadraticDualEnvelopingEquiv f g hinj).toLinearMap)^d=_
  rw [generatorSpace_transport]
  rfl

def degreeEquiv (d : ℕ) :
    wordPiece f g d ≃ₗ[K] TwoStepPBWGrading.wordPiece (bracketData f g) d :=
  (Submodule.equivMapOfInjective (quadraticDualEnvelopingEquiv f g hinj).toLinearMap
    (quadraticDualEnvelopingEquiv f g hinj).injective (wordPiece f g d)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport f g hinj d))

def hilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (wordPiece f g d) : ℤ))

include hinj in
theorem hilbertSeries_transport :
    hilbertSeries f g=TwoStepPBWGrading.hilbertSeries (bracketData f g) := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries,TwoStepPBWGrading.hilbertSeries,PowerSeries.coeff_mk]
  exact congrArg (fun n : ℕ => (n : ℤ)) (degreeEquiv f g hinj d).finrank_eq

include hinj in
/-- The full printed rational series for the ordinary quadratic dual,
expressed as an exact identity of power series over the integers. -/
theorem hilbertSeries_mul_denominator_eq_one :
    hilbertSeries f g*((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [hilbertSeries_transport f g hinj]
  exact TwoStepPBWGrading.hilbertSeries_mul_denominator_eq_one (bracketData f g)
    (bracketMap_surjective f g hinj)

include hinj in
theorem hilbertSeries_eq_inverse :
    hilbertSeries f g=(PowerSeries.invOneSubPow ℤ (Fintype.card ν) : ℤ⟦X⟧)*
      PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2) := by
  rw [hilbertSeries_transport f g hinj]
  exact TwoStepPBWGrading.hilbertSeries_eq_inverse (bracketData f g)
    (bracketMap_surjective f g hinj)

end PaperVerification.AlternatingForms.QuadraticDual
