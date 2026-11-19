module

public import PaperVerification.AlternatingFormsPluckerLinearAction

/-!
# Change of basis of the full isotropic Plücker ideal

The exterior naturality identity transports the entire ideal of isotropy
equations.  The resulting quotient equivalence retains the actual ideal;
no reducedness, saturation, or equality of closed points is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {t n m : ℕ}

/-- The isotropic scheme depends on the span of the two forms, with its
full original homogeneous ideal retained. -/
theorem pair_isotropicIdeal_eq_of_quadraticSpan_eq
    (f g f' g' : StrictPairs n → K)
    (h : Submodule.span K
      ({twoFormOfCoefficients f (Pi.basisFun K (Fin n)),
        twoFormOfCoefficients g (Pi.basisFun K (Fin n))} :
          Set (⋀[K]^2 (Fin n → K))) =
      Submodule.span K
      ({twoFormOfCoefficients f' (Pi.basisFun K (Fin n)),
        twoFormOfCoefficients g' (Pi.basisFun K (Fin n))} :
          Set (⋀[K]^2 (Fin n → K)))) :
    isotropicPluckerIdeal (t := t) (pairCoefficientForms f g) =
      isotropicPluckerIdeal (pairCoefficientForms f' g') := by
  rw [pair_isotropicIdeal_eq_linearIdeal, pair_isotropicIdeal_eq_linearIdeal,
    coefficientPairRelations_eq_exterior, coefficientPairRelations_eq_exterior]
  have he := exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ h
  simp only [exteriorDegreeRelations, he]

theorem coefficientWedge_linearMap
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (f f' : StrictPairs n → K)
    (hf : exteriorPower.map 2 e (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f' (Pi.basisFun K (Fin n)))
    (x : ⋀[K]^t (Fin n → K)) :
    exteriorPower.map (t+2) e (coefficientWedge f x) =
      coefficientWedge f' (exteriorPower.map t e x) := by
  have hf' := congrArg Subtype.val hf
  simp only [exteriorPower.coe_map] at hf'
  apply Subtype.ext
  simp only [exteriorPower.coe_map]
  change (ExteriorAlgebra.map e)
      ((twoFormOfCoefficients f (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * (x : ExteriorAlgebra K (Fin n → K))) =
    (twoFormOfCoefficients f' (Pi.basisFun K (Fin n)) :
      ExteriorAlgebra K (Fin n → K)) *
        ((exteriorPower.map t e x) : ExteriorAlgebra K (Fin n → K))
  rw [map_mul, hf', exteriorPower.coe_map]

/-- Forward transport of every equation under the actual linear coordinate map. -/
theorem pluckerLinearAction_preserves_isotropicIdeal
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    isotropicPluckerIdeal (t := t) forms ≤
      Ideal.comap (pluckerLinearAction e (t+2)).toRingHom
        (isotropicPluckerIdeal forms') := by
  rw [isotropicPluckerIdeal_eq_wedgeCoordinates]
  apply sup_le
  · intro p hp
    rw [Ideal.mem_comap, isotropicPluckerIdeal_eq_wedgeCoordinates]
    exact Ideal.mem_sup_left (pluckerLinearAction_preserves_matrixIdeal e p hp)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,x⟩,rfl⟩
    change exteriorPluckerCoordinates (t+2) n (coefficientWedge (forms l) x) ∈
      Ideal.comap (pluckerLinearAction e (t+2)).toRingHom
        (isotropicPluckerIdeal forms')
    rw [Ideal.mem_comap]
    change pluckerLinearAction e (t+2)
      (exteriorPluckerCoordinates (t+2) n (coefficientWedge (forms l) x)) ∈ _
    rw [pluckerLinearAction_coordinates, coefficientWedge_linearMap e _ _ (hforms l)]
    rw [isotropicPluckerIdeal_eq_wedgeCoordinates]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨(l,exteriorPower.map t e x),rfl⟩)

theorem twoForm_linearEquiv_reverse
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (f f' : StrictPairs n → K)
    (hf : exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f' (Pi.basisFun K (Fin n))) :
    exteriorPower.map 2 e.symm.toLinearMap
      (twoFormOfCoefficients f' (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f (Pi.basisFun K (Fin n)) := by
  rw [← hf]
  exact (exteriorPowerLinearEquiv e 2).symm_apply_apply _

/-- Exact equality of the original scheme ideals after an invertible coordinate change. -/
theorem pluckerLinearEquiv_map_isotropicIdeal
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Ideal.map (pluckerLinearEquiv e (t+2)).toRingHom
      (isotropicPluckerIdeal (t := t) forms) = isotropicPluckerIdeal forms' := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr
      (pluckerLinearAction_preserves_isotropicIdeal e.toLinearMap forms forms' hforms)
  · intro p hp
    let g := pluckerLinearEquiv e (t+2)
    have hg : g.symm p ∈ isotropicPluckerIdeal (t := t) forms :=
      pluckerLinearAction_preserves_isotropicIdeal e.symm.toLinearMap forms' forms
        (fun l => twoForm_linearEquiv_reverse e _ _ (hforms l)) hp
    have hm : g (g.symm p) ∈ Ideal.map g.toRingHom
        (isotropicPluckerIdeal (t := t) forms) :=
      Ideal.mem_map_of_mem g.toRingHom hg
    simpa only [AlgEquiv.apply_symm_apply] using hm

/-- The actual coordinate rings of linearly equivalent tuples of forms are equivalent. -/
def isotropicPluckerLinearEquiv
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms') :=
  Ideal.quotientEquivAlg _ _ (pluckerLinearEquiv e (t+2))
    (pluckerLinearEquiv_map_isotropicIdeal e forms forms' hforms).symm

@[simp] theorem isotropicPluckerLinearEquiv_mk
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    isotropicPluckerLinearEquiv e forms forms' hforms (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (pluckerLinearAction e.toLinearMap (t+2) p) := rfl

theorem pluckerLinearAction_homogeneous
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    (pluckerLinearAction e (t+2) p).IsHomogeneous d := by
  simpa only [pluckerLinearAction, one_mul] using hp.aeval
    (fun I => exteriorPluckerCoordinates (t+2) n
      (exteriorPower.map (t+2) e (exteriorPluckerBasis (t+2) n I)))
    (fun I => exteriorPluckerCoordinates_isHomogeneous _)

end PaperVerification.AlternatingForms
