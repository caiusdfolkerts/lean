module
public import sunlet.normalized_algebra
public import sunlet.verified_generic_conclusions

@[expose] public section
set_option Elab.async false

#check "SUNLET_VERIFIEDNORMALIZEDMODEL_IMPORTS_READY"

section Stage_NormalizedGenericEvaluation


/-!
# Faithful generic evaluation of the normalized model

The Laurent-coordinate algebra of the literal normalization embeds into
the independent parameter field. Consequently its equations are exactly
the equations of the original affine five-family map. This bridge lets
rational coordinate-recovery identities descend to the actual model.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

def normalizedVariableEquiv :
    Normalization.Variable ι Ω L.identity o ≃
      Ω ⊕ ToricPairAlgebra.Index (ι := L.NonidentityColor) o where
  toFun
    | .z x => .inl x
    | .k x => .inr (false, .inr x)
    | .l x => .inr (true, .inr x)
    | .u a => .inr (false, .inl a)
    | .v a => .inr (true, .inl a)
  invFun
    | .inl x => .z x
    | .inr (false, .inr x) => .k x
    | .inr (true, .inr x) => .l x
    | .inr (false, .inl a) => .u a
    | .inr (true, .inl a) => .v a
  left_inv j := by cases j <;> rfl
  right_inv j := by
    rcases j with x | ⟨b,a | x⟩
    · rfl
    · cases b <;> rfl
    · cases b <;> rfl

theorem generic_normalized_variableValues :
    Normalization.variableValues (L.genericNormalizedParameters (k := k) o) =
      IteratedRationalField.combined ∘ L.normalizedVariableEquiv o := by
  funext j
  cases j with
  | z x => rfl
  | k x =>
      simp only [Normalization.variableValues, genericNormalizedParameters,
        normalizedVariableEquiv, Equiv.coe_fn_mk, Function.comp_apply,
        IteratedRationalField.combined, Sum.elim_inr,
        embeddedTorus, Units.coe_map, genericTorus, dif_neg x.property, Units.val_mk0]
      rfl
  | l x =>
      simp only [Normalization.variableValues, genericNormalizedParameters,
        normalizedVariableEquiv, Equiv.coe_fn_mk, Function.comp_apply,
        IteratedRationalField.combined, Sum.elim_inr,
        embeddedTorus, Units.coe_map, genericTorus, dif_neg x.property, Units.val_mk0]
      rfl
  | u a => rfl
  | v a => rfl

theorem generic_normalized_variables_independent :
    AlgebraicIndependent k
      (Normalization.variableValues (L.genericNormalizedParameters (k := k) o)) := by
  rw [L.generic_normalized_variableValues o]
  exact (IteratedRationalField.combined_independent (k := k)
    (I := ToricPairAlgebra.Index (ι := L.NonidentityColor) o) (J := Ω)).comp
      (L.normalizedVariableEquiv o) (L.normalizedVariableEquiv o).injective

def genericNormalizedEvaluation :
    Normalization.LocalizedRing k L.identity o →ₐ[k] L.NormalizedSourceField (k := k) o :=
  Normalization.evaluate (L.genericNormalizedParameters (k := k) o)

theorem genericNormalizedEvaluation_algebraMap
    (f : Normalization.PolynomialRing k L.identity o) :
    L.genericNormalizedEvaluation o
      (algebraMap (Normalization.PolynomialRing k L.identity o)
        (Normalization.LocalizedRing k L.identity o) f) =
      MvPolynomial.aeval (R := k)
        (Normalization.variableValues (L.genericNormalizedParameters (k := k) o)) f := by
  have he : (L.genericNormalizedEvaluation (k := k) o).comp
      (IsScalarTower.toAlgHom k (Normalization.PolynomialRing k L.identity o)
        (Normalization.LocalizedRing k L.identity o)) =
      MvPolynomial.aeval (R := k)
        (Normalization.variableValues (L.genericNormalizedParameters (k := k) o)) := by
    ext j
    simpa only [genericNormalizedEvaluation, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply, MvPolynomial.aeval_X, Normalization.parameterVariable] using
      Normalization.evaluate_variable (K := k) (L.genericNormalizedParameters (k := k) o) j
  exact AlgHom.congr_fun he f

theorem genericNormalizedEvaluation_injective :
    Function.Injective (L.genericNormalizedEvaluation (k := k) o) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Normalization.denominator k L.identity o))
    (L.genericNormalizedEvaluation (k := k) o).toRingHom).mpr
  intro f g
  constructor
  · exact congrArg (L.genericNormalizedEvaluation o)
  · intro he
    change L.genericNormalizedEvaluation o
        (algebraMap (Normalization.PolynomialRing k L.identity o)
          (Normalization.LocalizedRing k L.identity o) f) =
      L.genericNormalizedEvaluation o
        (algebraMap (Normalization.PolynomialRing k L.identity o)
          (Normalization.LocalizedRing k L.identity o) g) at he
    rw [L.genericNormalizedEvaluation_algebraMap o,
      L.genericNormalizedEvaluation_algebraMap o] at he
    exact congrArg (algebraMap (Normalization.PolynomialRing k L.identity o)
      (Normalization.LocalizedRing k L.identity o))
      ((algebraicIndependent_iff_injective_aeval.mp
        (L.generic_normalized_variables_independent (k := k) o)) he)

theorem genericNormalizedEvaluation_comorphism (f : MvPolynomial (ι × Ω) k) :
    L.genericNormalizedEvaluation o
      (Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o) L.perm f) =
      MvPolynomial.aeval (R := k)
        (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o)) f := by
  have he : (L.genericNormalizedEvaluation (k := k) o).comp
      (Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o) L.perm) =
      MvPolynomial.aeval (R := k)
        (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o)) := by
    ext ab
    simpa only [AlgHom.comp_apply, Normalization.normalizedComorphism,
      MvPolynomial.aeval_X, Normalization.parameterMap, genericNormalizedEvaluation] using
      Normalization.evaluate_coordinate (L.genericNormalizedParameters (k := k) o)
        L.perm ab.1 ab.2
  exact AlgHom.congr_fun he f

/-- Equality with the actual original defining equations. No genericity
or algebraic-independence condition is assumed at this endpoint. -/
theorem generic_normalized_equation_iff (f : MvPolynomial (ι × Ω) k) :
    MvPolynomial.aeval (R := k)
      (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o)) f = 0 ↔
      PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := k) L.perm) f = 0 := by
  rw [← L.genericNormalizedEvaluation_comorphism o]
  have hi (p : Normalization.LocalizedRing k L.identity o) :
      L.genericNormalizedEvaluation o p = 0 ↔ p = 0 := by
    constructor
    · intro hp
      apply L.genericNormalizedEvaluation_injective o
      simpa only [map_zero] using hp
    · rintro rfl
      exact map_zero _
  rw [hi]
  change f ∈ RingHom.ker
      (Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o) L.perm) ↔
    f ∈ PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := k) L.perm)
  rw [Normalization.definingIdeal_eq_normalizedKernel L.perm L.normalized]

/-- The coordinate ring of the full affine model, defined by its original
five-family polynomial substitution, before any normalization. -/
abbrev ModelCoordinateRing :=
  MvPolynomial (ι × Ω) k ⧸
    PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := k) L.perm)

instance modelCoordinateRing_isDomain : IsDomain (L.ModelCoordinateRing (k := k)) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    (RingHom.ker_isPrime (PolynomialImage.comorphism
      (Sunlet.coordinatePolynomial (K := k) L.perm)))

abbrev ModelFunctionField := FractionRing (L.ModelCoordinateRing (k := k))

/-- The original coordinate ring is exactly the algebra generated by the
faithful generic normalized coordinates. -/
def modelCoordinateRingEquivGenericAlgebra :
    L.ModelCoordinateRing (k := k) ≃ₐ[k]
      Algebra.adjoin k (Set.range
        (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o))) :=
  (Ideal.quotientEquivAlgOfEq k (by
    ext f
    exact (L.generic_normalized_equation_iff (k := k) o f).symm)).trans
      ((Ideal.quotientKerEquivRange
        (MvPolynomial.aeval (Normalization.parameterMap L.perm
          (L.genericNormalizedParameters (k := k) o)))).trans
        (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval k _).symm))

open scoped IntermediateField.algebraAdjoinAdjoin

/-- The normalized generated field is the function field of the actual
original affine model. This is an algebra equivalence over the original
ground field, so rationality and degrees transport without extension of scalars. -/
def modelFunctionFieldEquivNormalizedImage :
    L.ModelFunctionField (k := k) ≃ₐ[k] L.NormalizedImageField (k := k) o :=
  IsFractionRing.algEquivOfAlgEquiv (L.modelCoordinateRingEquivGenericAlgebra (k := k) o)

/-- The field equivalence respects every literal model coordinate. -/
theorem modelFunctionFieldEquiv_coordinate (ab : ι × Ω) :
    (L.modelFunctionFieldEquivNormalizedImage (k := k) o
      (algebraMap (L.ModelCoordinateRing (k := k)) (L.ModelFunctionField (k := k))
        (Ideal.Quotient.mk
          (PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := k) L.perm))
          (MvPolynomial.X ab))) : L.NormalizedSourceField (k := k) o) =
      Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) ab := by
  rw [modelFunctionFieldEquivNormalizedImage,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [modelCoordinateRingEquivGenericAlgebra,Ideal.quotientKerEquivRange]

end Sunlet.NormalizedLatinSystem
end
end Stage_NormalizedGenericEvaluation
#check "SUNLET_VERIFIEDNORMALIZEDMODEL_NormalizedGenericEvaluation_DONE"

#check Sunlet.NormalizedLatinSystem.genericNormalizedEvaluation_injective
#print axioms Sunlet.NormalizedLatinSystem.genericNormalizedEvaluation_injective

#check Sunlet.NormalizedLatinSystem.generic_normalized_equation_iff
#print axioms Sunlet.NormalizedLatinSystem.generic_normalized_equation_iff

#check Sunlet.NormalizedLatinSystem.modelFunctionFieldEquivNormalizedImage
#print axioms Sunlet.NormalizedLatinSystem.modelFunctionFieldEquivNormalizedImage

#check Sunlet.NormalizedLatinSystem.modelFunctionFieldEquiv_coordinate
#print axioms Sunlet.NormalizedLatinSystem.modelFunctionFieldEquiv_coordinate
