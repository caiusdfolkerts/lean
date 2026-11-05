module

public import PaperVerification.AlternatingFormsBooleanBadRelations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Boolean upper bound at an actual one-parameter pencil

The parameter is the image of the polynomial variable in its fraction field.
The nonzero bad coefficient minor therefore remains nonzero.  Its columns
are proved to lie in the actual relation subspace of the ordinary Boolean
quotient, and rank-nullity gives the claimed dimension bound.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanUpperBound

open scoped BigOperators Classical
open BooleanWalks BooleanBadRelations BooleanQuotient BooleanCoefficients PolynomialMinors

variable {K : Type*} [Field K] [CharZero K]

abbrev ParameterField (K : Type*) [Field K] := FractionRing (Polynomial K)

def parameter : ParameterField K := algebraMap (Polynomial K) (ParameterField K) Polynomial.X

def constants : K →+* ParameterField K :=
  (algebraMap (Polynomial K) (ParameterField K)).comp Polynomial.C

theorem parameter_ne_zero : parameter (K := K) ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R := K)
  apply IsFractionRing.injective (Polynomial K) (ParameterField K)
  simpa only [parameter, map_zero] using h

theorem parameter_specialization :
    Polynomial.eval₂RingHom (constants (K := K)) parameter =
      algebraMap (Polynomial K) (ParameterField K) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, constants,
      RingHom.comp_apply]
  · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, parameter]

def first (m : ℕ) (i : Fin m) : ParameterField K := parameter ^ forwardWeight m i
def second (m : ℕ) (i : Fin m) : ParameterField K := parameter ^ backwardWeight m i

def mappedRelation {m q : ℕ} (S : BadSubset m q) : MvPolynomial (Fin m) (ParameterField K) :=
  MvPolynomial.map (algebraMap (Polynomial K) (ParameterField K)) (badRelation S)

theorem mappedRelation_mem {m q : ℕ} (S : BadSubset m q) :
    mappedRelation (K := K) S ∈ quotientIdeal (first (K := K) m) (second (K := K) m) := by
  have h := badRelation_mem_quotientIdeal (constants (K := K)) parameter parameter_ne_zero S
  rwa [parameter_specialization] at h

def badVector {m q : ℕ} (S : BadSubset m q) :
    FixedSubsets (Fin m) q → ParameterField K := coefficients q (mappedRelation S)

theorem badVector_mem {m q : ℕ} (S : BadSubset m q) :
    badVector (K := K) S ∈ relations (first (K := K) m) (second (K := K) m) q :=
  coefficients_mem_relations_of_mem_quotientIdeal _ _ _ (mappedRelation_mem S)

theorem badVector_coefficient_det_ne_zero (m q : ℕ) :
    (coefficientMatrix (fun S : BadSubset m q ↦ subsetExponent S.val.val)
      (mappedRelation (K := K))).det ≠ 0 := by
  intro h
  apply badRelation_coefficient_det_ne_zero (K := K) m q
  apply IsFractionRing.injective (Polynomial K) (ParameterField K)
  rw [map_zero, (algebraMap (Polynomial K) (ParameterField K)).map_det,
    coefficientMatrix_map]
  exact h

theorem badVector_linearIndependent (m q : ℕ) :
    LinearIndependent (ParameterField K) (badVector (K := K) (m := m) (q := q)) := by
  let restrict : (FixedSubsets (Fin m) q → ParameterField K) →ₗ[ParameterField K]
      (BadSubset m q → ParameterField K) :=
    LinearMap.pi (fun S ↦ LinearMap.proj S.val)
  apply LinearIndependent.of_comp restrict
  exact Matrix.linearIndependent_cols_of_det_ne_zero
    (badVector_coefficient_det_ne_zero (K := K) m q)

theorem bad_card_le_finrank_relations (m q : ℕ) :
    Fintype.card (BadSubset m q) ≤
      Module.finrank (ParameterField K) (relations (first (K := K) m) (second (K := K) m) q) := by
  let v : BadSubset m q → relations (first (K := K) m) (second (K := K) m) q :=
    fun S ↦ ⟨badVector S, badVector_mem S⟩
  have hv : LinearIndependent (ParameterField K) v :=
    LinearIndependent.of_comp (relations (first (K := K) m) (second (K := K) m) q).subtype
      (badVector_linearIndependent (K := K) m q)
  exact hv.fintype_card_le_finrank

/-- The full upper bound, including degree zero, all degrees above the
middle, and the zero-variable case. -/
theorem boolean_upper_bound (m q : ℕ) :
    Module.finrank (ParameterField K) (piece (first (K := K) m) (second (K := K) m) q) ≤
      Fintype.card (GoodSubset m q) := by
  have hbad := bad_card_le_finrank_relations (K := K) m q
  have hdim := (relations (first (K := K) m) (second (K := K) m) q).finrank_quotient_add_finrank
  have he := (cokernelEquivPiece (first (K := K) m) (second (K := K) m) q).finrank_eq
  have htotal : Module.finrank (ParameterField K)
      (FixedSubsets (Fin m) q → ParameterField K) = Fintype.card (FixedSubsets (Fin m) q) := by
    simp
  rw [htotal, he] at hdim
  have hcard : Fintype.card (BadSubset m q) =
      Fintype.card (FixedSubsets (Fin m) q) - Fintype.card (GoodSubset m q) :=
    Fintype.card_subtype_compl (Good (m := m) (q := q))
  have hle : Fintype.card (GoodSubset m q) ≤ Fintype.card (FixedSubsets (Fin m) q) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  omega

end PaperVerification.AlternatingForms.BooleanUpperBound
