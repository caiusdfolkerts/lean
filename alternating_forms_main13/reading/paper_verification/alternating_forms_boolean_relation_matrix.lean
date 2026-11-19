module

public import PaperVerification.AlternatingFormsBooleanMultiplication
public import PaperVerification.AlternatingFormsEvenGoodBooleanLowerBound
public import Mathlib.LinearAlgebra.Basis.Prod
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Finite matrices of the ordinary Boolean relation spaces

These are the matrices of multiplication by the original two linear forms,
in the genuine square-free coefficient bases.  Their coefficients are
polynomial in the two coefficient vectors.  The relation-range theorem and
rank-nullity identify their cokernels with the actual graded quotient pieces.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanRelationMatrix

open scoped BigOperators Classical
open BooleanQuotient BooleanWalks

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Column (ι : Type*) (r : ℕ) [DecidableEq ι] :=
  FixedSubsets ι r ⊕ FixedSubsets ι r

def relationLinear (b c : ι → R) (r : ℕ) :
    ((FixedSubsets ι r → R) × (FixedSubsets ι r → R)) →ₗ[R]
      (FixedSubsets ι (r+1) → R) :=
  (weightedInclusionOperator b r).coprod (weightedInclusionOperator c r)

def relationMatrix (b c : ι → R) (r : ℕ) :
    Matrix (FixedSubsets ι (r+1)) (Column ι r) R :=
  LinearMap.toMatrix ((Pi.basisFun R (FixedSubsets ι r)).prod
      (Pi.basisFun R (FixedSubsets ι r)))
    (Pi.basisFun R (FixedSubsets ι (r+1))) (relationLinear b c r)

theorem relationMatrix_inl (b c : ι → R) (r : ℕ)
    (U : FixedSubsets ι (r+1)) (T : FixedSubsets ι r) :
    relationMatrix b c r U (Sum.inl T) =
      ∑ i : U.val, if eraseSubset U i = T then b i.val else 0 := by
  simp only [relationMatrix, LinearMap.toMatrix_apply, Pi.basisFun_repr,
    relationLinear, LinearMap.coprod_apply, Module.Basis.prod_apply_inl_fst,
    Module.Basis.prod_apply_inl_snd, map_zero, add_zero, Pi.basisFun_apply,
    weightedInclusionOperator, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply,
    mul_ite, mul_one, mul_zero]

theorem relationMatrix_inr (b c : ι → R) (r : ℕ)
    (U : FixedSubsets ι (r+1)) (T : FixedSubsets ι r) :
    relationMatrix b c r U (Sum.inr T) =
      ∑ i : U.val, if eraseSubset U i = T then c i.val else 0 := by
  simp only [relationMatrix, LinearMap.toMatrix_apply, Pi.basisFun_repr,
    relationLinear, LinearMap.coprod_apply, Module.Basis.prod_apply_inr_fst,
    Module.Basis.prod_apply_inr_snd, map_zero, zero_add, Pi.basisFun_apply,
    weightedInclusionOperator, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply,
    mul_ite, mul_one, mul_zero]

/-- Every ring specialization acts on the two coefficient arrays, exactly. -/
theorem relationMatrix_map (φ : R →+* S) (b c : ι → R) (r : ℕ) :
    (relationMatrix b c r).map φ =
      relationMatrix (fun i ↦ φ (b i)) (fun i ↦ φ (c i)) r := by
  ext U T
  cases T with
  | inl T => simp only [Matrix.map_apply, relationMatrix_inl, map_sum, apply_ite, map_zero]
  | inr T => simp only [Matrix.map_apply, relationMatrix_inr, map_sum, apply_ite, map_zero]

theorem relationLinear_range (b c : ι → K) (r : ℕ) :
    (relationLinear b c r).range = relations b c (r+1) := by
  rw [relationLinear, LinearMap.range_coprod, relations_succ]

theorem relationMatrix_rank (b c : ι → K) (r : ℕ) :
    (relationMatrix b c r).rank = Module.finrank K (relations b c (r+1)) := by
  rw [relationMatrix, LinearMap.rank_toMatrix, relationLinear_range]

/-- This equation concerns the actual homogeneous piece of the polynomial
ideal quotient.  No matrix cokernel is substituted for the quotient by definition. -/
theorem piece_finrank_add_matrix_rank (b c : ι → K) (r : ℕ) :
    Module.finrank K (piece b c (r+1)) + (relationMatrix b c r).rank =
      Fintype.card (FixedSubsets ι (r+1)) := by
  have h := (relations b c (r+1)).finrank_quotient_add_finrank
  rw [(cokernelEquivPiece b c (r+1)).finrank_eq] at h
  rw [relationMatrix_rank]
  simpa only [Module.finrank_pi] using h

def universalMatrix (K : Type*) [CommRing K] (m r : ℕ) :
    Matrix (FixedSubsets (Fin m) (r+1)) (Column (Fin m) r)
      (EvenDeterminants.UniversalParameters K m) :=
  relationMatrix (EvenDeterminants.universalFirst m) (EvenDeterminants.universalSecond m) r

theorem universalMatrix_specialize (m r : ℕ)
    (φ : EvenDeterminants.UniversalParameters R m →+* S) :
    (universalMatrix R m r).map φ =
      relationMatrix (fun i ↦ φ (EvenDeterminants.universalFirst m i))
        (fun i ↦ φ (EvenDeterminants.universalSecond m i)) r :=
  relationMatrix_map φ _ _ r

theorem universalMatrix_evaluate (m r : ℕ) (b c : Fin m → K) :
    (universalMatrix K m r).map (EvenDeterminants.evaluateParameters b c) =
      relationMatrix b c r := by
  simp only [universalMatrix_specialize, EvenDeterminants.evaluateParameters_first,
    EvenDeterminants.evaluateParameters_second]

end PaperVerification.AlternatingForms.BooleanRelationMatrix
