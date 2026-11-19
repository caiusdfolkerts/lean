module

public import PaperVerification.AlternatingFormsOddPluckerDimension
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Actual exterior coordinates of the linear Plücker relations

The increasing exterior basis is sent to the literal degree-one Plücker
variables.  Every ordered exterior word is sent to the signed ordered
coordinate already used in the determinant charts.  In particular, the
polynomials defining isotropy are exactly the coordinates of multiplication
by the given two-forms on the entire lower exterior power.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n t m : ℕ}

def pluckerOrderEmbeddingEquiv (s n : ℕ) :
    PluckerIndex s n ≃ (Fin s ↪o Fin n) where
  toFun I := OrderEmbedding.ofStrictMono I.val I.property
  invFun f := ⟨f,f.strictMono⟩
  left_inv I := rfl
  right_inv f := by ext i; rfl

def pluckerSubsetEquiv (s n : ℕ) :
    PluckerIndex s n ≃ Set.powersetCard (Fin n) s :=
  (pluckerOrderEmbeddingEquiv s n).trans Set.powersetCard.ofFinEmbEquiv

/-- The genuine increasing exterior basis indexed in exactly the same way
as the Plücker polynomial variables. -/
def exteriorPluckerBasis (s n : ℕ) :
    Module.Basis (PluckerIndex s n) K (⋀[K]^s (Fin n → K)) :=
  ((Pi.basisFun K (Fin n)).exteriorPower s).reindex (pluckerSubsetEquiv s n).symm

theorem exteriorPluckerBasis_apply (I : PluckerIndex s n) :
    exteriorPluckerBasis (K := K) s n I =
      exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I.val i)) := by
  simp only [exteriorPluckerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    exteriorPower.basis_apply,exteriorPower.ιMulti_family,
    pluckerSubsetEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

/-- The coordinate inclusion into the literal degree-one polynomial space.
Its injectivity below prevents identification of different exterior vectors. -/
def exteriorPluckerCoordinates (s n : ℕ) :
    (⋀[K]^s (Fin n → K)) →ₗ[K] MvPolynomial (PluckerIndex s n) K :=
  (exteriorPluckerBasis s n).constr K MvPolynomial.X

@[simp] theorem exteriorPluckerCoordinates_basis (I : PluckerIndex s n) :
    exteriorPluckerCoordinates (K := K) s n (exteriorPluckerBasis s n I)=X I :=
  Module.Basis.constr_basis _ _ _ _

theorem exteriorPluckerCoordinates_injective (s n : ℕ) :
    Function.Injective (exteriorPluckerCoordinates (K := K) s n) :=
  (exteriorPluckerBasis s n).injective_constr_of_linearIndependent
    (MvPolynomial.linearIndependent_X (PluckerIndex s n) K)

/-- Ordered words, including repeated coordinates, have the very same
sorting sign as the universal determinant coordinate. -/
theorem exteriorPluckerCoordinates_word (I : Fin s → Fin n) :
    exteriorPluckerCoordinates (K := K) s n
      (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I i))) =
        orderedPluckerCoordinate I := by
  classical
  by_cases hI : Function.Injective I
  · have hword :
        exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I i)) =
          Equiv.Perm.sign (Tuple.sort I).symm •
            exteriorPluckerBasis (K := K) s n (sortedPluckerIndex I hI) := by
      rw [exteriorPluckerBasis_apply]
      have h := (exteriorPower.ιMulti K s (M := Fin n → K)).map_perm
        (fun i => Pi.basisFun K (Fin n) (I (Tuple.sort I i))) (Tuple.sort I).symm
      simpa only [Function.comp_def,Equiv.apply_symm_apply,sortedPluckerIndex] using h
    rw [hword,map_zsmul_unit,exteriorPluckerCoordinates_basis]
    simp only [orderedPluckerCoordinate,dif_pos hI,Units.smul_def,
      Int.cast_smul_eq_zsmul]
  · have hword : ¬Function.Injective
        (fun i => Pi.basisFun K (Fin n) (I i)) := by
      intro h
      exact hI (fun i j hij => h (congrArg (Pi.basisFun K (Fin n)) hij))
    rw [(exteriorPower.ιMulti K s).map_eq_zero_of_not_injective _ hword,map_zero]
    simp only [orderedPluckerCoordinate,dif_neg hI]

/-- Multiplication by the literal two-form, on the entire degree `t` exterior
power and with the target degree written as `t+2`. -/
def coefficientWedge (f : StrictPairs n → K) :
    (⋀[K]^t (Fin n → K)) →ₗ[K] (⋀[K]^(t+2) (Fin n → K)) where
  toFun x := ⟨(twoFormOfCoefficients f (Pi.basisFun K (Fin n)) :
      ExteriorAlgebra K (Fin n → K)) * x,
    by
      simpa only [Nat.add_comm 2 t] using
        (SetLike.mul_mem_graded
          (twoFormOfCoefficients f (Pi.basisFun K (Fin n))).property x.property)⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

theorem coefficientWedge_word (f : StrictPairs n → K) (J : Fin t → Fin n) :
    coefficientWedge (t := t) f
      (exteriorPower.ιMulti K t (fun i => Pi.basisFun K (Fin n) (J i))) =
      ∑ a : StrictPairs n, f a • exteriorPower.ιMulti K (t+2)
        (fun i => Pi.basisFun K (Fin n)
          (Fin.cons (α := fun _ => Fin n) a.val.1
            (Fin.cons (α := fun _ => Fin n) a.val.2 J) i)) := by
  apply Subtype.ext
  simp only [coefficientWedge,twoFormOfCoefficients,Submodule.coe_smul,
    AddSubmonoidClass.coe_finsetSum,exteriorPair_coe,exteriorPower.ιMulti_apply_coe,
    Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  simp only [ExteriorAlgebra.ιMulti_succ_apply,Fin.cons_zero,Fin.cons_succ,
    Matrix.vecTail,mul_assoc,Function.comp_def,exteriorPower.ιMulti_apply_coe]

/-- Each displayed linear isotropy equation is precisely the coordinate
image of the actual wedge product, without a presentation assumption. -/
theorem exteriorPluckerCoordinates_wedge_word
    (f : StrictPairs n → K) (J : Fin t → Fin n) :
    exteriorPluckerCoordinates (K := K) (t+2) n
      (coefficientWedge f
        (exteriorPower.ιMulti K t (fun i => Pi.basisFun K (Fin n) (J i)))) =
      pluckerIsotropyEquation f J := by
  rw [coefficientWedge_word,map_sum]
  simp only [map_smul,exteriorPluckerCoordinates_word,pluckerIsotropyEquation]

theorem exteriorPluckerCoordinates_wedge_mem
    (f : StrictPairs n → K) (η : ⋀[K]^t (Fin n → K)) :
    exteriorPluckerCoordinates (K := K) (t+2) n (coefficientWedge f η) ∈
      Ideal.span (Set.range (pluckerIsotropyEquation (t := t) f)) := by
  classical
  rw [←(exteriorPluckerBasis (K := K) t n).sum_repr η]
  simp only [map_sum,map_smul]
  apply (Ideal.span (Set.range (pluckerIsotropyEquation (t := t) f))).sum_mem
  intro I hI
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  rw [exteriorPluckerBasis_apply,exteriorPluckerCoordinates_wedge_word]
  exact Ideal.subset_span ⟨I.val,rfl⟩

/-- Equality of the complete generated ideals, so arbitrary lower-degree
exterior vectors introduce neither more nor fewer linear relations. -/
theorem wedgeCoordinates_span_eq (f : StrictPairs n → K) :
    Ideal.span (Set.range fun η : ⋀[K]^t (Fin n → K) =>
      exteriorPluckerCoordinates (K := K) (t+2) n (coefficientWedge f η)) =
        Ideal.span (Set.range (pluckerIsotropyEquation (t := t) f)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨η,rfl⟩
    exact exteriorPluckerCoordinates_wedge_mem f η
  · apply Ideal.span_le.mpr
    rintro _ ⟨J,rfl⟩
    apply Ideal.subset_span
    refine ⟨exteriorPower.ιMulti K t (fun i => Pi.basisFun K (Fin n) (J i)),?_⟩
    exact exteriorPluckerCoordinates_wedge_word f J

/-- The actual ideal used by the determinant charts is exactly the
Grassmannian identity ideal plus the coordinate image of all genuine
two-form wedge relations. All forms and all exterior degrees are retained. -/
theorem isotropicPluckerIdeal_eq_wedgeCoordinates
    (forms : Fin m → StrictPairs n → K) :
    isotropicPluckerIdeal (t := t) forms = matrixPluckerIdeal ⊔
      Ideal.span (Set.range fun a : Fin m × (⋀[K]^t (Fin n → K)) =>
        exteriorPluckerCoordinates (K := K) (t+2) n
          (coefficientWedge (forms a.1) a.2)) := by
  unfold isotropicPluckerIdeal
  congr 1
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,J⟩,rfl⟩
    apply Ideal.subset_span
    refine ⟨(l,exteriorPower.ιMulti K t (fun i => Pi.basisFun K (Fin n) (J i))),?_⟩
    exact exteriorPluckerCoordinates_wedge_word (forms l) J
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,η⟩,rfl⟩
    apply Ideal.span_mono ?_ (exteriorPluckerCoordinates_wedge_mem (forms l) η)
    rintro _ ⟨J,rfl⟩
    exact ⟨(l,J),rfl⟩

end PaperVerification.AlternatingForms
