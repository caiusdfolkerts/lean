module

public import PaperVerification.AlternatingFormsMinorStraightening
public import PaperVerification.WeightMonicSubringDescent

/-!
# Integral maximal-minor straightening and arbitrary coefficient change

The previously proved rational straightening theorem has integral input
polynomials.  Distinct monic diagonal leading terms force its expansion
coefficients to be integers.  Mapping these literal integer polynomial
identities proves straightening over every commutative ring, including
fields of positive characteristic.  The determinant expansion below
includes all zero-size boundary cases without any nonemptiness assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {s n r : ℕ}

theorem genericMinorProduct_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Fin r → Fin s → Fin n) :
    MvPolynomial.map φ (genericMinorProduct (K := R) I) =
      genericMinorProduct (K := S) I := by
  simp only [genericMinorProduct, map_prod, RingHom.map_det]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  apply Matrix.ext
  intro i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    MvPolynomial.map_X]

theorem genericStandardMinorProduct_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : StandardMinorChain s n r) :
    MvPolynomial.map φ (genericStandardMinorProduct (K := R) C) =
      genericStandardMinorProduct (K := S) C :=
  genericMinorProduct_map φ C.val

section MonicExpansion

variable {K : Type*} [Field K]

theorem genericMinorProduct_expansion (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := K) I =
      ∑ σ : Fin r → Equiv.Perm (Fin s),
        monomial (chainTermExponent I σ)
          (∏ j, Equiv.Perm.sign (σ j) • (1 : K)) := by
  classical
  have hd (j : Fin r) :
      Matrix.det (Matrix.of (fun i k : Fin s => (X (i,I j k) : MvPolynomial (Fin s × Fin n) K))) =
        ∑ σ : Equiv.Perm (Fin s), monomial (minorTermExponent (I j) σ)
          (Equiv.Perm.sign σ • (1 : K)) := by
    rw [Matrix.det_apply]
    simp only [Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [X, prod_monomial_eq_monomial_sum, Finset.prod_const_one,
      smul_monomial, minorTermExponent]
  simp only [genericMinorProduct, hd]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prod_monomial_eq_monomial_sum _ _

/-- The actual generic standard products have a unique monic greatest
diagonal monomial in every size, including empty rectangles. -/
theorem genericStandardMinorProduct_weightMonic (C : StandardMinorChain s n r) :
    IsWeightMonic (bandEntryWeight s n) (genericStandardMinorProduct (K := K) C)
      (chainDiagonalExponent C.val) := by
  apply isWeightMonic_of_finite_expansion _ _ _ _ (fun _ => 1)
    (genericMinorProduct_expansion C.val)
  · simp only [Equiv.Perm.sign_one, one_smul, Finset.prod_const_one]
  · exact chainTermExponent_weight_lt_diagonal C.val C.property.1

end MonicExpansion

/-- The diagonal exponent determines the standard chain by recovering
the sorted multiplicity list in every row. -/
theorem standardChainDiagonalExponent_injective :
    Function.Injective
      (fun C : StandardMinorChain s n r => chainDiagonalExponent C.val) := by
  classical
  intro C D h
  apply Subtype.ext
  funext t i
  have hperm : (List.ofFn fun t => C.val t i).Perm (List.ofFn fun t => D.val t i) := by
    apply List.perm_iff_count.mpr
    intro j
    simpa only [chainDiagonalExponent_apply] using congrArg (fun a => a (i,j)) h
  have hC : (List.ofFn fun t => C.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => C.val t i) from fun a b hab => C.property.2 hab i).sortedLE_ofFn).pairwise
  have hD : (List.ofFn fun t => D.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => D.val t i) from fun a b hab => D.property.2 hab i).sortedLE_ofFn).pairwise
  exact congrFun (List.ofFn_injective (List.Perm.eq_of_pairwise' hC hD hperm)) t

/-- Rational straightening descends to integral straightening by monicity,
so no tableau denominator remains in the maximal-minor identities. -/
theorem genericMinorProduct_mem_span_standard_int (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := ℤ) I ∈ Submodule.span ℤ
      (Set.range (genericStandardMinorProduct (K := ℤ) (s := s) (n := n) (r := r))) := by
  apply PaperVerification.weightMonic_span_descent
    (Int.castRingHom ℚ) Int.cast_injective (bandEntryWeight s n)
    (genericStandardMinorProduct (K := ℤ))
    (fun C : StandardMinorChain s n r => chainDiagonalExponent C.val)
    standardChainDiagonalExponent_injective
  · intro C
    rw [genericStandardMinorProduct_map]
    exact genericStandardMinorProduct_weightMonic C
  · simpa only [genericMinorProduct_map, genericStandardMinorProduct_map] using
      genericMinorProduct_mem_span_standard_rat I

/-- Explicit integral expansion coefficients exist for every product of
maximal minors.  The statement is a polynomial identity over `ℤ`. -/
theorem genericMinorProduct_integer_expansion (I : Fin r → Fin s → Fin n) :
    ∃ c : StandardMinorChain s n r → ℤ,
      (∑ C, c C • genericStandardMinorProduct (K := ℤ) C) =
        genericMinorProduct (K := ℤ) I :=
  (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (genericMinorProduct_mem_span_standard_int I)

/-- Every integral expansion remains exactly the same determinant identity
after arbitrary coefficient change, without an injectivity assumption. -/
theorem genericMinorProduct_integer_expansion_map
    {R : Type*} [CommRing R] (I : Fin r → Fin s → Fin n)
    (c : StandardMinorChain s n r → ℤ)
    (hc : (∑ C, c C • genericStandardMinorProduct (K := ℤ) C) =
      genericMinorProduct (K := ℤ) I) :
    (∑ C, (c C : R) • genericStandardMinorProduct (K := R) C) =
      genericMinorProduct (K := R) I := by
  have h := congrArg (MvPolynomial.map (Int.castRingHom R)) hc
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, genericStandardMinorProduct_map,
    genericMinorProduct_map, Int.coe_castRingHom] using h

/-- Full maximal-minor straightening over every commutative ring, with
all row counts, column counts, and factor counts retained. -/
theorem genericMinorProduct_mem_span_standard_all
    {R : Type*} [CommRing R] (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := R) I ∈ Submodule.span R
      (Set.range (genericStandardMinorProduct (K := R) (s := s) (n := n) (r := r))) := by
  obtain ⟨c,hc⟩ := genericMinorProduct_integer_expansion I
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  exact ⟨fun C => (c C : R), genericMinorProduct_integer_expansion_map I c hc⟩

/-- The same standard products are independent over every field; this
uses their actual distinct monic polynomial leading terms. -/
theorem genericStandardProducts_linearIndependent
    {K : Type*} [Field K] (s n r : ℕ) :
    LinearIndependent K (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r)) :=
  linearIndependent_of_weightMonic (bandEntryWeight s n) _ _
    standardChainDiagonalExponent_injective genericStandardMinorProduct_weightMonic

end PaperVerification.AlternatingForms
