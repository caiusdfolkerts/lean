module

public import PaperVerification.FermionPrefixCoordinates
public import PaperVerification.FermionEndpointReflection

/-!
# Actual harmonic coefficients satisfy the occupation cutoffs

The prefix coordinates and the finite inverse Gauss polynomials are identified
literally. The only scalar change is the unit sign of suffix extraction; this
sign is removed by its inverse, including over rings with zero divisors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {R I : Type*} [CommRing R] [DecidableEq I]

/-- The four occupation patterns of an actual exterior word. -/
def wordMark (T : Finset (I ⊕ I)) (i : I) : Mark :=
  if Sum.inl i ∈ T then
    if Sum.inr i ∈ T then .double else .theta
  else if Sum.inr i ∈ T then .xi else .unmarked

theorem wordMark_eq_theta_iff (T : Finset (I ⊕ I)) (i : I) :
    wordMark T i = .theta ↔ Sum.inl i ∈ T ∧ Sum.inr i ∉ T := by
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;> simp [wordMark, hθ, hξ]

theorem wordMark_eq_xi_iff (T : Finset (I ⊕ I)) (i : I) :
    wordMark T i = .xi ↔ Sum.inl i ∉ T ∧ Sum.inr i ∈ T := by
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;> simp [wordMark, hθ, hξ]

def harmonicDatum (φ β a c : I → R) (T : Finset (I ⊕ I)) (i : I) : Datum R :=
  ⟨φ i, β i, a i, c i, wordMark T i⟩

def dataFromFin {n : ℕ} (d : Fin n → Datum R) (j : ℕ) : Datum R :=
  if hj : j < n then d ⟨j, hj⟩ else ⟨0, 0, 0, 0, .unmarked⟩

@[simp] theorem dataFromFin_fin {n : ℕ} (d : Fin n → Datum R) (i : Fin n) :
    dataFromFin d i = d i := by simp only [dataFromFin, dif_pos i.isLt]

def harmonicData {n : ℕ} (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) : ℕ → Datum R :=
  dataFromFin (harmonicDatum φ β a c T)

theorem occupation_eq_product (data : ℕ → Datum R) (N i : ℕ) :
    occupation data N i = ∏ j : Fin i, occupationFactor (data j) N := by
  induction i with
  | zero => simp [occupation]
  | succ i ih =>
    rw [occupation, ih, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_comm]

theorem occupationFactor_wordMark (φ β a c : I → R) (T : Finset (I ⊕ I))
    (N : ℕ) (i : I) :
    occupationFactor (harmonicDatum φ β a c T i) N =
      Exterior.diagonalOccupationFactor (fun j ↦ C (-φ j)) (fun _ ↦ X)
        (fun j ↦ gaussNilpotentInverse 1 X (C (-φ j)) N) T i := by
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp only [harmonicDatum, wordMark, hθ, hξ, if_true, if_false,
      occupationFactor, Exterior.diagonalOccupationFactor, and_self, not_true_eq_false,
      not_false_eq_true, false_and, and_false, true_and, atZeroLinear, inverseLinear,
      map_neg, neg_mul, sub_eq_add_neg]

theorem polynomial_natDegree_le_of_unit_smul
    (u : ℤˣ) (p q : R[X]) (h : q = u • p) (d : ℕ) (hq : q.natDegree ≤ d) :
    p.natDegree ≤ d := by
  have hp : p = u⁻¹ • q := by rw [h, smul_smul, inv_mul_cancel, one_smul]
  rw [hp]
  exact (natDegree_smul_le _ _).trans hq

theorem coefficientBound_of_unit_smul
    (u : ℤˣ) (p q : R[X]) (h : q = u • p) (d : ℕ) (hq : CoefficientBound q d) :
    CoefficientBound p d := by
  have hp : p = u⁻¹ • q := by rw [h, smul_smul, inv_mul_cancel, one_smul]
  intro j hj
  rw [hp, Polynomial.coeff_smul, hq j hj, smul_zero]

end PaperVerification.Fermion.Endpoint

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Polynomial
open Colex
open Endpoint

section NegativeNodes

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- The finite-moment harmonic equations also hold at the negated nodes,
by the literal polynomial substitution `p(-t)`. -/
theorem IsHarmonic.neg_parameters (φ β a c : Fin n → R)
    (w : ExteriorAlgebra R V) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b (fun i ↦ -φ i) β a c w := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simpa only [thetaCurrent, thetaFunctional, Polynomial.eval_comp,
      Polynomial.eval_neg, Polynomial.eval_X] using hw.1 (p.comp (-X))
  · intro p
    simpa only [xiCurrent, xiFunctional, Polynomial.eval_comp,
      Polynomial.eval_neg, Polynomial.eval_X] using hw.2.1 (p.comp (-X))
  · intro p
    simpa only [mixedCurrent, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X] using hw.2.2 (p.comp (-X))

end NegativeNodes

section PrefixIdentities

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n i : ℕ}

local instance FermionHarmonicOccupation_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicOccupation_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicOccupation_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicOccupation_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicOccupation_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicOccupation_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

theorem wordMark_prefixWord (hi : i ≤ n) (T : Finset (Fin n ⊕ Fin n)) (j : Fin i) :
    wordMark (prefixWord hi T) j = wordMark T (j.castLE hi) := by
  have hθ : (Sum.inl j ∈ prefixWord hi T) ↔ Sum.inl (j.castLE hi) ∈ T :=
    mem_prefixWord hi T (Sum.inl j)
  have hξ : (Sum.inr j ∈ prefixWord hi T) ↔ Sum.inr (j.castLE hi) ∈ T :=
    mem_prefixWord hi T (Sum.inr j)
  by_cases ht : Sum.inl (j.castLE hi) ∈ T <;>
    by_cases hx : Sum.inr (j.castLE hi) ∈ T <;>
    simp only [wordMark, hθ, hξ, ht, hx, if_true, if_false]

theorem harmonicData_prefix (hi : i ≤ n) (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (j : Fin i) :
    harmonicData φ β a c T j =
      harmonicDatum (φ ∘ Fin.castLE hi) (β ∘ Fin.castLE hi)
        (a ∘ Fin.castLE hi) (c ∘ Fin.castLE hi) (prefixWord hi T) j := by
  have hjn : j.val < n := j.isLt.trans_le hi
  simp only [harmonicData, dataFromFin, dif_pos hjn, harmonicDatum,
    Function.comp_apply, wordMark_prefixWord]
  rfl

theorem prefix_occupation_eq_gauss (hi : i ≤ n) (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (N : ℕ) :
    Endpoint.occupation (harmonicData φ β a c T) N i =
      gaussOccupationPolynomial (fun j : Fin i ↦ -φ (j.castLE hi)) N (prefixWord hi T) := by
  rw [occupation_eq_product, gaussOccupationPolynomial]
  apply Finset.prod_congr rfl
  intro j hj
  rw [harmonicData_prefix hi φ β a c T j, occupationFactor_wordMark]
  rfl

/-- The scalar occupation polynomial from the global coefficient agrees with
the actual smaller-prefix Gauss coefficient up to the contraction unit sign. -/
theorem prefix_diagonal_coefficient (hi : i ≤ n) (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (N : ℕ) (w : ExteriorAlgebra R V)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) :
    diagonalCoefficientPolynomial (pairedPrefixBasis R hi)
      (fun j : Fin i ↦ -φ (j.castLE hi)) N (prefixWord hi T) (extractedPrefix b hi T w) =
      contractionSign (T \ pairedPrefix n i).toList T •
        scalarOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) i := by
  rw [diagonalCoefficientPolynomial, extractedPrefix_coefficient b hi T w hmax,
    map_zsmul_unit, mul_smul_comm, scalarOccupation, prefix_occupation_eq_gauss]

theorem prefix_trace_eq (hi : i ≤ n) (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (N : ℕ) :
    tracePolynomial (harmonicData φ β a c T) N i =
      ∑ j : Fin i, C (β (j.castLE hi) * a (j.castLE hi)) * C (c (j.castLE hi)) *
        gaussNilpotentInverse 1 X (C (-φ (j.castLE hi))) N := by
  rw [tracePolynomial_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [harmonicData_prefix hi φ β a c T j]
  simp only [harmonicDatum, Datum.weight, Function.comp_apply, inverseLinear, map_mul, mul_assoc]

theorem prefix_rankOne_coefficient (hi : i ≤ n) (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (N : ℕ) (w : ExteriorAlgebra R V)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) :
    -rankOneCoefficientPolynomial (pairedPrefixBasis R hi)
      (fun j : Fin i ↦ -φ (j.castLE hi))
      (fun j : Fin i ↦ β (j.castLE hi) * a (j.castLE hi)) (c ∘ Fin.castLE hi)
      N (prefixWord hi T) (extractedPrefix b hi T w) =
      contractionSign (T \ pairedPrefix n i).toList T •
        rankOneOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) i := by
  rw [rankOneCoefficientPolynomial, prefix_diagonal_coefficient b hi φ β a c T N w hmax,
    rankOneOccupation, prefix_trace_eq hi φ β a c T N]
  simp only [Function.comp_apply, mul_smul_comm, neg_mul, smul_neg]

/-- Every actual prefix gives the required scalar degree cutoff for the
global largest coefficient, with no infinite-field argument. -/
theorem largest_coefficient_scalar_occupation_bound
    (φ β a c : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) (i : ℕ) (hi : i ≤ n) :
    (scalarOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) i).natDegree ≤
      i - (T ∩ pairedPrefix n i).card := by
  let x := extractedPrefix b hi T w
  have hx := IsHarmonic.neg_parameters (pairedPrefixBasis R hi)
    (φ ∘ Fin.castLE hi) (β ∘ Fin.castLE hi) (a ∘ Fin.castLE hi) (c ∘ Fin.castLE hi) x
    (extractedPrefix_harmonic b hi T φ β a c w hw hmax)
  have hnil : ∀ j : Fin i, (-φ (j.castLE hi)) ^ N = 0 := by
    intro j
    rw [neg_pow, hφ _, mul_zero]
  have hk : (prefixWord hi T).card ≤ Fintype.card (Fin i) := by
    rw [Fintype.card_fin, card_prefixWord]
    exact largest_harmonic_term_prefix_card_le b φ β a c hfac k w hwdegree hw T hT hmax i hi
  have hd := diagonalCoefficientPolynomial_natDegree_le (pairedPrefixBasis R hi)
    (fun j : Fin i ↦ -φ (j.castLE hi)) N hnil
    (by simpa only [Fintype.card_fin] using unit_factorialCast_of_le hfac hi)
    (prefixWord hi T).card x (extractedPrefix_degree b hi T k w hwdegree hT) hk
    (by simpa only [mixedCurrent,Function.comp_def,Pi.neg_apply] using hx.2.2) (prefixWord hi T)
  apply polynomial_natDegree_le_of_unit_smul
    (contractionSign (T \ pairedPrefix n i).toList T) _ _
    (prefix_diagonal_coefficient b hi φ β a c T N w hmax)
  simpa only [Fintype.card_fin, card_prefixWord] using hd

/-- The actual rank-one polynomial has the sharper cutoff, including exact
vanishing at primitive height zero. -/
theorem largest_coefficient_rankOne_occupation_bound
    (φ β a c : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U : Finset (Fin n ⊕ Fin n), b.ExteriorAlgebra.repr w U ≠ 0 →
      toColex U ≤ toColex T) (i : ℕ) (hi : i ≤ n) :
    CoefficientBound
      (rankOneOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) i)
      (i - (T ∩ pairedPrefix n i).card) := by
  let x := extractedPrefix b hi T w
  have hx := IsHarmonic.neg_parameters (pairedPrefixBasis R hi)
    (φ ∘ Fin.castLE hi) (β ∘ Fin.castLE hi) (a ∘ Fin.castLE hi) (c ∘ Fin.castLE hi) x
    (extractedPrefix_harmonic b hi T φ β a c w hw hmax)
  have hnil : ∀ j : Fin i, (-φ (j.castLE hi)) ^ N = 0 := by
    intro j
    rw [neg_pow, hφ _, mul_zero]
  have hk : (prefixWord hi T).card ≤ Fintype.card (Fin i) := by
    rw [Fintype.card_fin, card_prefixWord]
    exact largest_harmonic_term_prefix_card_le b φ β a c hfac k w hwdegree hw T hT hmax i hi
  apply coefficientBound_of_unit_smul
    (contractionSign (T \ pairedPrefix n i).toList T) _ _
    (prefix_rankOne_coefficient b hi φ β a c T N w hmax)
  intro j hj
  rw [coeff_neg]
  apply neg_eq_zero.mpr
  apply rankOneCoefficientPolynomial_coeff_eq_zero (pairedPrefixBasis R hi)
    (fun q : Fin i ↦ -φ (q.castLE hi))
    (fun q : Fin i ↦ β (q.castLE hi) * a (q.castLE hi)) (c ∘ Fin.castLE hi) N hnil
    (by simpa only [Fintype.card_fin] using unit_factorialCast_of_le hfac hi)
    (prefixWord hi T).card x (extractedPrefix_degree b hi T k w hwdegree hT) hk
  · simpa only [mixedCurrent,Function.comp_def,Pi.neg_apply] using hx.2.2
  · simpa only [thetaCurrent, thetaFunctional, rankOneThetaDual,Function.comp_def,Pi.neg_apply] using hx.1
  · simpa only [xiCurrent, xiFunctional, rankOneXiDual, Function.comp_def,Pi.neg_apply] using hx.2.1
  · simpa only [Fintype.card_fin, card_prefixWord] using hj

end PrefixIdentities

end PaperVerification.Fermion.Exterior
