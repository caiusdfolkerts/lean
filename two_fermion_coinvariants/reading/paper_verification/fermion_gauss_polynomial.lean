module

public import PaperVerification.FermionScalarExtension
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Literal polynomial Gauss equations

The parameter is the indeterminate `Polynomial.X`. The equations below follow
by explicit scalar extension of the exterior vector and its annihilation
equations, not by evaluating a polynomial at scalar points. Nilpotence of the
moment nodes is exactly the hypothesis supplied by the homogeneous ordinary
Artinian algebra; no nilpotence of the original polynomial variables is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

section Coordinates

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (b : Module.Basis (I ⊕ I) R V)

/-- The exact scalar of the diagonal operator at an arbitrary exterior word. -/
def diagonalOccupationFactor (a c d : I → R) (T : Finset (I ⊕ I)) (i : I) : R :=
  if Sum.inl i ∈ T ∧ Sum.inr i ∈ T then d i
  else if Sum.inl i ∉ T ∧ Sum.inr i ∉ T then 1 + a i * c i else 1

theorem diagonalProduct_basis (a c d : I → R)
    (hd : ∀ i, d i * (1 + a i * c i) = 1) (T : Finset (I ⊕ I)) :
    ((Finset.univ.toList.map fun i ↦
      pairGaussDiagonal (a i) (c i) (d i) (pairLower b i) (pairRaise b i)).prod)
        (b.ExteriorAlgebra T) =
      (∏ i, diagonalOccupationFactor a c d T i) • b.ExteriorAlgebra T := by
  have h := list_prod_apply_eigenvector Finset.univ.toList
    (fun i ↦ pairGaussDiagonal (a i) (c i) (d i) (pairLower b i) (pairRaise b i))
    (diagonalOccupationFactor a c d T) (b.ExteriorAlgebra T)
    (fun i _ ↦ pairGaussDiagonal_basis b i T (a i) (c i) (d i) (hd i))
  simpa only [Finset.prod_map_toList] using h

theorem diagonalProduct_coord (a c d : I → R)
    (hd : ∀ i, d i * (1 + a i * c i) = 1)
    (w : ExteriorAlgebra R V) (T : Finset (I ⊕ I)) :
    b.ExteriorAlgebra.repr
      (((Finset.univ.toList.map fun i ↦
        pairGaussDiagonal (a i) (c i) (d i) (pairLower b i) (pairRaise b i)).prod) w) T =
      (∏ i, diagonalOccupationFactor a c d T i) * b.ExteriorAlgebra.repr w T := by
  have h : (b.ExteriorAlgebra.coord T).comp
      ((Finset.univ.toList.map fun i ↦
        pairGaussDiagonal (a i) (c i) (d i) (pairLower b i) (pairRaise b i)).prod) =
      (∏ i, diagonalOccupationFactor a c d T i) • b.ExteriorAlgebra.coord T := by
    apply b.ExteriorAlgebra.ext
    intro U
    simp only [LinearMap.comp_apply, diagonalProduct_basis b a c d hd U,
      map_smul, LinearMap.smul_apply]
    by_cases hUT : U = T
    · subst U
      rfl
    · simp [Module.Basis.coord_apply, Finsupp.single_apply, hUT, Ne.symm hUT]
  exact LinearMap.congr_fun h w

end Coordinates

section Polynomial

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (b : Module.Basis (I ⊕ I) R V)

/-- The diagonal rational product represented by its finite inverse polynomials. -/
def gaussOccupationPolynomial (y : I → R) (N : ℕ) (T : Finset (I ⊕ I)) : Polynomial R :=
  ∏ i, diagonalOccupationFactor
    (fun i ↦ Polynomial.C (y i)) (fun _ ↦ Polynomial.X)
    (fun i ↦ gaussNilpotentInverse 1 Polynomial.X (Polynomial.C (y i)) N) T i

/-- The coefficient of the selected exterior word in the diagonal identity. -/
def diagonalCoefficientPolynomial (y : I → R) (N : ℕ)
    (T : Finset (I ⊕ I)) (w : ExteriorAlgebra R V) : Polynomial R :=
  gaussOccupationPolynomial y N T * Polynomial.C (b.ExteriorAlgebra.repr w T)

/-- The exact rank-one trace, before multiplying by the extra parameter. -/
def rankOneCoefficientPolynomial (y U a : I → R) (N : ℕ)
    (T : Finset (I ⊕ I)) (w : ExteriorAlgebra R V) : Polynomial R :=
  (∑ i, Polynomial.C (U i) * Polynomial.C (a i) *
      gaussNilpotentInverse 1 Polynomial.X (Polynomial.C (y i)) N) *
    diagonalCoefficientPolynomial b y N T w

/-- Nilpotent nodes remain nilpotent after literal polynomial scalar extension. -/
theorem polynomial_gauss_nilpotence (y : I → R) (N : ℕ) (hy : ∀ i, y i ^ N = 0) :
    ∀ i, ((-1 * (Polynomial.X : Polynomial R)) * Polynomial.C (y i)) ^ N = 0 := by
  intro i
  rw [mul_pow, ← map_pow, hy i, map_zero, mul_zero]

/-- The first prefix equation is a literal polynomial of degree at most the
primitive weight. Its coefficients are given in the original coefficient ring. -/
theorem diagonalCoefficientPolynomial_eq
    (y : I → R) (N : ℕ) (hy : ∀ i, y i ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (T : Finset (I ⊕ I)) :
    diagonalCoefficientPolynomial b y N T w =
      ∑ j ∈ Finset.range (Fintype.card I - k + 1),
        Polynomial.X ^ j * Polynomial.C
          (b.ExteriorAlgebra.repr (diagonalGaussCoefficient b y k w j) T) := by
  let b' := Pi.basisFun (Polynomial R) (I ⊕ I)
  let w' := exteriorScalarExtension b b' Polynomial.C w
  have hnil := polynomial_gauss_nilpotence y N hy
  have hunit : IsUnit ((Fintype.card I).factorial : Polynomial R) := by
    simpa using hfac.map (Polynomial.C : R →+* Polynomial R)
  have h := diagonal_gauss_bounded_expression b' (Polynomial.C ∘ y) Polynomial.X N
    hnil hunit k w' (exteriorScalarExtension_mem b b' Polynomial.C hwdegree) hk
    (exteriorScalarExtension_mixed b b' Polynomial.C y w hw)
  have hc := congrArg (b'.ExteriorAlgebra.coord T) h
  simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul] at hc
  rw [diagonalProduct_coord b' _ _ _ (fun i ↦ by
    simpa only [one_mul, Function.comp_apply] using
      gaussNilpotentInverse_mul_of_product_pow_eq_zero
        (1 : Polynomial R) Polynomial.X (Polynomial.C (y i)) N (hnil i))] at hc
  simp only [w'] at hc
  simp_rw [exteriorScalarExtension_diagonalGaussCoefficient b b' Polynomial.C y k w] at hc
  simpa only [diagonalCoefficientPolynomial, gaussOccupationPolynomial,
    exteriorScalarExtension_coord, Function.comp_def] using hc

theorem diagonalCoefficientPolynomial_natDegree_le
    (y : I → R) (N : ℕ) (hy : ∀ i, y i ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (T : Finset (I ⊕ I)) :
    (diagonalCoefficientPolynomial b y N T w).natDegree ≤ Fintype.card I - k := by
  rw [diagonalCoefficientPolynomial_eq b y N hy hfac k w hwdegree hk hw T]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  rw [mul_comm]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ j).trans (by
    have := Finset.mem_range.mp hj
    omega)

/-- The polynomial rank-one identity has the same cutoff; its extra factor
`X` is retained so coefficient extraction gives the sharper bound directly. -/
theorem X_mul_rankOneCoefficientPolynomial_eq
    (y U a : I → R) (N : ℕ) (hy : ∀ i, y i ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hθ : ∀ p : Polynomial R,
      annihilation (rankOneThetaDual b (fun i ↦ a i * p.eval (y i))) w = 0)
    (hξ : ∀ p : Polynomial R,
      annihilation (rankOneXiDual b (fun i ↦ U i * p.eval (y i))) w = 0)
    (T : Finset (I ⊕ I)) :
    Polynomial.X * rankOneCoefficientPolynomial b y U a N T w =
      ∑ j ∈ Finset.range (Fintype.card I - k + 1),
        Polynomial.X ^ j * Polynomial.C
          (b.ExteriorAlgebra.repr (diagonalRankOneCoefficient b y U a 1 k w j) T) := by
  let b' := Pi.basisFun (Polynomial R) (I ⊕ I)
  let w' := exteriorScalarExtension b b' Polynomial.C w
  have hnil := polynomial_gauss_nilpotence y N hy
  have hunit : IsUnit ((Fintype.card I).factorial : Polynomial R) := by
    simpa using hfac.map (Polynomial.C : R →+* Polynomial R)
  have hθ' : ∀ p : Polynomial (Polynomial R),
      annihilation (rankOneThetaDual b'
        (fun i ↦ Polynomial.C (a i) * p.eval (Polynomial.C (y i)))) w' = 0 := by
    intro p
    have hh := exteriorScalarExtension_odd b b' Polynomial.C Sum.inl y a w
      (fun q ↦ by simpa only [rankOneThetaDual, annihilation, map_sum, map_smul] using hθ q) p
    simpa only [rankOneThetaDual, annihilation, map_sum, map_smul] using hh
  have hξ' : ∀ p : Polynomial (Polynomial R),
      annihilation (rankOneXiDual b'
        (fun i ↦ Polynomial.C (U i) * p.eval (Polynomial.C (y i)))) w' = 0 := by
    intro p
    have hh := exteriorScalarExtension_odd b b' Polynomial.C Sum.inr y U w
      (fun q ↦ by simpa only [rankOneXiDual, annihilation, map_sum, map_smul] using hξ q) p
    simpa only [rankOneXiDual, annihilation, map_sum, map_smul] using hh
  have h := diagonal_gauss_rankone_bounded_expression b' (Polynomial.C ∘ y)
    (Polynomial.C ∘ U) (Polynomial.C ∘ a) 1 Polynomial.X N hnil hunit
    k w' (exteriorScalarExtension_mem b b' Polynomial.C hwdegree) hk
    (exteriorScalarExtension_mixed b b' Polynomial.C y w hw) hθ' hξ'
  have hext (j : ℕ) :
      diagonalRankOneCoefficient b' (Polynomial.C ∘ y) (Polynomial.C ∘ U)
        (Polynomial.C ∘ a) 1 k w' j =
      exteriorScalarExtension b b' Polynomial.C
        (diagonalRankOneCoefficient b y U a 1 k w j) := by
    simpa only [map_one] using
      exteriorScalarExtension_diagonalRankOneCoefficient b b' Polynomial.C y U a 1 k w j
  have hc := congrArg (b'.ExteriorAlgebra.coord T) h
  simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, hext] at hc
  rw [diagonalProduct_coord b' _ _ _ (fun i ↦ by
    simpa only [one_mul, Function.comp_apply] using
      gaussNilpotentInverse_mul_of_product_pow_eq_zero
        (1 : Polynomial R) Polynomial.X (Polynomial.C (y i)) N (hnil i))] at hc
  simpa only [rankOneCoefficientPolynomial, diagonalCoefficientPolynomial,
    gaussOccupationPolynomial, w', exteriorScalarExtension_coord,
    map_one, one_mul, Function.comp_apply, mul_assoc] using hc

/-- The sharper rank-one coefficient bound, including the zero primitive-weight
case where the entire polynomial vanishes. -/
theorem rankOneCoefficientPolynomial_coeff_eq_zero
    (y U a : I → R) (N : ℕ) (hy : ∀ i, y i ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hθ : ∀ p : Polynomial R,
      annihilation (rankOneThetaDual b (fun i ↦ a i * p.eval (y i))) w = 0)
    (hξ : ∀ p : Polynomial R,
      annihilation (rankOneXiDual b (fun i ↦ U i * p.eval (y i))) w = 0)
    (T : Finset (I ⊕ I)) (j : ℕ) (hj : Fintype.card I - k ≤ j) :
    (rankOneCoefficientPolynomial b y U a N T w).coeff j = 0 := by
  have hd : (Polynomial.X * rankOneCoefficientPolynomial b y U a N T w).natDegree ≤
      Fintype.card I - k := by
    rw [X_mul_rankOneCoefficientPolynomial_eq b y U a N hy hfac k w hwdegree hk hw hθ hξ T]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    rw [mul_comm]
    exact (Polynomial.natDegree_C_mul_X_pow_le _ r).trans (by
      have := Finset.mem_range.mp hr
      omega)
  have h := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega :
    Fintype.card I - k < j + 1))
  simpa only [Polynomial.coeff_X_mul, Nat.add_sub_cancel] using h

end Polynomial

end PaperVerification.Fermion.Exterior
