module

public import PaperVerification.AlternatingFormsEvenDeterminantNormalization
public import PaperVerification.AlternatingFormsPolynomialMinors

/-!
# Universal determinant products and their nonzero coefficient minor

The vectors in this file are the original determinants with two independent
families of polynomial parameters.  After specializing those parameters, each
vector has its own exact power of the degeneration parameter.  We retain these
powers when comparing coefficient minors.  Consequently the independence
result concerns the universal vectors themselves.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators Polynomial
open PolynomialMinors

variable {K F α τ ι : Type*} [CommRing K] [CommRing F]

theorem oddSubsetDeterminant_map (φ : K →+* F) (r : ℕ)
    (b c : α → K) (a : OddRows r → α) :
    MvPolynomial.map φ (oddSubsetDeterminant r b c a) =
      oddSubsetDeterminant r (fun i => φ (b i)) (fun i => φ (c i)) a := by
  rw [oddSubsetDeterminant, oddSubsetDeterminant, (MvPolynomial.map φ).map_det]
  congr 1
  ext i j
  cases i <;> simp [oddSubsetMatrix]

theorem oddSubsetDeterminant_homogeneous (r : ℕ) (b c : α → K)
    (a : OddRows r → α) : (oddSubsetDeterminant r b c a).IsHomogeneous r := by
  rw [oddSubsetDeterminant_expansion]
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  exact (termVariables_homogeneous r a σ).C_mul _

/-- Two independent coefficient parameters for each variable. -/
abbrev UniversalParameters (K : Type*) [CommRing K] (m : ℕ) :=
  MvPolynomial (Bool × Fin m) K

def universalFirst (m : ℕ) (i : Fin m) : UniversalParameters K m :=
  MvPolynomial.X (false, i)

def universalSecond (m : ℕ) (i : Fin m) : UniversalParameters K m :=
  MvPolynomial.X (true, i)

/-- A literal specialization of the two universal coefficient vectors. -/
def parameterSpecialization (m : ℕ) : UniversalParameters K m →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C fun
    | (false, i) => firstParameter m i
    | (true, i) => secondParameter m i

@[simp] theorem parameterSpecialization_first (m : ℕ) (i : Fin m) :
    parameterSpecialization (K := K) m (universalFirst m i) = firstParameter m i := by
  simp [parameterSpecialization, universalFirst]

@[simp] theorem parameterSpecialization_second (m : ℕ) (i : Fin m) :
    parameterSpecialization (K := K) m (universalSecond m i) = secondParameter m i := by
  simp [parameterSpecialization, universalSecond]

section Products

variable [Fintype τ]

def determinantProduct (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (b c : Fin m → K) :
    MvPolynomial (Fin m) K :=
  ∏ a, oddSubsetDeterminant (r a) b c (fun i => I a (rowPosition (r a) i))

def normalizedProduct (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) : MvPolynomial (Fin m) K[X] :=
  ∏ a, normalizedDeterminant m (r a) (I a)

def productExponent (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) : ℕ :=
  ∑ a, determinantTermExponent m (r a) (I a) 1

/-- The exponent vector of the product of alternating-position monomials. -/
def productLeadingExponent (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) : Fin m →₀ ℕ :=
  ∑ a, ∑ i : Fin (r a), Finsupp.single (I a (rowPosition (r a) (Sum.inr i))) 1

def universalProduct (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) :
    MvPolynomial (Fin m) (UniversalParameters K m) :=
  determinantProduct m r I (universalFirst m) (universalSecond m)

theorem determinantProduct_map (φ : K →+* F) (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (b c : Fin m → K) :
    MvPolynomial.map φ (determinantProduct m r I b c) =
      determinantProduct m r I (fun i => φ (b i)) (fun i => φ (c i)) := by
  simp only [determinantProduct, map_prod, oddSubsetDeterminant_map]

theorem determinantProduct_joint_kernel (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (b c : Fin m → K) :
    directionalDerivative b (determinantProduct m r I b c) = 0 ∧
    directionalDerivative c (determinantProduct m r I b c) = 0 :=
  determinant_product_joint_kernel Finset.univ r b c
    (fun a i => I a (rowPosition (r a) i))

theorem determinantProduct_homogeneous (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (b c : Fin m → K) :
    (determinantProduct m r I b c).IsHomogeneous (∑ a, r a) :=
  MvPolynomial.IsHomogeneous.prod Finset.univ _ r
    (fun a _ => oddSubsetDeterminant_homogeneous (r a) b c _)

/-- The exact factor removed from the product is the sum of the exact factors
removed from its constituent determinants. -/
theorem normalizedProduct_factor (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (hI : ∀ a, StrictMono (I a)) :
    MvPolynomial.C (Polynomial.X ^ productExponent m r I) *
        normalizedProduct (K := K) m r I =
      determinantProduct m r I (firstParameter m) (secondParameter m) := by
  unfold productExponent normalizedProduct determinantProduct
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun a _ => normalizedDeterminant_factor m (r a) (I a) (hI a))

theorem normalizedProduct_at_zero (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (hI : ∀ a, StrictMono (I a)) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K)) (normalizedProduct m r I) =
      MvPolynomial.monomial (productLeadingExponent m r I) 1 := by
  unfold normalizedProduct productLeadingExponent
  rw [map_prod, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro a ha
  rw [normalizedDeterminant_at_zero m (r a) (I a) (hI a),
    MvPolynomial.monomial_sum_one]
  rfl

/-- This identity compares the original universal vector with the normalized
polynomial.  Its scalar factor must not be discarded in a generic-rank proof. -/
theorem universalProduct_specialization (m : ℕ) (r : τ → ℕ)
    (I : (a : τ) → Fin (2 * r a + 1) → Fin m) (hI : ∀ a, StrictMono (I a)) :
    MvPolynomial.map (parameterSpecialization (K := K) m) (universalProduct m r I) =
      MvPolynomial.C (Polynomial.X ^ productExponent m r I) * normalizedProduct m r I := by
  rw [universalProduct, determinantProduct_map]
  simp only [parameterSpecialization_first, parameterSpecialization_second]
  exact (normalizedProduct_factor m r I hI).symm

end Products

section Families

variable [Fintype τ] [Fintype ι] [DecidableEq ι] [IsDomain K]

/-- Distinct alternating-position monomials give a nonzero minor of the
original universal determinant products.  The conclusion is in the universal
parameter ring, not merely in its one-parameter specialization. -/
theorem universalProduct_coefficient_det_ne_zero (m : ℕ) (r : ι → τ → ℕ)
    (I : (w : ι) → (a : τ) → Fin (2 * r w a + 1) → Fin m)
    (hI : ∀ w a, StrictMono (I w a))
    (hinj : Function.Injective (fun w => productLeadingExponent m (r w) (I w))) :
    (coefficientMatrix (fun w => productLeadingExponent m (r w) (I w))
      (fun w => universalProduct (K := K) m (r w) (I w))).det ≠ 0 := by
  let e : ι → Fin m →₀ ℕ := fun w => productLeadingExponent m (r w) (I w)
  let A := coefficientMatrix e (fun w => universalProduct (K := K) m (r w) (I w))
  let B := coefficientMatrix e (fun w => normalizedProduct (K := K) m (r w) (I w))
  apply det_ne_zero_of_map_eq_column_scaled (parameterSpecialization m) A B
    (fun w => Polynomial.X ^ productExponent m (r w) (I w))
  · intro w
    exact pow_ne_zero _ Polynomial.X_ne_zero
  · apply Matrix.ext
    intro i j
    change parameterSpecialization m
        ((universalProduct (K := K) m (r j) (I j)).coeff (e i)) = _
    rw [← MvPolynomial.coeff_map, universalProduct_specialization m (r j) (I j) (hI j),
      MvPolynomial.coeff_C_mul]
    rfl
  · exact coefficient_det_ne_zero_of_monomial_specialization
      (Polynomial.evalRingHom (0 : K)) e hinj _
      (fun w => normalizedProduct_at_zero m (r w) (I w) (hI w))

theorem universalProduct_linearIndependent (m : ℕ) (r : ι → τ → ℕ)
    (I : (w : ι) → (a : τ) → Fin (2 * r w a + 1) → Fin m)
    (hI : ∀ w a, StrictMono (I w a))
    (hinj : Function.Injective (fun w => productLeadingExponent m (r w) (I w))) :
    LinearIndependent (UniversalParameters K m)
      (fun w => universalProduct (K := K) m (r w) (I w)) :=
  linearIndependent_of_coefficient_det_ne_zero _ _
    (universalProduct_coefficient_det_ne_zero m r I hI hinj)

end Families

end PaperVerification.AlternatingForms.EvenDeterminants
