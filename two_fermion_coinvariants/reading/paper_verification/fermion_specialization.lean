module

public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionHarmonicPairing
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The original superalgebra maps into the actual harmonic pairing

This is the bridge from the tensor-product presentation in the paper to the
exterior algebra over the ordinary quotient. It uses the literal two-sided
ideal; no relation is silently replaced by an ordinary commutative ideal.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

/-- Extend the two free odd spaces along the coefficient homomorphism. -/
def oddScalarExtension : OddModule K n →ₗ[K] OddModule A n where
  toFun v i := algebraMap K A (v i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [Algebra.smul_def]

@[simp] theorem oddScalarExtension_single (i : OddIndex n) :
    oddScalarExtension (K := K) (A := A) (Pi.single i 1) = Pi.single i 1 := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simp [oddScalarExtension]
  · simp [oddScalarExtension, Pi.single_eq_of_ne h]

/-- The actual exterior-algebra change of coefficients. -/
def oddExteriorSpecialization :
    ExteriorAlgebra K (OddModule K n) →ₐ[K] ExteriorAlgebra A (OddModule A n) :=
  ExteriorAlgebra.lift K
    ⟨((ExteriorAlgebra.ι A).restrictScalars K).comp oddScalarExtension,
      fun v ↦ ExteriorAlgebra.ι_sq_zero _⟩

@[simp] theorem oddExteriorSpecialization_generator (i : OddIndex n) :
    oddExteriorSpecialization (K := K) (A := A)
      (ExteriorAlgebra.ι K (Pi.single i 1)) =
        ExteriorAlgebra.ι A (Pi.single i 1) := by
  rw [oddExteriorSpecialization,ExteriorAlgebra.lift_ι_apply]
  change ExteriorAlgebra.ι A (oddScalarExtension (Pi.single i 1)) = _
  rw [oddScalarExtension_single]

/-- Specialize the polynomial coefficients and extend all odd variables. -/
def superSpecialization (f : PolynomialRing K n →ₐ[K] A) :
    SuperRing K n →ₐ[K] ExteriorAlgebra A (OddModule A n) :=
  Algebra.TensorProduct.lift (R := K) (S := K)
    (((Algebra.ofId A (ExteriorAlgebra A (OddModule A n))).restrictScalars K).comp f)
    oddExteriorSpecialization
    (fun p z ↦ Algebra.commute_algebraMap_left (f p) _)

theorem superSpecialization_tmul (f : PolynomialRing K n →ₐ[K] A)
    (p : PolynomialRing K n) (z : ExteriorAlgebra K (OddModule K n)) :
    superSpecialization f (p ⊗ₜ[K] z)=
      algebraMap A (ExteriorAlgebra A (OddModule A n)) (f p)*
        oddExteriorSpecialization z := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ p z

@[simp] theorem superSpecialization_includeLeft (f : PolynomialRing K n →ₐ[K] A)
    (p : PolynomialRing K n) :
    superSpecialization f (Algebra.TensorProduct.includeLeft (R := K) (S := K) p) =
      algebraMap A (ExteriorAlgebra A (OddModule A n)) (f p) := by
  rw [Algebra.TensorProduct.includeLeft_apply,superSpecialization_tmul,map_one,mul_one]

@[simp] theorem superSpecialization_theta (f : PolynomialRing K n →ₐ[K] A) (i : Fin n) :
    superSpecialization f (theta K n i) = ExteriorAlgebra.ι A (Pi.single (.inl i) 1) := by
  simp only [theta,Algebra.TensorProduct.includeRight_apply,superSpecialization_tmul,
    map_one,one_mul,oddExteriorSpecialization_generator]

@[simp] theorem superSpecialization_xi (f : PolynomialRing K n →ₐ[K] A) (i : Fin n) :
    superSpecialization f (xi K n i) = ExteriorAlgebra.ι A (Pi.single (.inr i) 1) := by
  simp only [xi,Algebra.TensorProduct.includeRight_apply,superSpecialization_tmul,
    map_one,one_mul,oddExteriorSpecialization_generator]

 theorem superSpecialization_smul (f : PolynomialRing K n →ₐ[K] A)
    (p : PolynomialRing K n) (z : SuperRing K n) :
    superSpecialization f (p • z) = f p • superSpecialization f z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b w
    rw [TensorProduct.smul_tmul',superSpecialization_tmul,superSpecialization_tmul]
    simp only [smul_eq_mul,map_mul,Algebra.smul_def,mul_assoc]
  · intro x y hx hy
    simp only [smul_add,map_add,hx,hy]

@[simp] theorem specialization_C (f : PolynomialRing K n →ₐ[K] A) (a : K) :
    f (MvPolynomial.C a) = algebraMap K A a := f.commutes a

 theorem superSpecialization_paired_polynomial (f : PolynomialRing K n →ₐ[K] A)
    (β : Fin n → K) (φ a c : Fin n → PolynomialRing K n) (k : ℕ) :
    superSpecialization f (moment φ (pairedCoefficients β a c .polynomial) k) =
      algebraMap A (ExteriorAlgebra A (OddModule A n))
        (moment (fun i ↦ f (φ i))
          (fun i ↦ algebraMap K A (β i) * f (a i) * f (c i)) k) := by
  simp only [moment, pairedCoefficients, map_sum, superSpecialization_smul,
    map_pow, map_mul, specialization_C, map_one]
  simp only [Algebra.smul_def,mul_one,Algebra.algebraMap_self,RingHom.id_apply,← map_mul,← map_pow]

 theorem superSpecialization_paired_theta (f : PolynomialRing K n →ₐ[K] A)
    (β : Fin n → K) (φ a c : Fin n → PolynomialRing K n) (k : ℕ) :
    superSpecialization f (moment φ (pairedCoefficients β a c .theta) k) =
      Exterior.thetaRelation (Pi.basisFun A (OddIndex n)) (fun i ↦ f (φ i))
        (fun i ↦ f (c i)) (Polynomial.X ^ k) := by
  simp only [moment, pairedCoefficients, map_sum, superSpecialization_smul, map_pow,
    superSpecialization_theta, Exterior.thetaRelation, Polynomial.eval_pow,
    Polynomial.eval_X, Pi.basisFun_apply, smul_smul, map_mul,map_pow,mul_comm]

 theorem superSpecialization_paired_xi (f : PolynomialRing K n →ₐ[K] A)
    (β : Fin n → K) (φ a c : Fin n → PolynomialRing K n) (k : ℕ) :
    superSpecialization f (moment φ (pairedCoefficients β a c .xi) k) =
      Exterior.xiRelation (Pi.basisFun A (OddIndex n)) (fun i ↦ f (φ i))
        (fun i ↦ algebraMap K A (β i)) (fun i ↦ f (a i)) (Polynomial.X ^ k) := by
  simp only [moment, pairedCoefficients, map_sum, superSpecialization_smul, map_pow,
    superSpecialization_xi, Exterior.xiRelation, Polynomial.eval_pow,
    Polynomial.eval_X, Pi.basisFun_apply, smul_smul, map_mul,
    specialization_C, mul_comm]

 theorem superSpecialization_paired_mixed (f : PolynomialRing K n →ₐ[K] A)
    (β : Fin n → K) (φ a c : Fin n → PolynomialRing K n) (k : ℕ) :
    superSpecialization f (moment φ (pairedCoefficients β a c .mixed) k) =
      Exterior.mixedRelation (Pi.basisFun A (OddIndex n)) (fun i ↦ f (φ i))
        (Polynomial.X ^ k) := by
  simp only [moment, pairedCoefficients, map_sum, superSpecialization_smul, map_pow,
    map_mul, superSpecialization_theta, superSpecialization_xi, Exterior.mixedRelation,
    Polynomial.eval_pow, Polynomial.eval_X, Pi.basisFun_apply]

/-- Every actual paired relation is orthogonal to every actual moment harmonic
once the ordinary moments vanish in the coefficient algebra. -/
 theorem pairedIdeal_le_harmonic_comap [LinearOrder (OddIndex n)]
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ a c : Fin n → PolynomialRing K n)
    (hordinary : ∀ k, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (a i) * f (c i)) k = 0) :
    pairedIdeal β φ a c ≤
      (Exterior.harmonicOrthogonalIdeal (Pi.basisFun A (OddIndex n))
        (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun i ↦ f (a i)) (fun i ↦ f (c i))).comap (superSpecialization f).toRingHom := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨⟨kind, k⟩, rfl⟩
  change superSpecialization f (moment φ (pairedCoefficients β a c kind) k) ∈
    Exterior.harmonicOrthogonalIdeal (Pi.basisFun A (OddIndex n))
      (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ f (a i)) (fun i ↦ f (c i))
  have h := Exterior.relations_mem_harmonicOrthogonal (Pi.basisFun A (OddIndex n))
    (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
    (fun i ↦ f (a i)) (fun i ↦ f (c i)) (Polynomial.X ^ k)
  cases kind with
  | polynomial =>
      rw [superSpecialization_paired_polynomial, hordinary, map_zero]
      exact TwoSidedIdeal.zero_mem _
  | theta => rw [superSpecialization_paired_theta]; exact h.1
  | xi => rw [superSpecialization_paired_xi]; exact h.2.1
  | mixed => rw [superSpecialization_paired_mixed]; exact h.2.2

 theorem paired_relation_pairing_zero [LinearOrder (OddIndex n)]
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ a c : Fin n → PolynomialRing K n)
    (hordinary : ∀ k, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (a i) * f (c i)) k = 0)
    (z : SuperRing K n) (hz : z ∈ pairedIdeal β φ a c)
    (w : ExteriorAlgebra A (OddModule A n))
    (hw : Exterior.IsHarmonic (Pi.basisFun A (OddIndex n))
      (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ f (a i)) (fun i ↦ f (c i)) w) :
    Exterior.coefficientPairing (Pi.basisFun A (OddIndex n)) (superSpecialization f z) w = 0 := by
  have h := pairedIdeal_le_harmonic_comap f β φ a c hordinary hz
  rw [TwoSidedIdeal.mem_comap, Exterior.mem_harmonicOrthogonalIdeal] at h
  exact h w hw

@[simp] theorem oddExteriorSpecialization_basis [LinearOrder (OddIndex n)]
    (s : Finset (OddIndex n)) :
    oddExteriorSpecialization (K := K) (A := A)
      ((Pi.basisFun K (OddIndex n)).ExteriorAlgebra s) =
        (Pi.basisFun A (OddIndex n)).ExteriorAlgebra s := by
  simp only [Module.Basis.exteriorAlgebra_eq_prod_map_sort, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply, Pi.basisFun_apply, oddExteriorSpecialization_generator]

 theorem superSpecialization_polynomial_wedge [LinearOrder (OddIndex n)]
    (f : PolynomialRing K n →ₐ[K] A) (p : PolynomialRing K n)
    (s : Finset (OddIndex n)) :
    superSpecialization f
      (p ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra s) =
        f p • (Pi.basisFun A (OddIndex n)).ExteriorAlgebra s := by
  rw [superSpecialization_tmul,oddExteriorSpecialization_basis,Algebra.smul_def]

end PaperVerification.Fermion
