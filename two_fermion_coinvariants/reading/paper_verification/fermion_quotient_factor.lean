module

public import PaperVerification.FermionSpecialization
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The literal exterior realization of a scalar-relation quotient

The original ambient algebra is the polynomial/exterior tensor product.
After quotienting its scalar factor, the exact polynomial coefficients of
the exterior basis identify the kernel. This constructs a surjective algebra
map from the exterior algebra over the ordinary quotient to the original
two-sided quotient, with its defining commutative square proved explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators

variable {K : Type*} [CommRing K] {n : ℕ}
variable [LinearOrder (OddIndex n)]

def superPolynomialBasis : Module.Basis (Finset (OddIndex n)) (PolynomialRing K n) (SuperRing K n) :=
  ((Pi.basisFun K (OddIndex n)).ExteriorAlgebra).baseChange (PolynomialRing K n)

@[simp] theorem superPolynomialBasis_apply (T : Finset (OddIndex n)) :
    superPolynomialBasis (K := K) T =
      (1 : PolynomialRing K n) ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T :=
  Module.Basis.baseChange_apply _ _ _

theorem superSpecialization_coordinate
    {A : Type*} [CommRing A] [Algebra K A] (f : PolynomialRing K n →ₐ[K] A)
    (z : SuperRing K n) (T : Finset (OddIndex n)) :
    (Pi.basisFun A (OddIndex n)).ExteriorAlgebra.repr (superSpecialization f z) T =
      f ((superPolynomialBasis (K := K)).repr z T) := by
  conv_lhs => rw [← (superPolynomialBasis (K := K)).sum_repr z, map_sum]
  simp only [superSpecialization_smul, superPolynomialBasis_apply,
    superSpecialization_polynomial_wedge, map_one, one_smul,
    map_sum, map_smul, Finsupp.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_ite, smul_zero, smul_eq_mul, mul_one, mul_zero,
    Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem superSpecialization_surjective
    {A : Type*} [CommRing A] [Algebra K A] (f : PolynomialRing K n →ₐ[K] A)
    (hf : Function.Surjective f) : Function.Surjective (superSpecialization f) := by
  intro w
  choose p hp using fun T : Finset (OddIndex n) ↦
    hf ((Pi.basisFun A (OddIndex n)).ExteriorAlgebra.repr w T)
  refine ⟨∑ T, p T ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T, ?_⟩
  simp only [map_sum, superSpecialization_polynomial_wedge, hp]
  exact (Pi.basisFun A (OddIndex n)).ExteriorAlgebra.sum_repr w

theorem superSpecialization_kernel_mem
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I)
    (z : SuperRing K n)
    (hz : superSpecialization (Ideal.Quotient.mkₐ K J) z = 0) : z ∈ I := by
  have hcoeff (T : Finset (OddIndex n)) : (superPolynomialBasis (K := K)).repr z T ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := superSpecialization_coordinate (Ideal.Quotient.mkₐ K J) z T
    rw [hz, map_zero, Finsupp.zero_apply] at hh
    exact hh.symm
  rw [← (superPolynomialBasis (K := K)).sum_repr z]
  apply sum_mem
  intro T hT
  have hm := I.mul_mem_right
    ((Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n)
      ((superPolynomialBasis (K := K)).repr z T))
    (superPolynomialBasis (K := K) T) (hJ _ (hcoeff T))
  simpa only [superPolynomialBasis_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, one_mul] using hm

def superQuotientFactorLinear
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I) :
    ExteriorAlgebra (PolynomialRing K n ⧸ J) (OddModule (PolynomialRing K n ⧸ J) n) →ₗ[K]
      I.ringCon.Quotient :=
  (superSpecialization (Ideal.Quotient.mkₐ K J)).toLinearMap.liftOfSurjective
    (superSpecialization_surjective _ Ideal.Quotient.mk_surjective)
    ⟨(I.ringCon.mkₐ K).toLinearMap, fun z hz ↦
      I.ringCon.eq.mpr (superSpecialization_kernel_mem I J hJ z hz)⟩

@[simp] theorem superQuotientFactorLinear_apply
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I)
    (z : SuperRing K n) :
    superQuotientFactorLinear I J hJ (superSpecialization (Ideal.Quotient.mkₐ K J) z) =
      I.ringCon.mkₐ K z := by
  exact LinearMap.equivOfSurjective_apply _ _

def superQuotientFactor
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I) :
    ExteriorAlgebra (PolynomialRing K n ⧸ J) (OddModule (PolynomialRing K n ⧸ J) n) →ₐ[K]
      I.ringCon.Quotient :=
  AlgHom.ofLinearMap (superQuotientFactorLinear I J hJ)
    (by
      have h := superQuotientFactorLinear_apply I J hJ 1
      have h1 : superSpecialization (Ideal.Quotient.mkₐ K J) (1 : SuperRing K n) = 1 :=
        map_one _
      have h2 : I.ringCon.mkₐ K (1 : SuperRing K n) = 1 :=
        (I.ringCon.mkₐ K).toRingHom.map_one
      rw [h1, h2] at h
      exact h)
    (by
      intro x y
      obtain ⟨x, rfl⟩ := superSpecialization_surjective (Ideal.Quotient.mkₐ K J)
        Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := superSpecialization_surjective (Ideal.Quotient.mkₐ K J)
        Ideal.Quotient.mk_surjective y
      rw [← map_mul, superQuotientFactorLinear_apply, superQuotientFactorLinear_apply,
        superQuotientFactorLinear_apply, map_mul])

@[simp] theorem superQuotientFactor_apply
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I)
    (z : SuperRing K n) :
    superQuotientFactor I J hJ (superSpecialization (Ideal.Quotient.mkₐ K J) z) =
      I.ringCon.mkₐ K z := superQuotientFactorLinear_apply I J hJ z

theorem superQuotientFactor_surjective
    (I : TwoSidedIdeal (SuperRing K n)) (J : Ideal (PolynomialRing K n))
    (hJ : ∀ p ∈ J, (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈ I) :
    Function.Surjective (superQuotientFactor I J hJ) := by
  intro z
  obtain ⟨z, rfl⟩ := I.ringCon.mkₐ_surjective (α := K) z
  exact ⟨superSpecialization (Ideal.Quotient.mkₐ K J) z, superQuotientFactor_apply I J hJ z⟩

end PaperVerification.Fermion
