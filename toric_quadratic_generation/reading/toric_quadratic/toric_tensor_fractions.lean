module

public import PaperVerification.ToricLaurentPicard
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-!
# Actual Laurent scalar extension and tensor denominator clearing

The tensor product with a lattice character algebra remains a domain over
an arbitrary domain. A tensor with a fraction field admits one common
denominator from the original coefficient ring. These elementary facts
will prove injectivity of the actual torus-product rational map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct nonZeroDivisors

theorem latticeGroupAlgebra_isDomain (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    IsDomain (AddMonoidAlgebra R (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain (FractionRing R) n
  let f := AddMonoidAlgebra.mapRingHom (Fin n→ℤ) (algebraMap R (FractionRing R))
  apply Function.Injective.isDomain f
  exact AddMonoidAlgebra.map_injective (algebraMap R (FractionRing R)).toAddMonoidHom
    (IsFractionRing.injective R (FractionRing R))

def latticeTensorAlgEquiv (k : Type*) [CommRing k] (n : ℕ)
    (R : Type*) [CommRing R] [Algebra k R] :
    AddMonoidAlgebra k (Fin n→ℤ) ⊗[k] R ≃ₐ[k] AddMonoidAlgebra R (Fin n→ℤ) :=
  (Algebra.TensorProduct.comm k (AddMonoidAlgebra k (Fin n→ℤ)) R).trans
    ((AddMonoidAlgebra.scalarTensorEquiv k R (M:=Fin n→ℤ)).restrictScalars k)

theorem latticeTensor_isDomain (k : Type*) [CommRing k] (n : ℕ)
    (R : Type*) [CommRing R] [IsDomain R] [Algebra k R] :
    IsDomain (AddMonoidAlgebra k (Fin n→ℤ) ⊗[k] R) := by
  letI := latticeGroupAlgebra_isDomain R n
  exact MulEquiv.isDomain (AddMonoidAlgebra R (Fin n→ℤ))
    (latticeTensorAlgEquiv k n R).toMulEquiv

section Denominators

variable (k A R K : Type*) [CommRing k] [CommRing A] [CommRing R] [IsDomain R]
    [Field K] [Algebra k A] [Algebra k R] [Algebra k K] [Algebra R K]
    [IsScalarTower k R K] [IsFractionRing R K]

/-- A tensor has finitely many fraction coefficients, so a single
nonzero coefficient-ring denominator clears all of them. -/
theorem tensor_exists_common_denominator (w : A ⊗[k] K) :
    ∃ (d : R) (_ : d≠0) (t : A ⊗[k] R),
      Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k R K) t=
        (1 ⊗ₜ[k] algebraMap R K d)*w := by
  let F := Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k R K)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1,one_ne_zero,0,by simp⟩
  | tmul a z =>
      obtain ⟨r,d,hd,hz⟩ := IsFractionRing.div_surjective R z
      have hd0 : d≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
      have hdK : algebraMap R K d≠0 := by
        simpa only [map_zero] using (IsFractionRing.injective R K).ne hd0
      refine ⟨d,hd0,a ⊗ₜ[k] r,?_⟩
      rw [← hz]
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [mul_div_cancel₀ _ hdK]
  | add w z hw hz =>
      obtain ⟨d,hd,t,ht⟩ := hw
      obtain ⟨e,he,u,hu⟩ := hz
      refine ⟨d*e,mul_ne_zero hd he,(1 ⊗ₜ[k] e)*t+(1 ⊗ₜ[k] d)*u,?_⟩
      change F _=_
      rw [map_add,map_mul,map_mul,show F t=(1 ⊗ₜ[k] algebraMap R K d)*w from ht,
        show F u=(1 ⊗ₜ[k] algebraMap R K e)*z from hu]
      simp only [F,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply,map_mul]
      have hprod : (1 ⊗ₜ[k] (algebraMap R K d*algebraMap R K e) : A ⊗[k] K)=
          (1 ⊗ₜ[k] algebraMap R K d)*(1 ⊗ₜ[k] algebraMap R K e) := by
        simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [hprod]
      ring

end Denominators

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.tensor_exists_common_denominator
