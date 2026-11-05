module

public import PaperVerification.ToricCharacterSubrepresentations
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

/-! # Coefficient extraction in the genuine tensor product -/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

theorem characterCoefficient_map
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W)
    (m : M) (z : AddMonoidAlgebra k M ⊗[k] V) :
    characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) l z) =
        l (characterCoefficient k m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v => simp only [TensorProduct.map_tmul,LinearMap.id_apply,
      characterCoefficient_tmul,map_smul]
  | add z w hz hw => simp only [map_add,hz,hw]

theorem characterCoefficient_mem_range
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W)
    (m : M) (z : AddMonoidAlgebra k M ⊗[k] W)
    (hz : z∈(TensorProduct.map
      (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) l).range) :
    characterCoefficient k m z∈l.range := by
  obtain ⟨w,rfl⟩ := hz
  exact ⟨characterCoefficient k m w,(characterCoefficient_map k l m w).symm⟩

variable {A : Type*} [CommRing A] [Algebra k A]

theorem characterCoefficient_mul_one_tmul (m : M)
    (z : AddMonoidAlgebra k M ⊗[k] A) (a : A) :
    characterCoefficient k m (z*(1⊗ₜ[k]a)) =
      characterCoefficient k m z*a := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,
        characterCoefficient_tmul,smul_mul_assoc]
  | add z w hz hw => simp only [add_mul,map_add,hz,hw]

/-- The coefficient of the actual coaction, after mapping the second
factor to a field and dividing by one genuine rational local frame. -/
theorem characterCoefficient_coaction_ratio
    (ι : AddMonoidAlgebra k M →ₐ[k] A) (f : AddMonoidAlgebra k M)
    (a : A) (m : M) :
    characterCoefficient k m
      ((Algebra.TensorProduct.map (AlgHom.id k _) ι
        (Coalgebra.comul (R:=k) f))*(1⊗ₜ[k]a)) =
          ι (single m (f.coeff m))*a := by
  rw [characterCoefficient_mul_one_tmul]
  change characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        ι.toLinearMap (Coalgebra.comul (R:=k) f))*a = _
  rw [characterCoefficient_map,characterCoefficient_comul]
  rfl

end PaperVerification.ToricCharacters
