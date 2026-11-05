module

public import PaperVerification.FermionSupercommutative
public import PaperVerification.FermionFiniteSuperTensor

/-!
# Supercommutativity of genuine signed tensor products

The sign identity is checked on homogeneous pure tensors, then extended
through the actual homogeneous spans. It retains the Koszul sign.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion

variable {F A B : Type*} [Field F] [Ring A] [Ring B]
  [Algebra F A] [Algebra F B]
  (pA : ℕ → Submodule F A) (pB : ℕ → Submodule F B)
  [GradedAlgebra pA] [GradedAlgebra pB]

theorem gradedTensor_units_smul_left (u : ℤˣ) (a : A) (b : B) :
    ((u • a) ᵍ⊗ₜ[F] b : pA ᵍ⊗[F] pB)=u • (a ᵍ⊗ₜ[F] b) := by
  rcases Int.units_eq_one_or u with rfl|rfl
  · simp
  · simp only [Units.neg_smul,one_smul,GradedTensorProduct.tmul,
      TensorProduct.neg_tmul,map_neg]

theorem gradedTensor_units_smul_right (u : ℤˣ) (a : A) (b : B) :
    (a ᵍ⊗ₜ[F] (u • b) : pA ᵍ⊗[F] pB)=u • (a ᵍ⊗ₜ[F] b) := by
  rcases Int.units_eq_one_or u with rfl|rfl
  · simp
  · simp only [Units.neg_smul,one_smul,GradedTensorProduct.tmul,
      TensorProduct.tmul_neg,map_neg]

theorem tensor_koszul_sign_identity (i j k l : ℕ) :
    (-1 : ℤˣ)^((k+l)*(i+j))*(-1 : ℤˣ)^(l*i)=
      (-1 : ℤˣ)^(j*k)*(-1 : ℤˣ)^(k*i)*(-1 : ℤˣ)^(l*j) := by
  calc
    (-1 : ℤˣ)^((k+l)*(i+j))*(-1 : ℤˣ)^(l*i)=
        ((-1 : ℤˣ)^(j*k)*(-1 : ℤˣ)^(k*i)*(-1 : ℤˣ)^(l*j))*
          ((-1 : ℤˣ)^(l*i)*(-1 : ℤˣ)^(l*i)) := by
      simp only [Nat.add_mul,Nat.mul_add,pow_add]
      simp only [Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm]
    _ = _ := by rw [Int.units_mul_self,mul_one]

theorem gradedTensor_supercommutative
    (hA : IsSupercommutative pA) (hB : IsSupercommutative pB) :
    IsSupercommutative (naturalGradedTensorPart pA pB) := by
  intro n m x y
  have hx := (naturalGradedTensorPart_eq_span pA pB n).le x.property
  have hy := (naturalGradedTensorPart_eq_span pA pB m).le y.property
  refine Submodule.span_induction₂
    (p := fun x y hx hy ↦ x*y=(-1 : ℤˣ)^(m*n) • (y*x))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨i,j,hij,a,ha,b,hb,rfl⟩ ⟨k,l,hkl,c,hc,d,hd,rfl⟩
    subst n
    subst m
    rw [GradedTensorProduct.tmul_coe_mul_coe_tmul pA pB a ⟨b,hb⟩ ⟨c,hc⟩ d,
      GradedTensorProduct.tmul_coe_mul_coe_tmul pA pB c ⟨d,hd⟩ ⟨a,ha⟩ b,
      hA i k ⟨a,ha⟩ ⟨c,hc⟩,hB j l ⟨b,hb⟩ ⟨d,hd⟩,
      gradedTensor_units_smul_left,gradedTensor_units_smul_right]
    simp only [smul_smul,tensor_koszul_sign_identity,mul_assoc]
  all_goals simp +contextual [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  all_goals
    intro r z t hz ht hzt
    rcases Int.units_eq_one_or ((-1 : ℤˣ)^(m*n)) with hs|hs <;>
      simp only [hs,Units.neg_smul,one_smul,smul_neg]

theorem gradedTensor_includeLeft_degree {i : ℕ} {a : A} (ha : a∈pA i) :
    GradedTensorProduct.includeLeft pA pB a∈naturalGradedTensorPart pA pB i := by
  change (a ᵍ⊗ₜ[F] 1 : pA ᵍ⊗[F] pB)∈naturalGradedTensorPart pA pB i
  simpa only [Nat.add_zero] using naturalGradedTensorPart_tmul_mem pA pB
    ha (SetLike.one_mem_graded pB)

theorem gradedTensor_includeRight_degree {i : ℕ} {b : B} (hb : b∈pB i) :
    GradedTensorProduct.includeRight pA pB b∈naturalGradedTensorPart pA pB i := by
  change (1 ᵍ⊗ₜ[F] b : pA ᵍ⊗[F] pB)∈naturalGradedTensorPart pA pB i
  simpa only [Nat.zero_add] using naturalGradedTensorPart_tmul_mem pA pB
    (SetLike.one_mem_graded pA) hb

theorem gradedTensor_lift_degree {C : Type*} [Ring C] [Algebra F C]
    (pC : ℕ → Submodule F C) [GradedAlgebra pC]
    (f : A →ₐ[F] C) (g : B →ₐ[F] C)
    (hf : ∀ i a,a∈pA i → f a∈pC i)
    (hg : ∀ i b,b∈pB i → g b∈pC i)
    (hcomm : ∀ ⦃i j⦄ (a : pA i) (b : pB j),
      f a*g b=(-1 : ℤˣ)^(j*i) • (g b*f a))
    {n : ℕ} {x : pA ᵍ⊗[F] pB} (hx : x∈naturalGradedTensorPart pA pB n) :
    GradedTensorProduct.lift pA pB f g hcomm x∈pC n := by
  rw [naturalGradedTensorPart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,j,hij,a,ha,b,hb,rfl⟩ := hx
      rw [GradedTensorProduct.lift_tmul,←hij]
      exact SetLike.mul_mem_graded (hf i a ha) (hg j b hb)
  | zero => simpa only [map_zero] using (pC n).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih

end PaperVerification.Fermion

