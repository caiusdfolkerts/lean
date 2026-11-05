module

public import PaperVerification.FermionTensorSupercommutative

/-!
# The natural exterior bigrading on genuine signed tensor products

The bidegree components are independently defined as spans of homogeneous
pure tensors, using bases of the original component spaces. Multiplication
uses the already fixed total-degree Koszul sign. Compatibility with total
degree is proved, rather than installing a new multiplication.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion

section Basis

variable {F C Γ : Type*} [Field F] [Ring C] [Algebra F C]
  [AddCommMonoid Γ] [DecidableEq Γ]

def multihomogeneousBasis (piece : Γ → Submodule F C) [GradedAlgebra piece] :
    Module.Basis (Σ g,Module.Free.ChooseBasisIndex F (piece g)) F C :=
  (DirectSum.Decomposition.isInternal piece).collectedBasis
    (fun g ↦ Module.Free.chooseBasis F (piece g))

theorem multihomogeneousBasis_mem (piece : Γ → Submodule F C) [GradedAlgebra piece]
    (i : Σ g,Module.Free.ChooseBasisIndex F (piece g)) :
    multihomogeneousBasis piece i∈piece i.1 :=
  (DirectSum.Decomposition.isInternal piece).collectedBasis_mem
    (fun g ↦ Module.Free.chooseBasis F (piece g)) i

end Basis

section Tensor

variable {F A B Γ : Type*} [Field F] [Ring A] [Ring B]
  [Algebra F A] [Algebra F B] [AddCommMonoid Γ] [DecidableEq Γ]
  (pA : ℕ → Submodule F A) (pB : ℕ → Submodule F B)
  [GradedAlgebra pA] [GradedAlgebra pB]
  (qA : Γ → Submodule F A) (qB : Γ → Submodule F B)
  [GradedAlgebra qA] [GradedAlgebra qB]

def naturalMultigradedTensorPart (g : Γ) : Submodule F (pA ᵍ⊗[F] pB) :=
  basisDegreePart
    (gradedTensorBasis pA pB (multihomogeneousBasis qA) (multihomogeneousBasis qB))
    (fun ij ↦ ij.1.1+ij.2.1) g

theorem multigradedTensor_tmul_mem {g h : Γ} {a : A} {b : B}
    (ha : a∈qA g) (hb : b∈qB h) :
    (a ᵍ⊗ₜ[F] b : pA ᵍ⊗[F] pB)∈naturalMultigradedTensorPart pA pB qA qB (g+h) := by
  have hA := congrFun (basisDegreePart_eq_existing qA
    (multihomogeneousBasis qA) Sigma.fst (multihomogeneousBasis_mem qA)) g
  have hB := congrFun (basisDegreePart_eq_existing qB
    (multihomogeneousBasis qB) Sigma.fst (multihomogeneousBasis_mem qB)) h
  rw [←hA] at ha
  rw [←hB] at hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨ia,hia,rfl⟩ := ha
      change ia.1=g at hia
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ib,hib,rfl⟩ := hb
          change ib.1=h at hib
          apply Submodule.subset_span
          exact ⟨(ia,ib),by change ia.1+ib.1=g+h; rw [hia,hib],
            gradedTensorBasis_apply pA pB (multihomogeneousBasis qA)
              (multihomogeneousBasis qB) ia ib⟩
      | zero =>
          simp only [GradedTensorProduct.tmul,TensorProduct.tmul_zero,map_zero]
          exact Submodule.zero_mem _
      | add b c hb hc ihb ihc =>
          simp only [GradedTensorProduct.tmul,TensorProduct.tmul_add,map_add]
          exact Submodule.add_mem _ ihb ihc
      | smul r b hb ih =>
          simp only [GradedTensorProduct.tmul,TensorProduct.tmul_smul,map_smul]
          exact Submodule.smul_mem _ r ih
  | zero =>
      simp only [GradedTensorProduct.tmul,TensorProduct.zero_tmul,map_zero]
      exact Submodule.zero_mem _
  | add a c ha hc iha ihc =>
      simp only [GradedTensorProduct.tmul,TensorProduct.add_tmul,map_add]
      exact Submodule.add_mem _ iha ihc
  | smul r a ha ih =>
      simp only [GradedTensorProduct.tmul,TensorProduct.smul_tmul',map_smul]
      exact Submodule.smul_mem _ r ih

theorem naturalMultigradedTensorPart_eq_span (g : Γ) :
    naturalMultigradedTensorPart pA pB qA qB g=
      Submodule.span F {t : pA ᵍ⊗[F] pB |
        ∃ i j,i+j=g ∧ ∃ a∈qA i,∃ b∈qB j,t=a ᵍ⊗ₜ[F] b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro t ⟨⟨ia,ib⟩,hg,rfl⟩
    apply Submodule.subset_span
    exact ⟨ia.1,ib.1,hg,multihomogeneousBasis qA ia,multihomogeneousBasis_mem qA ia,
      multihomogeneousBasis qB ib,multihomogeneousBasis_mem qB ib,
      gradedTensorBasis_apply pA pB (multihomogeneousBasis qA)
        (multihomogeneousBasis qB) ia ib⟩
  · apply Submodule.span_le.mpr
    rintro t ⟨i,j,hij,a,ha,b,hb,rfl⟩
    change (a ᵍ⊗ₜ[F] b : pA ᵍ⊗[F] pB)∈naturalMultigradedTensorPart pA pB qA qB g
    simpa only [hij] using multigradedTensor_tmul_mem pA pB qA qB ha hb

variable (degree : Γ →+ ℕ)
  (hA : ∀ g,qA g≤pA (degree g)) (hB : ∀ g,qB g≤pB (degree g))

def naturalMultigradedTensorAlgebra :
    GradedAlgebra (naturalMultigradedTensorPart pA pB qA qB) :=
  basisDegreeGradedAlgebra
    (gradedTensorBasis pA pB (multihomogeneousBasis qA) (multihomogeneousBasis qB))
    (fun ij ↦ ij.1.1+ij.2.1)
    (by
      change (1 ᵍ⊗ₜ[F] 1 : pA ᵍ⊗[F] pB)∈_
      simpa only [zero_add, naturalMultigradedTensorPart] using
        multigradedTensor_tmul_mem pA pB qA qB
        (SetLike.one_mem_graded qA) (SetLike.one_mem_graded qB))
    (by
      rintro ⟨ia,ib⟩ ⟨ja,jb⟩
      simp only [gradedTensorBasis_apply]
      have hm :
          ((multihomogeneousBasis qA ia*multihomogeneousBasis qA ja) ᵍ⊗ₜ[F]
            (multihomogeneousBasis qB ib*multihomogeneousBasis qB jb) :
              pA ᵍ⊗[F] pB)∈
          naturalMultigradedTensorPart pA pB qA qB
            ((ia.1+ib.1)+(ja.1+jb.1)) := by
        simpa only [add_assoc,add_left_comm,add_comm] using
          multigradedTensor_tmul_mem pA pB qA qB
            (SetLike.mul_mem_graded (multihomogeneousBasis_mem qA ia)
              (multihomogeneousBasis_mem qA ja))
            (SetLike.mul_mem_graded (multihomogeneousBasis_mem qB ib)
              (multihomogeneousBasis_mem qB jb))
      have he := GradedTensorProduct.tmul_coe_mul_coe_tmul
        (𝒜 := pA) (ℬ := pB)
        (multihomogeneousBasis qA ia)
        (⟨multihomogeneousBasis qB ib,hB ib.1 (multihomogeneousBasis_mem qB ib)⟩ :
          pB (degree ib.1))
        (⟨multihomogeneousBasis qA ja,hA ja.1 (multihomogeneousBasis_mem qA ja)⟩ :
          pA (degree ja.1))
        (multihomogeneousBasis qB jb)
      rw [he]
      rw [@Units.smul_def _ _ (_) (_),←Int.cast_smul_eq_zsmul F]
      exact Submodule.smul_mem _ _ hm)

include hA hB in
theorem naturalMultigradedTensorPart_total (g : Γ) :
    naturalMultigradedTensorPart pA pB qA qB g≤
      naturalGradedTensorPart pA pB (degree g) := by
  rw [naturalMultigradedTensorPart_eq_span]
  apply Submodule.span_le.mpr
  rintro x ⟨i,j,hij,a,ha,b,hb,rfl⟩
  rw [←hij,map_add]
  exact naturalGradedTensorPart_tmul_mem pA pB (hA i ha) (hB j hb)

end Tensor

section Maps

variable {F A B C Γ : Type*} [Field F] [Ring A] [Ring B] [Ring C]
  [Algebra F A] [Algebra F B] [Algebra F C]
  [AddCommMonoid Γ] [DecidableEq Γ]
  (pA : ℕ → Submodule F A) (pB : ℕ → Submodule F B)
  [GradedAlgebra pA] [GradedAlgebra pB]
  (qA : Γ → Submodule F A) (qB : Γ → Submodule F B)
  [GradedAlgebra qA] [GradedAlgebra qB]

theorem multigradedTensor_includeLeft {g : Γ} {a : A} (ha : a∈qA g) :
    GradedTensorProduct.includeLeft pA pB a∈naturalMultigradedTensorPart pA pB qA qB g := by
  simpa only [GradedTensorProduct.includeLeft_apply,add_zero] using multigradedTensor_tmul_mem pA pB qA qB
    ha (SetLike.one_mem_graded qB)

theorem multigradedTensor_includeRight {g : Γ} {b : B} (hb : b∈qB g) :
    GradedTensorProduct.includeRight pA pB b∈naturalMultigradedTensorPart pA pB qA qB g := by
  simpa only [GradedTensorProduct.includeRight_apply,zero_add] using multigradedTensor_tmul_mem pA pB qA qB
    (SetLike.one_mem_graded qA) hb

theorem multigradedTensor_lift (qC : Γ → Submodule F C) [GradedAlgebra qC]
    (f : A →ₐ[F] C) (g : B →ₐ[F] C)
    (hf : ∀ i a,a∈qA i → f a∈qC i)
    (hg : ∀ i b,b∈qB i → g b∈qC i)
    (hcomm : ∀ ⦃i j⦄ (a : pA i) (b : pB j),
      f a*g b=(-1 : ℤˣ)^(j*i) • (g b*f a))
    {degree : Γ} {x : pA ᵍ⊗[F] pB}
    (hx : x∈naturalMultigradedTensorPart pA pB qA qB degree) :
    GradedTensorProduct.lift pA pB f g hcomm x∈qC degree := by
  rw [naturalMultigradedTensorPart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,j,hij,a,ha,b,hb,rfl⟩ := hx
      rw [GradedTensorProduct.lift_tmul,←hij]
      exact SetLike.mul_mem_graded (hf i a ha) (hg j b hb)
  | zero => simpa only [map_zero] using (qC degree).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih

end Maps
end PaperVerification.Fermion

