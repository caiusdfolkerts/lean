module

public import PaperVerification.FermionBasisGrading
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Natural grading of the genuine graded tensor product

Mathlib supplies the ring structure and its signed universal property. This
module supplies the missing total-degree grading by partitioning a tensor
product basis and proves that homogeneous pure tensors have the expected
degree. Over a field, homogeneous bases are obtained from the component
decompositions, so no extra freeness assumption is needed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct
variable {R A B I J : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (partA : ℕ → Submodule R A) (partB : ℕ → Submodule R B)
  [GradedAlgebra partA] [GradedAlgebra partB]
variable (bA : Module.Basis I R A) (bB : Module.Basis J R B)
  (degA : I → ℕ) (degB : J → ℕ)

def gradedTensorBasis : Module.Basis (I×J) R (partA ᵍ⊗[R] partB) :=
  (bA.tensorProduct bB).map (GradedTensorProduct.of R partA partB)

@[simp] theorem gradedTensorBasis_apply (i : I) (j : J) :
    gradedTensorBasis partA partB bA bB (i,j) =
      (bA i ᵍ⊗ₜ[R] bB j : partA ᵍ⊗[R] partB) := by
  simp only [gradedTensorBasis,Module.Basis.map_apply,Module.Basis.tensorProduct_apply]

def tensorBasisDegreePart (n : ℕ) : Submodule R (partA ᵍ⊗[R] partB) :=
  basisDegreePart (gradedTensorBasis partA partB bA bB)
    (fun ij : I×J ↦ degA ij.1+degB ij.2) n

variable (hbA : ∀ i,bA i∈partA (degA i))
  (hbB : ∀ j,bB j∈partB (degB j))

include hbA hbB in
theorem gradedTensor_homogeneous_tmul_mem {i j : ℕ} {a : A} {b : B}
    (ha : a∈partA i) (hb : b∈partB j) :
    (a ᵍ⊗ₜ[R] b : partA ᵍ⊗[R] partB)∈
      tensorBasisDegreePart partA partB bA bB degA degB (i+j) := by
  have hA := congrFun (basisDegreePart_eq_existing partA bA degA hbA) i
  have hB := congrFun (basisDegreePart_eq_existing partB bB degB hbB) j
  rw [←hA] at ha
  rw [←hB] at hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨ia,hia,rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ib,hib,rfl⟩ := hb
          apply Submodule.subset_span
          change degA ia = i at hia
          change degB ib = j at hib
          exact ⟨(ia,ib),by
            change degA ia + degB ib = i + j
            rw [hia,hib],gradedTensorBasis_apply partA partB bA bB ia ib⟩
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

def tensorBasisDegreeGradedAlgebra :
    GradedAlgebra (tensorBasisDegreePart partA partB bA bB degA degB) :=
  basisDegreeGradedAlgebra (gradedTensorBasis partA partB bA bB)
    (fun ij : I×J ↦ degA ij.1+degB ij.2)
    (by
      change (1 ᵍ⊗ₜ[R] 1 : partA ᵍ⊗[R] partB)∈_
      simpa only [Nat.zero_add, tensorBasisDegreePart] using
        gradedTensor_homogeneous_tmul_mem partA partB bA bB degA degB hbA hbB
          (SetLike.one_mem_graded partA) (SetLike.one_mem_graded partB))
    (by
      rintro ⟨ia,ib⟩ ⟨ja,jb⟩
      simp only [gradedTensorBasis_apply]
      have hm :
          ((bA ia*bA ja) ᵍ⊗ₜ[R] (bB ib*bB jb) : partA ᵍ⊗[R] partB)∈
            tensorBasisDegreePart partA partB bA bB degA degB
              ((degA ia+degB ib)+(degA ja+degB jb)) := by
        simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
          gradedTensor_homogeneous_tmul_mem partA partB bA bB degA degB hbA hbB
            (SetLike.mul_mem_graded (hbA ia) (hbA ja))
            (SetLike.mul_mem_graded (hbB ib) (hbB jb))
      have he := GradedTensorProduct.tmul_coe_mul_coe_tmul
        (𝒜 := partA) (ℬ := partB)
        (bA ia) (⟨bB ib,hbB ib⟩ : partB (degB ib))
        (⟨bA ja,hbA ja⟩ : partA (degA ja)) (bB jb)
      rw [he]
      rw [@Units.smul_def _ _ (_) (_),←Int.cast_smul_eq_zsmul R]
      exact Submodule.smul_mem _ _ hm)

section Field

variable {F C D : Type*} [Field F] [Ring C] [Ring D]
  [Algebra F C] [Algebra F D]
variable (pieceC : ℕ → Submodule F C) (pieceD : ℕ → Submodule F D)
  [GradedAlgebra pieceC] [GradedAlgebra pieceD]

def homogeneousBasis (piece : ℕ → Submodule F C) [GradedAlgebra piece] :
    Module.Basis (Σ n,Module.Free.ChooseBasisIndex F (piece n)) F C :=
  (DirectSum.Decomposition.isInternal piece).collectedBasis
    (fun n ↦ Module.Free.chooseBasis F (piece n))

theorem homogeneousBasis_mem (piece : ℕ → Submodule F C) [GradedAlgebra piece]
    (i : Σ n,Module.Free.ChooseBasisIndex F (piece n)) :
    homogeneousBasis piece i∈piece i.1 :=
  (DirectSum.Decomposition.isInternal piece).collectedBasis_mem
    (fun n ↦ Module.Free.chooseBasis F (piece n)) i

def naturalGradedTensorPart (n : ℕ) : Submodule F (pieceC ᵍ⊗[F] pieceD) :=
  tensorBasisDegreePart pieceC pieceD (homogeneousBasis pieceC) (homogeneousBasis pieceD)
    Sigma.fst Sigma.fst n

def naturalGradedTensorAlgebra : GradedAlgebra (naturalGradedTensorPart pieceC pieceD) :=
  tensorBasisDegreeGradedAlgebra pieceC pieceD
    (homogeneousBasis pieceC) (homogeneousBasis pieceD) Sigma.fst Sigma.fst
    (homogeneousBasis_mem pieceC) (homogeneousBasis_mem pieceD)

theorem naturalGradedTensorPart_tmul_mem {i j : ℕ} {c : C} {d : D}
    (hc : c∈pieceC i) (hd : d∈pieceD j) :
    (c ᵍ⊗ₜ[F] d : pieceC ᵍ⊗[F] pieceD)∈naturalGradedTensorPart pieceC pieceD (i+j) :=
  gradedTensor_homogeneous_tmul_mem pieceC pieceD
    (homogeneousBasis pieceC) (homogeneousBasis pieceD) Sigma.fst Sigma.fst
    (homogeneousBasis_mem pieceC) (homogeneousBasis_mem pieceD) hc hd

/-- An intrinsic description shows that the grading does not depend on the
chosen homogeneous bases: it is exactly the span of pure tensors with the
specified total degree. -/
theorem naturalGradedTensorPart_eq_span (n : ℕ) :
    naturalGradedTensorPart pieceC pieceD n=
      Submodule.span F {t : pieceC ᵍ⊗[F] pieceD |
        ∃ i j,i+j=n ∧ ∃ c∈pieceC i,∃ d∈pieceD j,t=c ᵍ⊗ₜ[F] d} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro t ⟨⟨ic,id⟩,hdegree,rfl⟩
    apply Submodule.subset_span
    exact ⟨ic.1,id.1,hdegree,homogeneousBasis pieceC ic,homogeneousBasis_mem pieceC ic,
      homogeneousBasis pieceD id,homogeneousBasis_mem pieceD id,
      gradedTensorBasis_apply pieceC pieceD (homogeneousBasis pieceC)
        (homogeneousBasis pieceD) ic id⟩
  · apply Submodule.span_le.mpr
    rintro t ⟨i,j,hij,c,hc,d,hd,rfl⟩
    change (c ᵍ⊗ₜ[F] d : pieceC ᵍ⊗[F] pieceD) ∈
      naturalGradedTensorPart pieceC pieceD n
    rw [← hij]
    exact naturalGradedTensorPart_tmul_mem pieceC pieceD hc hd

end Field
end PaperVerification.Fermion
