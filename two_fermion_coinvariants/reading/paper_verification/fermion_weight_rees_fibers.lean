module

public import PaperVerification.FermionWeightRees
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual algebra fibers of the Laurent Rees family

A specified target basis whose multiplication is the evaluation of the
actual Rees structure constants induces an algebra equivalence from the
literal tensor-product fiber. At one these identities are the multiplication
and unit identities of the original algebra, so that fiber is proved here
without any additional premise. At zero the corresponding identities must
be established in the actual initial quotient before this transfer is used.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.WeightRees

open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (weight : I → ℕ) (hmul : Multiplicative b weight)

include hmul in
theorem multiplicationPolynomial_eval_zero (i j k : I) :
    (multiplicationPolynomial b weight i j k).eval 0=
      if weight k=weight i+weight j then b.repr (b i*b j) k else 0 := by
  classical
  by_cases hc : b.repr (b i*b j) k=0
  · simp only [multiplicationPolynomial,hc,Polynomial.eval_monomial,zero_mul]
    split_ifs <;> rfl
  · have hw := hmul i j k hc
    by_cases he : weight k=weight i+weight j
    · simp only [multiplicationPolynomial,he,Nat.sub_self,Polynomial.eval_monomial,
        pow_zero,mul_one,ite_true]
    · have hd : weight k-(weight i+weight j)≠0 := by omega
      simp only [multiplicationPolynomial,Polynomial.eval_monomial,zero_pow hd,mul_zero,
        if_neg he]

theorem unitPolynomial_eval_zero (i : I) :
    (Polynomial.monomial (weight i) (b.repr 1 i)).eval 0=
      if weight i=0 then b.repr 1 i else 0 := by
  classical
  by_cases hw : weight i=0
  · simp only [hw,Polynomial.eval_monomial,pow_zero,mul_one,ite_true]
  · simp only [Polynomial.eval_monomial,zero_pow hw,mul_zero,if_neg hw]

section Fiber

variable {B : Type*} [Ring B] [Algebra K B] (c : K) (b₀ : Module.Basis I K B)

/-- The specified scalar specialization; kept explicit in every fiber type. -/
def scalarEvaluation (c : K) : Algebra (Polynomial K) K :=
  (Polynomial.evalRingHom c).toAlgebra

/-- The target module structure induced by the same scalar specialization. -/
def targetEvaluation (c : K) : Algebra (Polynomial K) B :=
  ((algebraMap K B).comp (Polynomial.evalRingHom c)).toAlgebra'
    (fun p x ↦ Algebra.commutes (p.eval c) x)

def evaluationTower (c : K) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    IsScalarTower (Polynomial K) K B := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  exact IsScalarTower.of_algebraMap_eq (fun p ↦ rfl)

theorem evaluation_smul (p : Polynomial K) (x : B) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    p • x=p.eval c • x := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  rw [Algebra.smul_def,Algebra.smul_def]
  rfl

def evaluateLinear :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    algebra b weight hmul →ₗ[Polynomial K] B := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  exact (basis b weight hmul).constr (Polynomial K) b₀

@[simp] theorem evaluateLinear_basis (i : I) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    evaluateLinear b weight hmul c b₀ (basis b weight hmul i)=b₀ i := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  exact (basis b weight hmul).constr_basis (Polynomial K) _ i

theorem evaluateLinear_one
    (hone : (1 : B)=∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)).eval c • b₀ i) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    evaluateLinear b weight hmul c b₀ 1=1 := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  rw [basis_unit_expansion,map_sum]
  simp only [map_smul,evaluateLinear_basis,evaluation_smul]
  exact hone.symm

theorem evaluateLinear_mul
    (hmul₀ : ∀ i j,b₀ i*b₀ j=
      ∑ k,(multiplicationPolynomial b weight i j k).eval c • b₀ k)
    (x y : algebra b weight hmul) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    evaluateLinear b weight hmul c b₀ (x*y)=
      evaluateLinear b weight hmul c b₀ x*evaluateLinear b weight hmul c b₀ y := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  let E := evaluateLinear b weight hmul c b₀
  have hgen (i j : I) : E (basis b weight hmul i*basis b weight hmul j)=
      E (basis b weight hmul i)*E (basis b weight hmul j) := by
    rw [basis_mul,map_sum]
    simp only [E,map_smul,evaluateLinear_basis,evaluation_smul]
    exact (hmul₀ i j).symm
  have hx : x∈Submodule.span (Polynomial K) (Set.range (basis b weight hmul)) := by
    rw [(basis b weight hmul).span_eq]
    trivial
  have hy : y∈Submodule.span (Polynomial K) (Set.range (basis b weight hmul)) := by
    rw [(basis b weight hmul).span_eq]
    trivial
  have hright (i : I) : E (basis b weight hmul i*y)=E (basis b weight hmul i)*E y := by
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨j,rfl⟩ := hz; exact hgen i j
    | zero => simp only [mul_zero,map_zero]
    | add z t hz ht ihz iht => simp only [mul_add,map_add,ihz,iht]
    | smul p z hz ih => simp only [mul_smul_comm,map_smul,ih]
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i,rfl⟩ := hz; exact hright i
  | zero => simp only [zero_mul,map_zero]
  | add z t hz ht ihz iht => simp only [add_mul,map_add,ihz,iht]
  | smul p z hz ih => simp only [smul_mul_assoc,map_smul,ih]

def fiberLinearEquiv :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    K ⊗[Polynomial K] algebra b weight hmul ≃ₗ[K] B := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  exact ((basis b weight hmul).baseChange K).equiv b₀ (Equiv.refl I)

@[simp] theorem fiberLinearEquiv_basis (i : I) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    fiberLinearEquiv b weight hmul c b₀ (1 ⊗ₜ[Polynomial K] basis b weight hmul i)=b₀ i := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  rw [←Module.Basis.baseChange_apply,fiberLinearEquiv,Module.Basis.equiv_apply]
  rfl

theorem fiberLinearEquiv_eq_lift :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    (fiberLinearEquiv b weight hmul c b₀).toLinearMap=
      (evaluateLinear b weight hmul c b₀).liftBaseChange K := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  apply ((basis b weight hmul).baseChange K).ext
  intro i
  simp only [Module.Basis.baseChange_apply,LinearEquiv.coe_coe,fiberLinearEquiv_basis,
    LinearMap.liftBaseChange_tmul,evaluateLinear_basis,one_smul]

@[simp] theorem fiberLinearEquiv_tmul (s : K) (x : algebra b weight hmul) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    fiberLinearEquiv b weight hmul c b₀ (s ⊗ₜ[Polynomial K] x)=
      s • evaluateLinear b weight hmul c b₀ x := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  change (fiberLinearEquiv b weight hmul c b₀).toLinearMap (s ⊗ₜ[Polynomial K] x)=_
  rw [fiberLinearEquiv_eq_lift,LinearMap.liftBaseChange_tmul]

theorem fiberLinearEquiv_one
    (hone : (1 : B)=∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)).eval c • b₀ i) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    fiberLinearEquiv b weight hmul c b₀ 1=1 := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  rw [Algebra.TensorProduct.one_def,fiberLinearEquiv_tmul,one_smul,
    evaluateLinear_one b weight hmul c b₀ hone]

theorem fiberLinearEquiv_mul
    (hmul₀ : ∀ i j,b₀ i*b₀ j=
      ∑ k,(multiplicationPolynomial b weight i j k).eval c • b₀ k) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    ∀ x y : K ⊗[Polynomial K] algebra b weight hmul,
    fiberLinearEquiv b weight hmul c b₀ (x*y)=
      fiberLinearEquiv b weight hmul c b₀ x*fiberLinearEquiv b weight hmul c b₀ y := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero]
  | add x x' hx hx' => simp only [add_mul,map_add,hx,hx']
  | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero,map_zero]
      | add y y' hy hy' => simp only [mul_add,map_add,hy,hy']
      | tmul t y =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [fiberLinearEquiv_tmul,evaluateLinear_mul b weight hmul c b₀ hmul₀,
            smul_mul_smul_comm]

/-- The conclusion is an algebra equivalence from the literal tensor fiber. -/
def fiberAlgEquiv
    (hone : (1 : B)=∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)).eval c • b₀ i)
    (hmul₀ : ∀ i j,b₀ i*b₀ j=
      ∑ k,(multiplicationPolynomial b weight i j k).eval c • b₀ k) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    K ⊗[Polynomial K] algebra b weight hmul ≃ₐ[K] B := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  exact AlgEquiv.ofLinearEquiv (fiberLinearEquiv b weight hmul c b₀)
    (fiberLinearEquiv_one b weight hmul c b₀ hone)
    (fiberLinearEquiv_mul b weight hmul c b₀ hmul₀)

@[simp] theorem fiberAlgEquiv_basis
    (hone : (1 : B)=∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)).eval c • b₀ i)
    (hmul₀ : ∀ i j,b₀ i*b₀ j=
      ∑ k,(multiplicationPolynomial b weight i j k).eval c • b₀ k) (i : I) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    fiberAlgEquiv b weight hmul c b₀ hone hmul₀
      (1 ⊗ₜ[Polynomial K] basis b weight hmul i)=b₀ i := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  exact fiberLinearEquiv_basis b weight hmul c b₀ i

end Fiber

def fiberOne :
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (1 : K)).toAlgebra
    K ⊗[Polynomial K] algebra b weight hmul ≃ₐ[K] A := by
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (1 : K)).toAlgebra
  apply fiberAlgEquiv b weight hmul 1 b
  · simpa only [Polynomial.eval_monomial,one_pow,mul_one] using (b.sum_repr (1 : A)).symm
  · intro i j
    simpa only [multiplicationPolynomial,Polynomial.eval_monomial,one_pow,mul_one] using
      (b.sum_repr (b i*b j)).symm

end PaperVerification.Fermion.WeightRees
