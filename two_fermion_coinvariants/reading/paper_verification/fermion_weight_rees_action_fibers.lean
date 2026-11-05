module

public import PaperVerification.FermionWeightReesEquivariant
public import PaperVerification.FermionWeightReesFibers

/-!
# Specialization of the coefficientwise Rees action

The action matrix in the actual Rees basis is obtained by homogenizing the
matrix in the original basis. Evaluation at one recovers the original action;
evaluation at zero keeps its equal-weight entries. This makes the fiber
intertwining assertion a statement about the literal tensor-product fibers.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators TensorProduct LaurentPolynomial
  PaperVerification.Fermion.WeightRees

namespace PaperVerification.Fermion.WeightRees

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (weight : I → ℕ) (hmul : Multiplicative b weight)
  (e : A ≃ₐ[K] A)
  (he : ∀ r x, e x ∈ BlockInitial.lowerSubmodule b weight r ↔
    x ∈ BlockInitial.lowerSubmodule b weight r)

def actionPolynomial (i j : I) : Polynomial K :=
  Polynomial.monomial (weight j-weight i) (b.repr (e (b i)) j)

include he in
theorem action_weight_le (i j : I) (hj : b.repr (e (b i)) j≠0) :
    weight i≤weight j := by
  have hi : b i∈BlockInitial.lowerSubmodule b weight (weight i) := by
    intro k hk
    by_cases hki : k=i
    · exact le_of_eq (congrArg weight hki.symm)
    · exact (hk (by simp only [Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hki])).elim
  exact ((he (weight i) (b i)).mpr hi) j hj

/-- Homogenizing the original action matrix gives its actual matrix in the
free Rees basis. The exponent is nonnegative by filtration preservation. -/
theorem filtrationEquiv_basis (i : I) :
    filtrationEquiv b weight hmul e he (basis b weight hmul i)=
      ∑ j, actionPolynomial b weight e i j • basis b weight hmul j := by
  apply Subtype.ext
  change parameterLaurentEquiv e (basis b weight hmul i : LaurentPolynomial A)=_
  rw [basis_coe]
  rw [show parameterLaurentEquiv e (shiftedBasisVector b weight i)=
      AddMonoidAlgebra.single (-(weight i : ℤ)) (e (b i)) from
    AddMonoidAlgebra.mapAlgHom_single _ _ _]
  change AddMonoidAlgebra.single (-(weight i : ℤ)) (e (b i))=
    (algebra b weight hmul).val
      (∑ j,actionPolynomial b weight e i j • basis b weight hmul j)
  rw [map_sum]
  simp only [map_smul,Subalgebra.val_apply,basis_coe]
  change (AddMonoidAlgebra.lsingle (R := K) (-(weight i : ℤ))) (e (b i))=_
  rw [←b.sum_repr (e (b i)),map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change AddMonoidAlgebra.single (-(weight i : ℤ))
    ((b.repr (e (b i)) j) • b j)=_
  rw [actionPolynomial,monomial_smul_shifted]
  by_cases hc : b.repr (e (b i)) j=0
  · simp only [hc,zero_smul,AddMonoidAlgebra.single_zero]
  · have hw := action_weight_le b weight e he i j hc
    have hexp : ((weight j-weight i : ℕ) : ℤ)-(weight j : ℤ)=-(weight i : ℤ) := by
      omega
    rw [hexp]

@[simp] theorem actionPolynomial_eval_one (i j : I) :
    (actionPolynomial b weight e i j).eval 1=b.repr (e (b i)) j := by
  simp only [actionPolynomial,Polynomial.eval_monomial,one_pow,mul_one]

include he in
theorem actionPolynomial_eval_zero (i j : I) :
    (actionPolynomial b weight e i j).eval 0=
      if weight j=weight i then b.repr (e (b i)) j else 0 := by
  by_cases hc : b.repr (e (b i)) j=0
  · simp only [actionPolynomial,hc,Polynomial.eval_monomial,zero_mul]
    split_ifs <;> rfl
  · have hw := action_weight_le b weight e he i j hc
    by_cases hij : weight j=weight i
    · simp only [actionPolynomial,hij,Nat.sub_self,Polynomial.eval_monomial,
        pow_zero,mul_one,ite_true]
    · have hd : weight j-weight i≠0 := by omega
      simp only [actionPolynomial,Polynomial.eval_monomial,zero_pow hd,mul_zero,
        if_neg hij]

section Fiber

variable {B : Type*} [Ring B] [Algebra K B] (c : K)
  (b₀ : Module.Basis I K B) (e₀ : B ≃ₐ[K] B)

/-- Scalar extension of the actual Rees automorphism, with the parameter
specialized to c. This is an algebra automorphism of the literal fiber. -/
def actionOnFiber :
    letI := scalarEvaluation c
    K ⊗[Polynomial K] algebra b weight hmul ≃ₐ[K]
      K ⊗[Polynomial K] algebra b weight hmul := by
  letI := scalarEvaluation c
  exact Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
    (filtrationEquiv b weight hmul e he)

@[simp] theorem actionOnFiber_tmul (s : K) (x : algebra b weight hmul) :
    letI := scalarEvaluation c
    actionOnFiber b weight hmul e he c (s ⊗ₜ[Polynomial K] x)=
      s ⊗ₜ[Polynomial K] filtrationEquiv b weight hmul e he x := by
  letI := scalarEvaluation c
  rfl

theorem evaluateLinear_equivariant
    (he₀ : ∀ i,e₀ (b₀ i)=
      ∑ j,(actionPolynomial b weight e i j).eval c • b₀ j)
    (x : algebra b weight hmul) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    evaluateLinear b weight hmul c b₀ (filtrationEquiv b weight hmul e he x)=
      e₀ (evaluateLinear b weight hmul c b₀ x) := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  have hgen (i : I) :
      evaluateLinear b weight hmul c b₀
        (filtrationEquiv b weight hmul e he (basis b weight hmul i))=
      e₀ (evaluateLinear b weight hmul c b₀ (basis b weight hmul i)) := by
    rw [filtrationEquiv_basis,map_sum,evaluateLinear_basis]
    simp only [map_smul,evaluateLinear_basis,evaluation_smul]
    exact (he₀ i).symm
  conv_lhs => rw [←(basis b weight hmul).sum_repr x,map_sum,map_sum]
  conv_rhs => rw [←(basis b weight hmul).sum_repr x,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul,evaluation_smul,hgen]

/-- Checking the actual target basis matrix is sufficient to prove that the
specified algebra identification intertwines the literal fiber action. -/
theorem fiberLinearEquiv_equivariant
    (he₀ : ∀ i,e₀ (b₀ i)=
      ∑ j,(actionPolynomial b weight e i j).eval c • b₀ j) :
    letI := scalarEvaluation c
    letI := targetEvaluation (B := B) c
    letI := evaluationTower (B := B) c
    ∀ z : K ⊗[Polynomial K] algebra b weight hmul,
    fiberLinearEquiv b weight hmul c b₀ (actionOnFiber b weight hmul e he c z)=
      e₀ (fiberLinearEquiv b weight hmul c b₀ z) := by
  letI := scalarEvaluation c
  letI := targetEvaluation (B := B) c
  letI := evaluationTower (B := B) c
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul s x =>
      rw [actionOnFiber_tmul,fiberLinearEquiv_tmul,fiberLinearEquiv_tmul,
        evaluateLinear_equivariant b weight hmul e he c b₀ e₀ he₀,map_smul]

end Fiber

/-- The original automorphism is recovered on the unit fiber, without any
additional premise on its matrix. -/
theorem fiberOne_equivariant :
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (1 : K)).toAlgebra
    ∀ z : K ⊗[Polynomial K] algebra b weight hmul,
      fiberOne b weight hmul (actionOnFiber b weight hmul e he 1 z)=
        e (fiberOne b weight hmul z) := by
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (1 : K)).toAlgebra
  intro z
  apply fiberLinearEquiv_equivariant b weight hmul e he 1 b e
  intro i
  simp only [actionPolynomial_eval_one]
  exact (b.sum_repr (e (b i))).symm

end PaperVerification.Fermion.WeightRees
