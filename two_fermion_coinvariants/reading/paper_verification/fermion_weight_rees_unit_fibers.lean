module

public import PaperVerification.FermionWeightReesActionFibers
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Every unit fiber of the actual weighted Rees algebra

The target basis is the original basis multiplied by the inverse weight powers
of the specialization parameter. The actual Rees structure constants therefore
evaluate to the original product, and the same cancellation intertwines every
filtration-preserving original action. No generic-fiber assertion is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.WeightRees

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]

def unitWeightScale (c : Kˣ) (r : ℕ) : K := ((c^r)⁻¹ : Kˣ)

theorem unitWeightScale_cancel (c : Kˣ) (r : ℕ) :
    (c : K)^r*unitWeightScale c r=1 := by
  simpa only [unitWeightScale,Units.val_pow_eq_pow_val] using (c^r).mul_inv

theorem unitWeightScale_add (c : Kˣ) (r s : ℕ) :
    unitWeightScale c (r+s)=unitWeightScale c r*unitWeightScale c s := by
  simp only [unitWeightScale,pow_add,mul_inv_rev,Units.val_mul]
  exact mul_comm _ _

theorem unitWeightScale_sub (c : Kˣ) (r s : ℕ) (h : s≤r) :
    (c : K)^(r-s)*unitWeightScale c r=unitWeightScale c s := by
  have hu : c^(r-s)*(c^r)⁻¹=(c^s)⁻¹ := by
    rw [pow_sub c h,mul_right_comm,mul_inv_cancel,one_mul]
  simpa only [unitWeightScale,Units.val_mul,Units.val_pow_eq_pow_val] using
    congrArg (fun u : Kˣ ↦ (u : K)) hu

variable (b : Module.Basis I K A) (weight : I → ℕ)

/-- The independently rescaled original basis at a unit parameter. -/
def unitFiberBasis (c : Kˣ) : Module.Basis I K A :=
  b.unitsSMul (fun i ↦ (c^(weight i))⁻¹)

@[simp] theorem unitFiberBasis_apply (c : Kˣ) (i : I) :
    unitFiberBasis b weight c i=unitWeightScale c (weight i) • b i := by
  rw [unitFiberBasis,Module.Basis.unitsSMul_apply,Units.smul_def]
  rfl

theorem unitFiberBasis_one (c : Kˣ) :
    (1 : A)=∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)).eval (c : K) •
      unitFiberBasis b weight c i := by
  calc
    (1 : A)=∑ i,b.repr 1 i • b i := (b.sum_repr 1).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [unitFiberBasis_apply,Polynomial.eval_monomial,smul_smul,
        mul_assoc,unitWeightScale_cancel,mul_one]

theorem unitFiberBasis_mul (hmul : Multiplicative b weight) (c : Kˣ) (i j : I) :
    unitFiberBasis b weight c i*unitFiberBasis b weight c j=
      ∑ k,(multiplicationPolynomial b weight i j k).eval (c : K) •
        unitFiberBasis b weight c k := by
  rw [unitFiberBasis_apply,unitFiberBasis_apply,smul_mul_smul_comm]
  conv_lhs => rw [←b.sum_repr (b i*b j)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hc : b.repr (b i*b j) k=0
  · simp only [hc,zero_smul,smul_zero,multiplicationPolynomial,
      Polynomial.eval_monomial,zero_mul]
  · rw [unitFiberBasis_apply,multiplicationPolynomial,Polynomial.eval_monomial,
      smul_smul,smul_smul]
    congr 1
    calc
      (unitWeightScale c (weight i)*unitWeightScale c (weight j))*
          b.repr (b i*b j) k=
        b.repr (b i*b j) k*unitWeightScale c (weight i+weight j) := by
          rw [unitWeightScale_add]
          ring
      _=(b.repr (b i*b j) k*(c : K)^(weight k-(weight i+weight j)))*
          unitWeightScale c (weight k) := by
        rw [mul_assoc,unitWeightScale_sub c _ _ (hmul i j k hc)]

variable (hmul : Multiplicative b weight)

/-- Every unit specialization is the original algebra, with its original product. -/
def fiberUnit (c : Kˣ) :
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (c : K)).toAlgebra
    K ⊗[Polynomial K] algebra b weight hmul ≃ₐ[K] A := by
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (c : K)).toAlgebra
  exact fiberAlgEquiv b weight hmul (c : K) (unitFiberBasis b weight c)
    (unitFiberBasis_one b weight c) (unitFiberBasis_mul b weight hmul c)

variable (e : A ≃ₐ[K] A)
  (he : ∀ r x,e x∈BlockInitial.lowerSubmodule b weight r ↔
    x∈BlockInitial.lowerSubmodule b weight r)

include he in
theorem unitFiberBasis_action (c : Kˣ) (i : I) :
    e (unitFiberBasis b weight c i)=
      ∑ j,(actionPolynomial b weight e i j).eval (c : K) •
        unitFiberBasis b weight c j := by
  rw [unitFiberBasis_apply,map_smul]
  conv_lhs => rw [←b.sum_repr (e (b i))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : b.repr (e (b i)) j=0
  · simp only [hc,zero_smul,smul_zero,actionPolynomial,Polynomial.eval_monomial,zero_mul]
  · rw [unitFiberBasis_apply,actionPolynomial,Polynomial.eval_monomial,
      smul_smul,smul_smul]
    congr 1
    rw [mul_assoc,unitWeightScale_sub c _ _ (action_weight_le b weight e he i j hc)]
    exact mul_comm _ _

/-- The identification at every unit parameter intertwines the actual action. -/
theorem fiberUnit_equivariant (c : Kˣ) :
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (c : K)).toAlgebra
    ∀ z : K ⊗[Polynomial K] algebra b weight hmul,
      fiberUnit b weight hmul c (actionOnFiber b weight hmul e he (c : K) z)=
        e (fiberUnit b weight hmul c z) := by
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (c : K)).toAlgebra
  intro z
  exact fiberLinearEquiv_equivariant b weight hmul e he (c : K)
    (unitFiberBasis b weight c) e (unitFiberBasis_action b weight e he c) z

end PaperVerification.Fermion.WeightRees
