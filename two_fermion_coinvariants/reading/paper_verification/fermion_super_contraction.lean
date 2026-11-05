module

public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionExterior
public import PaperVerification.FermionTwistedDerivation
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Actual odd contraction on the polynomial/exterior tensor algebra

The operator is the tensor extension of exterior contraction. Its square,
parity-twisted Leibniz rule, polynomial linearity, and anticommutator with
creation are proved in the original ambient algebra.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

def superParity : SuperRing R n →ₐ[R] SuperRing R n :=
  Algebra.TensorProduct.map (AlgHom.id R (PolynomialRing R n))
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm R (OddModule R n))))

def superContraction (l : Module.Dual R (OddModule R n)) : Module.End R (SuperRing R n) :=
  TensorProduct.map (LinearMap.id : Module.End R (PolynomialRing R n)) (Exterior.annihilation l)

@[simp] theorem superParity_tmul (p : PolynomialRing R n)
    (w : ExteriorAlgebra R (OddModule R n)) :
    superParity (p ⊗ₜ[R] w)=p ⊗ₜ[R] CliffordAlgebra.involute w := by
  rw [superParity,Algebra.TensorProduct.map_tmul,AlgHom.id_apply]

@[simp] theorem superContraction_tmul (l : Module.Dual R (OddModule R n))
    (p : PolynomialRing R n) (w : ExteriorAlgebra R (OddModule R n)) :
    superContraction l (p ⊗ₜ[R] w)=p ⊗ₜ[R] Exterior.annihilation l w := by
  rw [superContraction,TensorProduct.map_tmul,LinearMap.id_apply]

theorem superParity_involutive : Function.Involutive (superParity (R := R) (n := n)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p w => rw [superParity_tmul,superParity_tmul,CliffordAlgebra.involute_involute]
  | add x y hx hy => simp only [map_add,hx,hy]

@[simp] theorem superContraction_one (l : Module.Dual R (OddModule R n)) :
    superContraction l (1 : SuperRing R n)=0 := by
  rw [Algebra.TensorProduct.one_def,superContraction_tmul,
    Exterior.annihilation_one,TensorProduct.tmul_zero]

theorem superContraction_square (l : Module.Dual R (OddModule R n)) :
    superContraction l*superContraction l=0 := by
  apply LinearMap.ext
  intro x
  change superContraction l (superContraction l x)=0
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p w =>
      rw [superContraction_tmul,superContraction_tmul]
      have h : Exterior.annihilation l (Exterior.annihilation l w)=0 :=
        LinearMap.congr_fun (Exterior.annihilation_square l) w
      rw [h,TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add,hx,hy,add_zero]

theorem superContraction_mul (l : Module.Dual R (OddModule R n)) (x y : SuperRing R n) :
    superContraction l (x*y)=superContraction l x*y+superParity x*superContraction l y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero,zero_add]
  | tmul p u =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero,map_zero,add_zero]
      | tmul q v =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul,superContraction_tmul,superParity_tmul]
          have h : Exterior.annihilation l (u*v)=Exterior.annihilation l u*v+
              CliffordAlgebra.involute u*Exterior.annihilation l v :=
            CliffordAlgebra.contractLeft_mul l u v
          rw [h,TensorProduct.tmul_add]
      | add y z hy hz => simp only [mul_add,map_add,hy,hz]; abel
  | add x z hx hz => simp only [add_mul,map_add,hx,hz]; abel

theorem superContraction_polynomial_smul (l : Module.Dual R (OddModule R n))
    (p : PolynomialRing R n) (x : SuperRing R n) :
    superContraction l (p • x)=p • superContraction l x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero,map_zero]
  | tmul q v => simp only [TensorProduct.smul_tmul',superContraction_tmul]
  | add x y hx hy => simp only [smul_add,map_add,hx,hy]

theorem superParity_polynomial_smul (p : PolynomialRing R n) (x : SuperRing R n) :
    superParity (p • x)=p • superParity x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero,map_zero]
  | tmul q v => simp only [TensorProduct.smul_tmul',superParity_tmul]
  | add x y hx hy => simp only [smul_add,map_add,hx,hy]

def superOdd (v : OddModule R n) : SuperRing R n :=
  Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι R v)

@[simp] theorem superContraction_odd (l : Module.Dual R (OddModule R n))
    (v : OddModule R n) : superContraction l (superOdd v)=(l v) • (1 : SuperRing R n) := by
  simp only [superOdd,Algebra.TensorProduct.includeRight_apply,superContraction_tmul,
    Exterior.annihilation,CliffordAlgebra.contractLeft_ι,Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul,←Algebra.TensorProduct.one_def]

@[simp] theorem superParity_odd (v : OddModule R n) :
    superParity (superOdd v)=-superOdd v := by
  simp only [superOdd,Algebra.TensorProduct.includeRight_apply,superParity_tmul,
    CliffordAlgebra.involute_ι,TensorProduct.tmul_neg]

theorem superOdd_sq (v : OddModule R n) : superOdd v*superOdd v=0 := by
  rw [superOdd,←map_mul,ExteriorAlgebra.ι_sq_zero,map_zero]

/-- Odd normality in the original algebra, retaining the parity automorphism. -/
theorem superOdd_normal (v : OddModule R n) (x : SuperRing R n) :
    x*superOdd v=superOdd v*superParity x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero,mul_zero]
  | tmul p w =>
      simp only [superOdd,Algebra.TensorProduct.includeRight_apply,superParity_tmul,
        Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      have h := ExteriorAlgebra.ι_mul_eq_involute_mul v (CliffordAlgebra.involute w)
      rw [CliffordAlgebra.involute_involute] at h
      exact congrArg (fun z ↦ p ⊗ₜ[R] z) h.symm
  | add x y hx hy => simp only [add_mul,map_add,mul_add,hx,hy]

theorem superContraction_creation (l : Module.Dual R (OddModule R n))
    (v : OddModule R n) :
    superContraction l*LinearMap.mulLeft R (superOdd v)+
      LinearMap.mulLeft R (superOdd v)*superContraction l=(l v) • 1 := by
  apply LinearMap.ext
  intro x
  change superContraction l (superOdd v*x)+superOdd v*superContraction l x=(l v) • x
  rw [superContraction_mul,superContraction_odd,superParity_odd,
    smul_mul_assoc,one_mul]
  have hneg : -superOdd v * superContraction l x =
      -(superOdd v * superContraction l x) :=
    neg_mul (superOdd v) (superContraction l x)
  rw [hneg]
  abel

/-- The unweighted total xi contraction used by the strict-family split. -/
def strictXiFunctional : Module.Dual R (OddModule R n) where
  toFun v := ∑ i,v (Sum.inr i)
  map_add' x y := by simp only [Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]

def strictXiVector (β : Fin n → R) : OddModule R n := fun j ↦
  match j with
  | .inl _ => 0
  | .inr i => β i

@[simp] theorem strictXiFunctional_vector (β : Fin n → R) :
    strictXiFunctional (strictXiVector β)=∑ i,β i := rfl

@[simp] theorem strictXiFunctional_theta (i : Fin n) :
    strictXiFunctional (Pi.single (Sum.inl i) (1 : R))=0 := by
  simp [strictXiFunctional,Pi.single_apply]

@[simp] theorem strictXiFunctional_xi (i : Fin n) :
    strictXiFunctional (Pi.single (Sum.inr i) (1 : R))=1 := by
  simp [strictXiFunctional,Pi.single_apply]

@[simp] theorem strictXiContraction_theta (i : Fin n) :
    superContraction strictXiFunctional (theta R n i)=0 := by
  change superContraction strictXiFunctional (superOdd (Pi.single (Sum.inl i) 1))=0
  rw [superContraction_odd,strictXiFunctional_theta,zero_smul]

@[simp] theorem strictXiContraction_xi (i : Fin n) :
    superContraction strictXiFunctional (xi R n i)=1 := by
  change superContraction (strictXiFunctional (R := R) (n := n))
    (superOdd (Pi.single (Sum.inr i) (1 : R))) = (1 : SuperRing R n)
  rw [superContraction_odd,strictXiFunctional_xi,one_smul]

@[simp] theorem superParity_theta (i : Fin n) : superParity (theta R n i)=-theta R n i :=
  superParity_odd (Pi.single (Sum.inl i) 1)

@[simp] theorem superParity_xi (i : Fin n) : superParity (xi R n i)=-xi R n i :=
  superParity_odd (Pi.single (Sum.inr i) 1)

end PaperVerification.Fermion
