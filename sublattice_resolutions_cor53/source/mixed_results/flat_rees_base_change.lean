module
public import mixed_results.part001
public import graph_foundation.part011
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.Polynomial.AlgebraMap

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FlatReesBaseChange -/
section

/-! # Flat base change of the literal Rees algebra

The coefficient in degree `m` is the actual ideal power `I^m`.
Tensoring its direct-sum decomposition and applying the flat ideal
identification gives a bijection. Its multiplication is checked on
homogeneous coefficient elements, where it is ordinary multiplication.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.FlatReesBaseChange
open Classical
open scoped TensorProduct DirectSum
variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]
local instance : DecidableEq ℕ := fun a b => Classical.propDecidable (a = b)

def powerPiece (I : Ideal S) (m : ℕ) : Submodule S S := I^m

theorem powerPiece_one (I : Ideal S) : (1 : S)∈powerPiece I 0 := by
  simp [powerPiece]

theorem powerPiece_mul (I : Ideal S) (m n : ℕ) (x : S) (hx : x∈powerPiece I m)
    (y : S) (hy : y∈powerPiece I n) : x*y∈powerPiece I (m+n) := by
  change x*y∈I^(m+n)
  rw [pow_add]
  exact Ideal.mul_mem_mul hx hy

abbrev coefficients (I : Ideal S) :=
  gradedCoefficientAlgebra (powerPiece I) (powerPiece_one I) (powerPiece_mul I)

def polynomialEquiv (I : Ideal S) : coefficients I ≃ₐ[S] reesAlgebra I where
  toFun x := ⟨Polynomial.ofFinsupp x.val,x.property⟩
  invFun x := ⟨x.val.toFinsupp,x.property⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Polynomial.eta x.val)
  map_add' _ _ := Subtype.ext Polynomial.ofFinsupp_add
  map_mul' x y := Subtype.ext (Polynomial.ofFinsupp_mul x.val y.val)
  commutes' r := Subtype.ext (Polynomial.ofFinsupp_algebraMap r)

def single (I : Ideal S) (m : ℕ) : powerPiece I m →ₗ[S] coefficients I :=
  coefficientSingle (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m

theorem single_mul (I : Ideal S) (m n : ℕ) (x : powerPiece I m) (y : powerPiece I n) :
    single I m x*single I n y=
      single I (m+n) ⟨x.val*y.val,powerPiece_mul I m n _ x.property _ y.property⟩ := by
  apply Subtype.ext
  exact AddMonoidAlgebra.single_mul_single m n x.val y.val

theorem single_zero_one (I : Ideal S) : single I 0 ⟨1,powerPiece_one I⟩=1 := by
  apply Subtype.ext
  rfl

def decomposition (I : Ideal S) : coefficients I ≃ₗ[S] (Π₀m : ℕ,powerPiece I m) :=
  gradedCoefficientDFinsuppEquiv (powerPiece I) (powerPiece_one I) (powerPiece_mul I)

@[simp] theorem decomposition_single (I : Ideal S) (m : ℕ) (x : powerPiece I m) :
    decomposition I (single I m x)=DFinsupp.single m x :=
  gradedCoefficientToDFinsupp_single (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m x

@[simp] theorem decomposition_symm_single (I : Ideal S) (m : ℕ) (x : powerPiece I m) :
    (decomposition I).symm (DFinsupp.single m x)=single I m x :=
  gradedCoefficientDFinsuppEquiv_symm_single (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m x

/-- Projection onto the literal auxiliary degree `m`; it is linear over
the entire coefficient ring. -/
def projection (I : Ideal S) (m : ℕ) : coefficients I →ₗ[S] coefficients I :=
  (single I m).comp (coefficientAt (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m)

@[simp] theorem projection_single (I : Ideal S) (m n : ℕ) (x : powerPiece I n) :
    projection I m (single I n x)=if n=m then single I n x else 0 := by
  by_cases h : n=m
  · subst n
    rw [if_pos rfl]
    change single I m (coefficientAt (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m
      (single I m x))=single I m x
    congr 1
    apply Subtype.ext
    exact Finsupp.single_eq_same
  · rw [if_neg h]
    apply Subtype.ext
    change AddMonoidAlgebra.single m ((AddMonoidAlgebra.single n x.val).coeff m)=0
    rw [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_of_ne' h,AddMonoidAlgebra.single_zero]

 theorem projection_idempotent (I : Ideal S) (m : ℕ) (x : coefficients I) :
    projection I m (projection I m x)=projection I m x := by
  change projection I m (single I m _)=_
  rw [projection_single,if_pos rfl]
  rfl

variable [Module.Flat S R] (I : Ideal S)
local notation "J" => I.map (algebraMap S R)

def powerEquiv (m : ℕ) : (R ⊗[S] powerPiece I m) ≃ₗ[R] powerPiece J m :=
  (FlatIdealBaseChange.equiv (I^m)).trans
    (LinearEquiv.ofEq _ _ (by change Ideal.map _ (I^m)=J^m; rw [Ideal.map_pow]))

@[simp] theorem powerEquiv_tmul (m : ℕ) (r : R) (x : powerPiece I m) :
    (powerEquiv I m (r ⊗ₜ[S] x)).val=r*algebraMap S R x.val :=
  FlatIdealBaseChange.equiv_tmul (I^m) r x

def linearEquiv : (R ⊗[S] coefficients I) ≃ₗ[R] coefficients J :=
  (LinearEquiv.baseChange S R (coefficients I) (Π₀m : ℕ,powerPiece I m)
    (decomposition I)).trans
    ((TensorProduct.directSumRight S R R (fun m : ℕ => ↥(powerPiece I m))).trans
      ((DFinsupp.mapRange.linearEquiv (powerEquiv I)).trans (decomposition J).symm))

@[simp] theorem linearEquiv_tmul_single (r : R) (m : ℕ) (x : powerPiece I m) :
    linearEquiv I (r ⊗ₜ[S] single I m x)=single J m (powerEquiv I m (r ⊗ₜ[S] x)) := by
  simp only [linearEquiv,LinearEquiv.trans_apply,LinearEquiv.baseChange_tmul,
    decomposition_single]
  change (decomposition J).symm
    (DFinsupp.mapRange.linearEquiv (powerEquiv I)
      (TensorProduct.directSumRight S R R (fun m : ℕ => ↥(powerPiece I m))
        (r ⊗ₜ[S] DirectSum.lof S ℕ (fun m => ↥(powerPiece I m)) m x)))=_
  rw [TensorProduct.directSumRight_tmul_lof]
  simp only [DFinsupp.mapRange.linearEquiv_apply]
  change (decomposition J).symm
    (DFinsupp.mapRange (fun i x => powerEquiv I i x) _
      (DFinsupp.single m (r ⊗ₜ[S] x))) = _
  rw [DFinsupp.mapRange_single, decomposition_symm_single]

theorem linearEquiv_one : linearEquiv (R := R) I 1=1 := by
  change linearEquiv I ((1 : R) ⊗ₜ[S] (1 : coefficients I))=1
  rw [← single_zero_one I,linearEquiv_tmul_single]
  have he : powerEquiv I 0 ((1 : R) ⊗ₜ[S] ⟨1,powerPiece_one I⟩)=
      ⟨1,powerPiece_one J⟩ := by
    apply Subtype.ext
    rw [powerEquiv_tmul,map_one,one_mul]
  rw [he,single_zero_one]

theorem linearEquiv_mul_single (r s : R) (m n : ℕ)
    (x : powerPiece I m) (y : powerPiece I n) :
    linearEquiv I ((r ⊗ₜ[S] single I m x)*(s ⊗ₜ[S] single I n y))=
      linearEquiv I (r ⊗ₜ[S] single I m x)*linearEquiv I (s ⊗ₜ[S] single I n y) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,single_mul,linearEquiv_tmul_single,
    linearEquiv_tmul_single,linearEquiv_tmul_single,single_mul]
  congr 1
  apply Subtype.ext
  simp only [powerEquiv_tmul,map_mul]
  ring

theorem linearEquiv_mul (x y : R ⊗[S] coefficients I) :
    linearEquiv I (x*y)=linearEquiv I x*linearEquiv I y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero]
  | add x z hx hz => simp only [add_mul,map_add,hx,hz]
  | tmul r a =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero,map_zero]
      | add y z hy hz => simp only [mul_add,map_add,hy,hz]
      | tmul s b =>
          have ha := (coefficient_decomposition (powerPiece I)
            (powerPiece_one I) (powerPiece_mul I) a).symm
          have hb := (coefficient_decomposition (powerPiece I)
            (powerPiece_one I) (powerPiece_mul I) b).symm
          rw [ha,hb]
          simp only [TensorProduct.tmul_sum,map_sum,Finset.sum_mul,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          exact linearEquiv_mul_single (R := R) I r s n m
            (coefficientAt (powerPiece I) (powerPiece_one I) (powerPiece_mul I) n a)
            (coefficientAt (powerPiece I) (powerPiece_one I) (powerPiece_mul I) m b)

/-- The flat identification retains each auxiliary coefficient degree. -/
theorem linearEquiv_projection (m : ℕ) (z : R ⊗[S] coefficients I) :
    linearEquiv I (((projection I m).lTensor R) z)=
      projection J m (linearEquiv I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul r a =>
      have ha := (coefficient_decomposition (powerPiece I)
        (powerPiece_one I) (powerPiece_mul I) a).symm
      rw [ha]
      simp only [TensorProduct.tmul_sum,map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      change linearEquiv I (r ⊗ₜ[S] projection I m (single I n _))=
        projection J m (linearEquiv I (r ⊗ₜ[S] single I n _))
      rw [projection_single,linearEquiv_tmul_single,projection_single]
      by_cases h : n=m
      · rw [if_pos h,if_pos h,linearEquiv_tmul_single]
      · rw [if_neg h,if_neg h,TensorProduct.tmul_zero,map_zero]

/-- The flat base-change equivalence retains the literal multiplication. -/
def algebraEquiv : (R ⊗[S] coefficients I) ≃ₐ[R] coefficients J :=
  AlgEquiv.ofLinearEquiv (linearEquiv I) (linearEquiv_one I) (linearEquiv_mul I)

/-- The same equivalence for Mathlib's conventional polynomial Rees algebras. -/
def standardAlgebraEquiv : (R ⊗[S] reesAlgebra I) ≃ₐ[R] reesAlgebra J :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (polynomialEquiv I).symm).trans
    ((algebraEquiv I).trans (polynomialEquiv J))

end FourPapers.FlatReesBaseChange

end
end
end

end
