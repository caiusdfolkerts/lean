module

public import PaperVerification.FermionTensorQuotient
public import PaperVerification.FermionDiagonalExterior
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change of finite exterior presentations

The tensor coefficient is commutative, while the exterior factor and the
quotients are allowed to be noncommutative.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Classical

namespace PaperVerification.Fermion

def exteriorLinearEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
    (ExteriorAlgebra.map e.symm.toLinearMap)
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by
        ext x
        exact e.apply_symm_apply x
      rw [h,ExteriorAlgebra.map_id])
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by
        ext x
        exact e.symm_apply_apply x
      rw [h,ExteriorAlgebra.map_id])

@[simp] theorem exteriorLinearEquiv_ι {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (m : M) :
    exteriorLinearEquiv e (ExteriorAlgebra.ι R m)=ExteriorAlgebra.ι R (e m) :=
  ExteriorAlgebra.map_apply_ι _ _

def finiteExteriorBaseChange (R S ι : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Fintype ι] :
    S ⊗[R] ExteriorAlgebra R (ι → R) ≃ₐ[S] ExteriorAlgebra S (ι → S) :=
  (ExteriorAlgebra.baseChangeEquiv R (ι → R) S).trans
    (exteriorLinearEquiv (TensorProduct.piScalarRight R S S ι))

@[simp] theorem finiteExteriorBaseChange_generator
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι]
    (s : S) (i : ι) :
    finiteExteriorBaseChange R S ι (s ⊗ₜ[R] exteriorGenerator (A := R) i)=
      s • exteriorGenerator (A := S) i := by
  rw [finiteExteriorBaseChange,AlgEquiv.trans_apply,exteriorGenerator,
    ExteriorAlgebra.baseChangeEquiv_apply,exteriorLinearEquiv_ι,
    TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]
  have h : (fun j : ι ↦ ((Pi.single i (1:R) : ι → R) j) • s)=
      s • (Pi.single i (1:S) : ι → S) := by
    funext j
    by_cases hij : j=i
    · subst j; simp
    · simp [Pi.single_apply,hij,Ne.symm hij]
  rw [h,map_smul]
  rfl

/-- Scalar-base cancellation generalized to a noncommutative final factor. -/
def noncommCancelBaseChange (R P S E : Type*) [CommRing R] [CommRing P]
    [CommRing S] [Ring E] [Algebra R P] [Algebra R S] [Algebra P S]
    [IsScalarTower R P S] [Algebra R E] :
    S ⊗[P] (P ⊗[R] E) ≃ₐ[S] S ⊗[R] E :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R P S S E).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

@[simp] theorem noncommCancelBaseChange_tmul
    {R P S E : Type*} [CommRing R] [CommRing P] [CommRing S] [Ring E]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S] [Algebra R E]
    (s : S) (p : P) (e : E) :
    noncommCancelBaseChange R P S E (s ⊗ₜ[P] (p ⊗ₜ[R] e))=(p • s) ⊗ₜ[R] e :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R P S s e p

def scalarExteriorBaseChange (R P S ι : Type*) [CommRing R] [CommRing P]
    [CommRing S] [Algebra R P] [Algebra R S] [Algebra P S]
    [IsScalarTower R P S] [Fintype ι] :
    S ⊗[P] (P ⊗[R] ExteriorAlgebra R (ι → R)) ≃ₐ[S]
      ExteriorAlgebra S (ι → S) :=
  (noncommCancelBaseChange R P S _).trans (finiteExteriorBaseChange R S ι)

@[simp] theorem scalarExteriorBaseChange_generator
    {R P S ι : Type*} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S] [Fintype ι]
    (s : S) (p : P) (i : ι) :
    scalarExteriorBaseChange R P S ι
      (s ⊗ₜ[P] (p ⊗ₜ[R] exteriorGenerator (A := R) i))=
      (p • s) • exteriorGenerator (A := S) i := by
  rw [scalarExteriorBaseChange,AlgEquiv.trans_apply,
    noncommCancelBaseChange_tmul,finiteExteriorBaseChange_generator]

section QuotientCongruence

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- A concrete algebra equivalence descends when both literal ideals map
into one another. The two inverse laws are checked on quotient representatives. -/
def twoSidedQuotientEquiv (e : A ≃ₐ[R] B)
    (I : TwoSidedIdeal A) (J : TwoSidedIdeal B)
    (he : ∀ a∈I,e a∈J) (hei : ∀ b∈J,e.symm b∈I) :
    I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient := by
  let qI : A →ₐ[R] I.ringCon.Quotient := I.ringCon.mkₐ R
  let qJ : B →ₐ[R] J.ringCon.Quotient := J.ringCon.mkₐ R
  let f : I.ringCon.Quotient →ₐ[R] J.ringCon.Quotient :=
    I.ringCon.liftₐ (qJ.comp e.toAlgHom)
      (ringCon_le_ker_of_kills I (qJ.comp e.toAlgHom) (by
        intro a ha
        exact quotientMk_eq_zero_of_mem (R := R) J (e a) (he a ha)))
  let g : J.ringCon.Quotient →ₐ[R] I.ringCon.Quotient :=
    J.ringCon.liftₐ (qI.comp e.symm.toAlgHom)
      (ringCon_le_ker_of_kills J (qI.comp e.symm.toAlgHom) (by
        intro b hb
        exact quotientMk_eq_zero_of_mem (R := R) I (e.symm b) (hei b hb)))
  exact AlgEquiv.ofAlgHom f g
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro b
      change qJ (e (e.symm b))=qJ b
      rw [AlgEquiv.apply_symm_apply])
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro a
      change qI (e.symm (e a))=qI a
      rw [AlgEquiv.symm_apply_apply])

@[simp] theorem twoSidedQuotientEquiv_mk
    (e : A ≃ₐ[R] B) (I : TwoSidedIdeal A) (J : TwoSidedIdeal B)
    (he : ∀ a∈I,e a∈J) (hei : ∀ b∈J,e.symm b∈I) (a : A) :
    twoSidedQuotientEquiv e I J he hei (I.ringCon.mkₐ R a)=J.ringCon.mkₐ R (e a) := rfl

end QuotientCongruence

def twoSidedQuotientEquivOfEq {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {I J : TwoSidedIdeal A} (h : I=J) : I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient := by
  subst J
  exact AlgEquiv.refl

@[simp] theorem twoSidedQuotientEquivOfEq_mk
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {I J : TwoSidedIdeal A} (h : I=J) (x : A) :
    twoSidedQuotientEquivOfEq (R := R) h (I.ringCon.mkₐ R x)=J.ringCon.mkₐ R x := by
  subst J
  rfl

end PaperVerification.Fermion

