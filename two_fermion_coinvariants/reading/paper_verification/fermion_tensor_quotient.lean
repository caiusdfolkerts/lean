module

public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of genuine two-sided algebra quotients

The coefficient algebra is commutative; the algebra being quotiented need not be.
This distinction is needed for the exterior algebra presentations in Theorem 7.2.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion

section QuotientUniversal

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B]

theorem ringCon_le_ker_of_kills (I : TwoSidedIdeal A) (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a = 0) : I.ringCon ≤ RingCon.ker f.toRingHom := by
  intro a b hab
  change f a = f b
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hf (a - b) ((I.rel_iff a b).mp hab)

theorem quotientMk_eq_zero_of_mem (I : TwoSidedIdeal A) (a : A) (ha : a ∈ I) :
    I.ringCon.mkₐ R a = 0 := by
  have h : I.ringCon.mkₐ R a = I.ringCon.mkₐ R 0 :=
    Quotient.sound ha
  simpa using h

theorem twoSided_map_killed (I : TwoSidedIdeal A) (f : A →+* B)
    (g : B →+* C) (h : ∀ a ∈ I, g (f a) = 0) :
    ∀ b ∈ TwoSidedIdeal.map f I, g b = 0 := by
  have hle : TwoSidedIdeal.map f I ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker g) := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change g (f a) = g 0
    simpa using h a ha
  intro b hb
  have hzero := hle hb
  change g b = g 0 at hzero
  simpa using hzero

end QuotientUniversal

section TensorQuotient

variable (R S A : Type*) [CommRing R] [CommRing S] [Ring A]
  [Algebra R S] [Algebra R A]

def tensorTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal (S ⊗[R] A) :=
  TwoSidedIdeal.map
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom I

abbrev TensorTwoSidedQuotient (I : TwoSidedIdeal A) :=
  (tensorTwoSidedIdeal R S A I).ringCon.Quotient

variable {R S A}

def tensorQuotientRight (I : TwoSidedIdeal A) :
    I.ringCon.Quotient →ₐ[R] TensorTwoSidedQuotient R S A I := by
  let f : A →ₐ[R] TensorTwoSidedQuotient R S A I :=
    (((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
  exact I.ringCon.liftₐ f (ringCon_le_ker_of_kills I f (by
    intro a ha
    change (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (1 ⊗ₜ[R] a)=0
    exact quotientMk_eq_zero_of_mem (R := S) (tensorTwoSidedIdeal R S A I) _
      (TwoSidedIdeal.subset_span ⟨a,ha,rfl⟩)))

def tensorQuotientForward (I : TwoSidedIdeal A) :
    S ⊗[R] I.ringCon.Quotient →ₐ[S] TensorTwoSidedQuotient R S A I :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (tensorQuotientRight I)
    (fun s a ↦ Algebra.commutes s _)

@[simp] theorem tensorQuotientForward_tmul_mk (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorQuotientForward (R := R) (S := S) I (s ⊗ₜ[R] I.ringCon.mkₐ R a) =
      (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a) := by
  let q : S ⊗[R] A →ₐ[S] TensorTwoSidedQuotient R S A I :=
    (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S
  change algebraMap S (TensorTwoSidedQuotient R S A I) s * q (1 ⊗ₜ[R] a)=q (s ⊗ₜ[R] a)
  rw [←q.commutes s,←map_mul]
  congr 1
  simp [Algebra.TensorProduct.algebraMap_apply]

def tensorQuotientRawBackward (I : TwoSidedIdeal A) :
    S ⊗[R] A →ₐ[S] S ⊗[R] I.ringCon.Quotient :=
  Algebra.TensorProduct.map (AlgHom.id S S) (I.ringCon.mkₐ R)

def tensorQuotientBackward (I : TwoSidedIdeal A) :
    TensorTwoSidedQuotient R S A I →ₐ[S] S ⊗[R] I.ringCon.Quotient :=
  (tensorTwoSidedIdeal R S A I).ringCon.liftₐ (tensorQuotientRawBackward I)
    (ringCon_le_ker_of_kills _ _ <|
      twoSided_map_killed I
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
        (tensorQuotientRawBackward I).toRingHom fun a ha ↦ by
          simp [tensorQuotientRawBackward, quotientMk_eq_zero_of_mem I a ha])

@[simp] theorem tensorQuotientBackward_mk_tmul (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorQuotientBackward (R := R) (S := S) I
      ((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)) =
      s ⊗ₜ[R] I.ringCon.mkₐ R a := rfl

/-- Base change commutes with a genuine two-sided quotient, with no flatness
assumption and no commutativity assumption on the algebra being quotiented. -/
def tensorTwoSidedQuotientEquiv (I : TwoSidedIdeal A) :
    S ⊗[R] I.ringCon.Quotient ≃ₐ[S] TensorTwoSidedQuotient R S A I :=
  AlgEquiv.ofAlgHom (tensorQuotientForward I) (tensorQuotientBackward I)
    (by
      apply RingCon.Quotient.hom_extₐ
      apply Algebra.TensorProduct.ext'
      intro s a
      change tensorQuotientForward I
        (tensorQuotientBackward I ((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)))=
          (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)
      rw [tensorQuotientBackward_mk_tmul,tensorQuotientForward_tmul_mk])
    (by
      apply Algebra.TensorProduct.ext'
      intro s q
      obtain ⟨a, rfl⟩ := I.ringCon.mk'_surjective q
      change tensorQuotientBackward I
        (tensorQuotientForward I (s ⊗ₜ[R] I.ringCon.mkₐ R a))=s ⊗ₜ[R] I.ringCon.mkₐ R a
      rw [tensorQuotientForward_tmul_mk,tensorQuotientBackward_mk_tmul])

@[simp] theorem tensorTwoSidedQuotientEquiv_tmul_mk (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorTwoSidedQuotientEquiv (R := R) (S := S) I
      (s ⊗ₜ[R] I.ringCon.mkₐ R a) =
      (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a) :=
  tensorQuotientForward_tmul_mk I s a

end TensorQuotient

end PaperVerification.Fermion
