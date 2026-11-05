module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Grading an actual surjective algebra image

A homogeneous kernel descends the direct-sum decomposition. The construction
uses the actual image submodules under a surjective algebra map, including
noncommutative algebra quotients. It introduces no assumed decomposition of
the target and no assumption of flatness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)

def gradedImagePart (n : Γ) : Submodule R B := (part n).map q.toLinearMap

def gradedImageComponent (n : Γ) :
    part n →ₗ[R] gradedImagePart part q n :=
  (q.toLinearMap.comp (part n).subtype).codRestrict _
    (fun a ↦ ⟨a,a.property,rfl⟩)

def gradedImageDecomposeSource :
    A →ₗ[R] ⨁ n,gradedImagePart part q n :=
  (DirectSum.lmap (gradedImageComponent part q)).comp
    (DirectSum.decomposeLinearEquiv part).toLinearMap

@[simp] theorem gradedImageDecomposeSource_coe (n : Γ) (a : part n) :
    gradedImageDecomposeSource part q (a : A)=
      DirectSum.lof R Γ (gradedImagePart part q ·) n
        (gradedImageComponent part q n a) := by
  simp only [gradedImageDecomposeSource,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,DirectSum.decomposeLinearEquiv_apply_coe,DirectSum.lmap_lof]

theorem gradedImageDecomposeSource_recompose (a : A) :
    DirectSum.coeLinearMap (gradedImagePart part q)
      (gradedImageDecomposeSource part q a)=q a := by
  have hcomm :
      (DirectSum.coeLinearMap (gradedImagePart part q)).comp
        (DirectSum.lmap (gradedImageComponent part q)) =
      q.toLinearMap.comp (DirectSum.coeLinearMap part) := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply,DirectSum.lmap_lof,DirectSum.coeLinearMap_lof]
    rfl
  change ((DirectSum.coeLinearMap (gradedImagePart part q)).comp
    (DirectSum.lmap (gradedImageComponent part q)))
      (DirectSum.decomposeLinearEquiv part a)=_
  rw [hcomm]
  change q ((DirectSum.decomposeLinearEquiv part).symm
    (DirectSum.decomposeLinearEquiv part a))=q a
  rw [LinearEquiv.symm_apply_apply]

variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)

include hker in
theorem gradedImageDecomposeSource_ker :
    LinearMap.ker q.toLinearMap ≤ LinearMap.ker (gradedImageDecomposeSource part q) := by
  intro a ha
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  change q (GradedAlgebra.proj part n a)=0
  exact hker n a ha

set_option maxHeartbeats 800000 in
def gradedImageDecompose (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    B →ₗ[R] ⨁ n, gradedImagePart part q n := by
  let descended : (A ⧸ LinearMap.ker q.toLinearMap) →ₗ[R]
      (⨁ n, gradedImagePart part q n) :=
    (LinearMap.ker q.toLinearMap).liftQ
      (R₂ := R) (M₂ := ⨁ n, gradedImagePart part q n) (τ₁₂ := RingHom.id R)
      (gradedImageDecomposeSource part q)
      (gradedImageDecomposeSource_ker part q hker)
  let quotientEquiv : (A ⧸ LinearMap.ker q.toLinearMap) ≃ₗ[R] B :=
    q.toLinearMap.quotKerEquivOfSurjective hq
  exact descended.comp quotientEquiv.symm.toLinearMap

@[simp] theorem gradedImageDecompose_q (a : A) :
    gradedImageDecompose part q hq hker (q a)=gradedImageDecomposeSource part q a := by
  simp only [gradedImageDecompose,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap]
  have he : (q.toLinearMap.quotKerEquivOfSurjective hq).symm (q a) =
      Submodule.Quotient.mk a :=
    LinearMap.quotKerEquivOfSurjective_symm_apply q.toLinearMap hq a
  rw [he,Submodule.liftQ_apply]

def gradedImageDecomposition (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    DirectSum.Decomposition (gradedImagePart part q) := by
  exact DirectSum.Decomposition.ofLinearMap (gradedImagePart part q)
    (gradedImageDecompose part q hq hker)
    (by
      apply LinearMap.ext
      intro b
      obtain ⟨a,rfl⟩ := hq b
      simp only [LinearMap.comp_apply,gradedImageDecompose_q,
        gradedImageDecomposeSource_recompose,LinearMap.id_apply])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      rintro ⟨b,hb⟩
      obtain ⟨a,ha,rfl⟩ := hb
      simp only [LinearMap.comp_apply,DirectSum.coeLinearMap_lof,LinearMap.id_apply]
      change gradedImageDecompose part q hq hker (q a) =
        DirectSum.lof R Γ (gradedImagePart part q ·) n
          (gradedImageComponent part q n ⟨a,ha⟩)
      rw [gradedImageDecompose_q]
      exact gradedImageDecomposeSource_coe part q n ⟨a,ha⟩)

instance gradedImageGradedMonoid :
    SetLike.GradedMonoid (gradedImagePart part q) where
  one_mem := ⟨1,SetLike.one_mem_graded part,map_one q⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    exact ⟨x*y,SetLike.mul_mem_graded hx hy,map_mul q x y⟩

/-- The image grading is genuine: multiplication and the unique direct-sum
decomposition are both constructed from the source grading. -/
def gradedImageAlgebra (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    GradedAlgebra (gradedImagePart part q) where
  toGradedMonoid := gradedImageGradedMonoid part q
  toDecomposition := gradedImageDecomposition part q hq hker

section RestrictScalars

variable {S C : Type*} [CommRing S] [Ring C] [Algebra R S]
  [Algebra S C] [Algebra R C] [IsScalarTower R S C]
variable (piece : Γ → Submodule S C) [GradedAlgebra piece]

def restrictGradedPart (n : Γ) : Submodule R C := (piece n).restrictScalars R

/-- Restricting the coefficient ring leaves the actual homogeneous subspaces
and their unique additive decomposition unchanged. -/
def restrictGradedAlgebra : GradedAlgebra (restrictGradedPart (R := R) piece) :=
  inferInstanceAs (GradedAlgebra (fun n ↦ (piece n).restrictScalars R))

end RestrictScalars

end PaperVerification.Fermion
