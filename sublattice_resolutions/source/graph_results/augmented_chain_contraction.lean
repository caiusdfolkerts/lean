module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Exact.Basic

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.AugmentedChainContraction -/
section

/-!
# Split augmented chain complexes and arbitrary base change

These are actual linear maps on every chain group, with separate degree-zero
and positive-degree contraction identities. Tensoring the identities proves
exactness over every coefficient algebra, including nonflat ones.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers

open scoped TensorProduct

variable (R : Type*) [CommRing R]
  (C : ℕ → Type*) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
  (M : Type*) [AddCommGroup M] [Module R M]

structure AugmentedChainContraction where
  d : ∀ p, C (p+1) →ₗ[R] C p
  augmentation : C 0 →ₗ[R] M
  homotopy : ∀ p, C p →ₗ[R] C (p+1)
  sectionMap : M →ₗ[R] C 0
  square : ∀ p, (d p).comp (d (p+1)) = 0
  augmentation_boundary : augmentation.comp (d 0) = 0
  retract : augmentation.comp sectionMap = LinearMap.id
  contraction_zero : (d 0).comp (homotopy 0) = LinearMap.id - sectionMap.comp augmentation
  contraction_succ : ∀ p,
    (d (p+1)).comp (homotopy (p+1)) + (homotopy p).comp (d p) = LinearMap.id

namespace AugmentedChainContraction

variable {R C M}
  (A : AugmentedChainContraction R C M)

theorem augmentation_surjective : Function.Surjective A.augmentation := by
  intro m
  exact ⟨A.sectionMap m, LinearMap.congr_fun A.retract m⟩

theorem boundary_of_augmentation_zero (x : C 0) (hx : A.augmentation x = 0) :
    A.d 0 (A.homotopy 0 x) = x := by
  have he := LinearMap.congr_fun A.contraction_zero x
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hx, map_zero, sub_zero] using he

theorem boundary_of_cycle (p : ℕ) (x : C (p+1)) (hx : A.d p x = 0) :
    A.d (p+1) (A.homotopy (p+1) x) = x := by
  have he := LinearMap.congr_fun (A.contraction_succ p) x
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    hx, map_zero, add_zero] using he

theorem exact_augmentation : Function.Exact (A.d 0) A.augmentation := by
  intro x
  constructor
  · intro hx
    exact ⟨A.homotopy 0 x, A.boundary_of_augmentation_zero x hx⟩
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun A.augmentation_boundary y

theorem exact_positive (p : ℕ) : Function.Exact (A.d (p+1)) (A.d p) := by
  intro x
  constructor
  · intro hx
    exact ⟨A.homotopy (p+1) x, A.boundary_of_cycle p x hx⟩
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (A.square p) y

variable (T : Type*) [CommRing T] [Algebra R T]

/-- All actual chain and augmentation identities survive arbitrary scalar
extension. The new coefficient algebra need not be flat. -/
def baseChange : AugmentedChainContraction T (fun p => T ⊗[R] C p) (T ⊗[R] M) where
  d p := (A.d p).baseChange T
  augmentation := A.augmentation.baseChange T
  homotopy p := (A.homotopy p).baseChange T
  sectionMap := A.sectionMap.baseChange T
  square p := by
    rw [← LinearMap.baseChange_comp, A.square p, LinearMap.baseChange_zero]
  augmentation_boundary := by
    rw [← LinearMap.baseChange_comp, A.augmentation_boundary, LinearMap.baseChange_zero]
  retract := by
    rw [← LinearMap.baseChange_comp, A.retract, LinearMap.baseChange_id]
  contraction_zero := by
    rw [← LinearMap.baseChange_comp, A.contraction_zero, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, LinearMap.baseChange_comp]
  contraction_succ p := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, A.contraction_succ p, LinearMap.baseChange_id]

theorem baseChange_exact_augmentation :
    Function.Exact ((A.d 0).baseChange T) (A.augmentation.baseChange T) :=
  (A.baseChange T).exact_augmentation

theorem baseChange_exact_positive (p : ℕ) :
    Function.Exact ((A.d (p+1)).baseChange T) ((A.d p).baseChange T) :=
  (A.baseChange T).exact_positive p

theorem baseChange_augmentation_surjective :
    Function.Surjective (A.augmentation.baseChange T) :=
  (A.baseChange T).augmentation_surjective

end AugmentedChainContraction
end FourPapers

end
end
end


end
