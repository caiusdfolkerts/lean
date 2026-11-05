module

public import TauCeti.RingTheory.Semisimple.Multiplicity
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Prod
public import Lean.Elab.Tactic.Omega

/-!
# Reconstruction from Hom lower bounds and equal dimension

Over a finite-dimensional semisimple algebra, every left ideal has a
complement in the regular module. The dimensions of Hom from the two
complements add to the dimension of the target. Thus lower bounds for all
left-ideal Hom spaces, together with equal target dimension, force equality
for each one. The proved arbitrary-field multiplicity reconstruction then
gives an actual module isomorphism. No splitting field is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SemisimpleHomComparison

variable {K A M N : Type*} [Field K] [Ring A] [Algebra K A]
  [Module.Finite K A] [IsSemisimpleRing A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] [Module.Finite K M]
  [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N] [Module.Finite K N]

theorem hom_finrank_add_of_complement (S T : Submodule A A) (hST : IsCompl S T) :
    Module.finrank K (S →ₗ[A] M) + Module.finrank K (T →ₗ[A] M) = Module.finrank K M := by
  letI : Module.Finite K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  letI : Module.Finite K T :=
    Module.Finite.of_injective (T.subtype.restrictScalars K) Subtype.val_injective
  letI : Module.Finite K (S →ₗ[A] M) := Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ K A S M K) (LinearMap.restrictScalars_injective K)
  letI : Module.Finite K (T →ₗ[A] M) := Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ K A T M K) (LinearMap.restrictScalars_injective K)
  let e : ((S →ₗ[A] M) × (T →ₗ[A] M)) ≃ₗ[K] M :=
    (LinearMap.coprodEquiv K).trans
      ((LinearEquiv.congrLeft M K (S.prodEquivOfIsCompl T hST)).trans
        (LinearMap.ringLmapEquivSelf A K M))
  have h := e.finrank_eq
  rw [Module.finrank_prod] at h
  exact h

/-- Lower bounds for every left-ideal Hom space become equalities when the
two finite modules have equal dimension. -/
theorem hom_finrank_eq_of_le_of_finrank_eq
    (hle : ∀ S : Submodule A A, Module.finrank K (S →ₗ[A] M) ≤ Module.finrank K (S →ₗ[A] N))
    (hdim : Module.finrank K M = Module.finrank K N) (S : Submodule A A) :
    Module.finrank K (S →ₗ[A] M) = Module.finrank K (S →ₗ[A] N) := by
  obtain ⟨T,hT⟩ := exists_isCompl S
  have hM := hom_finrank_add_of_complement (K := K) (M := M) S T hT
  have hN := hom_finrank_add_of_complement (K := K) (M := N) S T hT
  have hS := hle S
  have hT' := hle T
  omega

/-- The actual original-field semisimple reconstruction used in the
power-tail representation theorem. -/
theorem nonempty_linearEquiv_of_hom_finrank_le_of_finrank_eq
    (hle : ∀ S : Submodule A A, Module.finrank K (S →ₗ[A] M) ≤ Module.finrank K (S →ₗ[A] N))
    (hdim : Module.finrank K M = Module.finrank K N) : Nonempty (M ≃ₗ[A] N) := by
  letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite K A M
  letI : Module.Finite A N := Module.Finite.of_restrictScalars_finite K A N
  apply TauCeti.nonempty_linearEquiv_of_finrank_linearMap_eq (k := K)
  intro S hS
  exact hom_finrank_eq_of_le_of_finrank_eq hle hdim S

end PaperVerification.SemisimpleHomComparison
