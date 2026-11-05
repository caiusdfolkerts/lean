module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.Abel

/-!
# A quotient supported in one homogeneous component

An idempotent projection that preserves a relation subspace identifies the
quotient by its kernel and that subspace with the projected part of the original
quotient. No finite-dimensionality or choice of a basis is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.ProjectionQuotient

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem projected_quotient_kernel (π : V →ₗ[K] V)
    (hπ : ∀ v, π (π v) = π v) (U : Submodule K V)
    (hU : ∀ v ∈ U, π v ∈ U) :
    LinearMap.ker (U.mkQ.comp π) = LinearMap.ker π ⊔ U := by
  ext v
  change U.mkQ (π v) = 0 ↔ v ∈ LinearMap.ker π ⊔ U
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hv
    apply Submodule.mem_sup.mpr
    refine ⟨v - π v, ?_, π v, hv, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hπ, sub_self]
    · abel
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, LinearMap.mem_ker.mp hx, zero_add]
    exact hU y hy

def projectedQuotientEquiv (π : V →ₗ[K] V)
    (hπ : ∀ v, π (π v) = π v) (U : Submodule K V)
    (hU : ∀ v ∈ U, π v ∈ U) :
    (V ⧸ (LinearMap.ker π ⊔ U)) ≃ₗ[K] LinearMap.range (U.mkQ.comp π) :=
  (Submodule.quotEquivOfEq _ _ (projected_quotient_kernel π hπ U hU).symm).trans
    (U.mkQ.comp π).quotKerEquivRange

theorem projectedQuotientEquiv_mk (π : V →ₗ[K] V)
    (hπ : ∀ v, π (π v) = π v) (U : Submodule K V)
    (hU : ∀ v ∈ U, π v ∈ U) (v : V) :
    ((projectedQuotientEquiv π hπ U hU)
      ((LinearMap.ker π ⊔ U).mkQ v) : V ⧸ U) = U.mkQ (π v) := rfl

end PaperVerification.ProjectionQuotient
