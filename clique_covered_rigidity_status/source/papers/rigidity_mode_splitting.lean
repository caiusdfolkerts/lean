module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Separating actual local stress modes

This is the finite-dimensional algebra behind equation (7).  The modes
and their coefficient functionals are specified as actual vectors and
linear maps.  The two support assumptions say exactly which modes are
present in a prefix and which coefficients vanish there.  No dimension
identity or direct-sum assertion is assumed.
-/

noncomputable section
namespace Papers.Rigidity.ModeSplitting

open scoped Classical BigOperators

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Module.Finite K M] [Fintype I]

/-- The common kernel of the displayed coefficient functionals. -/
def nullModes (ρ : I → M →ₗ[K] K) : Submodule K M where
  carrier := {x | ∀ i, ρ i x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simp [hx i, hy i]
  smul_mem' := by
    intro c x hx i
    simp [hx i]

@[simp] theorem mem_nullModes (ρ : I → M →ₗ[K] K) (x : M) :
    x ∈ nullModes ρ ↔ ∀ i, ρ i x = 0 := Iff.rfl

/-- Coefficients of the modes available in one prefix. -/
def prefixCoefficients (P : Submodule K M) (ρ : I → M →ₗ[K] K)
    (A : Finset I) : P →ₗ[K] (A → K) :=
  LinearMap.pi fun i => (ρ i.val).comp P.subtype

@[simp] theorem prefixCoefficients_apply (P : Submodule K M)
    (ρ : I → M →ₗ[K] K) (A : Finset I) (x : P) (i : A) :
    prefixCoefficients P ρ A x i = ρ i.val x.val := rfl

/-- Biorthogonal actual modes supply every available coefficient tuple. -/
theorem prefixCoefficients_surjective (P : Submodule K M)
    (ρ : I → M →ₗ[K] K) (s : I → M) (A : Finset I)
    (hdual : ∀ i j, ρ i (s j) = if i = j then 1 else 0)
    (hmem : ∀ i ∈ A, s i ∈ P) :
    Function.Surjective (prefixCoefficients P ρ A) := by
  intro c
  let x : P := ∑ j : A, c j • (⟨s j.val, hmem j.val j.property⟩ : P)
  refine ⟨x, ?_⟩
  ext i
  simp [x, hdual]

/-- Vanishing of the available coefficients is the full mode kernel,
because all unavailable coefficients vanish on the prefix already. -/
def prefixKernelEquiv (P : Submodule K M) (ρ : I → M →ₗ[K] K)
    (A : Finset I)
    (habsent : ∀ x ∈ P, ∀ i ∉ A, ρ i x = 0) :
    (prefixCoefficients P ρ A).ker ≃ₗ[K] ↥(P ⊓ nullModes ρ) where
  toFun x := ⟨x.val.val, x.val.property, by
    intro i
    by_cases hi : i ∈ A
    · exact congrFun (LinearMap.mem_ker.mp x.property) ⟨i, hi⟩
    · exact habsent x.val.val x.val.property i hi⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    rw [LinearMap.mem_ker]
    funext i
    exact x.property.2 i.val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact prefix dimension after separating all locally supported modes. -/
theorem prefix_finrank (P : Submodule K M) (ρ : I → M →ₗ[K] K)
    (s : I → M) (A : Finset I)
    (hdual : ∀ i j, ρ i (s j) = if i = j then 1 else 0)
    (hmem : ∀ i ∈ A, s i ∈ P)
    (habsent : ∀ x ∈ P, ∀ i ∉ A, ρ i x = 0) :
    Module.finrank K P = A.card + Module.finrank K ↥(P ⊓ nullModes ρ) := by
  have h := (prefixCoefficients P ρ A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (prefixCoefficients_surjective P ρ s A hdual hmem),
    finrank_top, (prefixKernelEquiv P ρ A habsent).finrank_eq] at h
  simpa using h.symm

/-- The same decomposition as an actual equality of vectors; this is
the support-preserving subtraction used in the paper. -/
theorem subtract_available_modes_mem (P : Submodule K M)
    (ρ : I → M →ₗ[K] K) (s : I → M) (A : Finset I)
    (hdual : ∀ i j, ρ i (s j) = if i = j then 1 else 0)
    (hmem : ∀ i ∈ A, s i ∈ P)
    (habsent : ∀ x ∈ P, ∀ i ∉ A, ρ i x = 0)
    (x : M) (hx : x ∈ P) :
    x - ∑ i ∈ A, ρ i x • s i ∈ P ⊓ nullModes ρ := by
  constructor
  · exact P.sub_mem hx (P.sum_mem (fun i hi => P.smul_mem _ (hmem i hi)))
  · intro i
    by_cases hi : i ∈ A
    · simp [map_sub, map_sum, hdual, hi]
    · simp [map_sub, map_sum, hdual, hi, habsent x hx i hi]

end Papers.Rigidity.ModeSplitting
