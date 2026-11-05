module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

/-!
# Invariant subspaces for a diagonal operator with distinct eigenvalues

The proof constructs the finite spectral projectors as products of linear
factors. It identifies an invariant subspace with the actual coordinate
subspace spanned by the coordinate vectors it contains. This applies to the
torus-fixed subspaces once one torus element has distinct eigenvalues.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DiagonalInvariantSubspaces

open scoped BigOperators Classical

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The actual diagonal endomorphism in the coordinate basis. -/
def diagonal (d : ι → K) : Module.End K (ι → K) where
  toFun v i := d i * v i
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

@[simp] theorem diagonal_apply (d : ι → K) (v : ι → K) (i : ι) :
    diagonal d v i = d i * v i := rfl

/-- Applying any finite product of factors `D-dⱼ` preserves an invariant
subspace. The displayed expression gives every coordinate of the result. -/
theorem spectralProduct_mem (d : ι → K) (U : Submodule K (ι → K))
    (hU : ∀ v ∈ U, diagonal d v ∈ U) (s : Finset ι)
    (v : ι → K) (hv : v ∈ U) :
    (fun i => (∏ j ∈ s, (d i-d j))*v i) ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert j s hj ih =>
    have h := U.sub_mem (hU _ ih) (U.smul_mem (d j) ih)
    convert h using 1
    ext i
    simp only [Finset.prod_insert hj, Pi.sub_apply, Pi.smul_apply,
      diagonal_apply, smul_eq_mul]
    ring

/-- A coordinate component of a vector in an invariant subspace belongs
to that subspace when all diagonal entries are distinct. -/
theorem coordinateComponent_mem (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) (hU : ∀ v ∈ U, diagonal d v ∈ U)
    (v : ι → K) (hv : v ∈ U) (i : ι) : Pi.single i (v i) ∈ U := by
  classical
  let c := ∏ j ∈ Finset.univ.erase i, (d i-d j)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hd h).symm)
  have h := U.smul_mem c⁻¹ (spectralProduct_mem d U hU (Finset.univ.erase i) v hv)
  convert h using 1
  ext j
  by_cases hji : j = i
  · subst j
    simp [c, hc]
  · have hprod : (∏ q ∈ Finset.univ.erase i, (d j-d q)) = 0 :=
      Finset.prod_eq_zero (show j ∈ Finset.univ.erase i by simp [hji]) (by simp)
    simp [Pi.single_apply, hji, hprod]

/-- The coordinate support of a subspace, defined intrinsically by which
coordinate vectors belong to it. -/
def coordinateSupport (U : Submodule K (ι → K)) : Set ι :=
  {i | Pi.single i 1 ∈ U}

/-- Every invariant subspace is a coordinate subspace; there are no further
invariant subspaces when the eigenvalues are pairwise distinct. -/
theorem invariant_eq_coordinateSubspace (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) (hU : ∀ v ∈ U, diagonal d v ∈ U) :
    U = Pi.spanSubset K (coordinateSupport U) := by
  classical
  apply le_antisymm
  · intro v hv
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    by_contra hvi
    apply hi
    change Pi.single i 1 ∈ U
    have h := U.smul_mem (v i)⁻¹ (coordinateComponent_mem d hd U hU v hv i)
    convert h using 1
    ext j
    by_cases hij : i = j
    · subst j
      simp [hvi]
    · simp [Pi.single_apply, hij]
  · change Submodule.span K (Pi.basisFun K ι '' coordinateSupport U) ≤ U
    rw [Submodule.span_le]
    rintro _ ⟨i,hi,rfl⟩
    change Pi.basisFun K ι i ∈ U
    rw [Pi.basisFun_apply]
    exact hi

/-- Every coordinate subspace is invariant under every diagonal map. -/
theorem coordinateSubspace_invariant (d : ι → K) (s : Set ι)
    (v : ι → K) (hv : v ∈ Pi.spanSubset K s) : diagonal d v ∈ Pi.spanSubset K s := by
  rw [Pi.mem_spanSubset_iff] at hv ⊢
  intro i hi
  simp [hv i hi]

theorem invariant_iff_coordinateSubspace (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) :
    (∀ v ∈ U, diagonal d v ∈ U) ↔ ∃ s : Set ι, U = Pi.spanSubset K s := by
  constructor
  · intro h
    exact ⟨coordinateSupport U,invariant_eq_coordinateSubspace d hd U h⟩
  · rintro ⟨s,rfl⟩
    exact coordinateSubspace_invariant d s

end PaperVerification.DiagonalInvariantSubspaces
