module

public import PaperVerification.EquivariantHomSpecialization
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Projected matrix ranks and actual equivariant cokernels

The rank of postcomposition followed by Reynolds averaging is the dimension
of the image of postcomposition on genuine intertwining maps. This is proved
by equality of the actual subspaces after the coordinate embedding. Combined
with averaging exactness, it gives the dimension of the literal equivariant
cokernel; no multiplicity or dimension equality is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

variable {R : Type*} [CommRing R]
variable {G v w l : Type*} [Group G] [Fintype G]
  [Fintype v] [Fintype w] [Fintype l] [Invertible (Fintype.card G : R)]
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq w := Classical.decEq w
local instance : DecidableEq l := Classical.decEq l

def intertwinerCoordinates (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) :
    IntertwiningMap τ ρ →ₗ[R] (v × l → R) :=
  homCoordinates.toLinearMap.comp (IntertwiningMap.toLinearMapl (ρ := τ) (σ := ρ))

@[simp] theorem intertwinerCoordinates_apply (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) (h : IntertwiningMap τ ρ) :
    intertwinerCoordinates τ ρ h = homCoordinates h.toLinearMap := rfl

theorem intertwinerCoordinates_injective (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) : Function.Injective (intertwinerCoordinates τ ρ) :=
  homCoordinates.injective.comp (IntertwiningMap.toLinearMap_injective τ ρ)

theorem reynoldsMatrix_coordinates (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) (h : (l → R) →ₗ[R] (v → R)) :
    reynoldsMatrix τ ρ *ᵥ homCoordinates h =
      homCoordinates ((Representation.linHom τ ρ).averageMap h) := by
  rw [reynoldsMatrix, LinearMap.toMatrix'_mulVec]
  symm
  apply EquivariantHomExact.averageMap_natural
  intro g a
  change homCoordinates (Representation.linHom τ ρ g a) =
    homCoordinates (Representation.linHom τ ρ g (homCoordinates.symm (homCoordinates a)))
  rw [LinearEquiv.symm_apply_apply]

theorem projectedPost_range (τ : Representation R G (l → R))
    {ρ : Representation R G (v → R)} {σ : Representation R G (w → R)}
    (f : IntertwiningMap ρ σ) :
    LinearMap.range ((postMatrix (LinearMap.toMatrix' f.toLinearMap) * reynoldsMatrix τ ρ).mulVecLin) =
      (LinearMap.range (IntertwiningMap.llcomp τ ρ σ f)).map (intertwinerCoordinates τ σ) := by
  have hmat : (LinearMap.toMatrix' f.toLinearMap).mulVecLin = f.toLinearMap :=
    Matrix.toLin'_toMatrix' f.toLinearMap
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    let h := EquivariantHomExact.averagedIntertwiner τ ρ (homCoordinates.symm x)
    refine ⟨f.comp h, ⟨h,rfl⟩, ?_⟩
    obtain ⟨a, rfl⟩ := (homCoordinates (R := R) (v := v) (l := l)).surjective x
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec,
      reynoldsMatrix_coordinates, postMatrix_coordinates, hmat,
      intertwinerCoordinates_apply, h, LinearEquiv.symm_apply_apply,
      EquivariantHomExact.averagedIntertwiner_toLinearMap]
    rfl
  · rintro ⟨h, ⟨a, rfl⟩, rfl⟩
    refine ⟨homCoordinates a.toLinearMap, ?_⟩
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec,
      reynoldsMatrix_coordinates, postMatrix_coordinates, hmat,
      intertwinerCoordinates_apply]
    have ha := congrArg IntertwiningMap.toLinearMap
      (EquivariantHomExact.averagedIntertwiner_of_intertwiner τ ρ a)
    rw [EquivariantHomExact.averagedIntertwiner_toLinearMap] at ha
    rw [ha]
    rfl

section Field

variable {K : Type*} [Field K] [Invertible (Fintype.card G : K)]

/-- The projected full-Hom matrix has exactly the rank of the actual map on
intertwining spaces, over arbitrary (possibly nonsplitting) fields. -/
theorem projectedPost_rank (τ : Representation K G (l → K))
    {ρ : Representation K G (v → K)} {σ : Representation K G (w → K)}
    (f : IntertwiningMap ρ σ) :
    (postMatrix (LinearMap.toMatrix' f.toLinearMap) * reynoldsMatrix τ ρ).rank =
      Module.finrank K (LinearMap.range (IntertwiningMap.llcomp τ ρ σ f)) := by
  unfold Matrix.rank
  rw [projectedPost_range]
  exact (Submodule.equivMapOfInjective (intertwinerCoordinates τ σ)
    (intertwinerCoordinates_injective τ σ)
    (LinearMap.range (IntertwiningMap.llcomp τ ρ σ f))).finrank_eq.symm

theorem reynoldsMatrix_rank (τ : Representation K G (l → K))
    (ρ : Representation K G (v → K)) :
    (reynoldsMatrix τ ρ).rank = Module.finrank K (IntertwiningMap τ ρ) := by
  have h := projectedPost_rank τ (IntertwiningMap.id ρ)
  have hid : IntertwiningMap.llcomp τ ρ ρ (IntertwiningMap.id ρ) = LinearMap.id := by
    ext a x
    rfl
  have hmatrix : LinearMap.toMatrix' (IntertwiningMap.id ρ).toLinearMap = 1 :=
    LinearMap.toMatrix'_id
  rw [hmatrix, postMatrix_one, Matrix.one_mul, hid, LinearMap.range_id, finrank_top] at h
  exact h

/-- The dimension of the genuine equivariant quotient is the difference of
two actual projected matrix ranks. -/
theorem equivariant_cokernel_rank_formula {Q : Type*} [AddCommGroup Q] [Module K Q]
    (τ : Representation K G (l → K))
    {ρ : Representation K G (v → K)} {σ : Representation K G (w → K)}
    {π : Representation K G Q} (f : IntertwiningMap ρ σ) (q : IntertwiningMap σ π)
    (hq : Function.Surjective q)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap) :
    Module.finrank K (IntertwiningMap τ π) +
      (postMatrix (LinearMap.toMatrix' f.toLinearMap) * reynoldsMatrix τ ρ).rank =
        (reynoldsMatrix τ σ).rank := by
  rw [projectedPost_rank, reynoldsMatrix_rank]
  exact EquivariantHomExact.intertwiner_cokernel_finrank τ q f hq hexact

end Field

end PaperVerification.EquivariantHomMatrices
