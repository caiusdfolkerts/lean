module

public import PaperVerification.EquivariantHomExact
public import PaperVerification.ProjectedRankSpecialization
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite matrices for actual linear-map spaces

The product index records a target coordinate and a source coordinate. The
matrix `postMatrix F` is literal postcomposition by `F`, not a dimension model
of that operation. Its exactness follows column by column from the original
complex. The Reynolds projection is likewise the actual averaging operator
on the transported `linHom` representation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

variable {R : Type*} [CommRing R]
variable {u v w l : Type*} [Fintype u] [Fintype v] [Fintype w] [Fintype l]
local instance : DecidableEq u := Classical.decEq u
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq w := Classical.decEq w
local instance : DecidableEq l := Classical.decEq l

def flatten : Matrix v l R ≃ₗ[R] (v × l → R) where
  toFun A p := A p.1 p.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homCoordinates : ((l → R) →ₗ[R] (v → R)) ≃ₗ[R] (v × l → R) :=
  LinearMap.toMatrix'.trans flatten

@[simp] theorem homCoordinates_apply (f : (l → R) →ₗ[R] (v → R)) (p : v × l) :
    homCoordinates f p = f (Pi.single p.2 1) p.1 := rfl

theorem homCoordinates_symm_apply (x : v × l → R) (a : l → R) (i : v) :
    homCoordinates.symm x a i = ∑ j : l, x (i,j) * a j := rfl

/-- The finite matrix of postcomposition on the full linear-map space. -/
def postMatrix (F : Matrix w v R) : Matrix (w × l) (v × l) R :=
  fun p q => if p.2 = q.2 then F p.1 q.1 else 0

theorem postMatrix_mulVec (F : Matrix w v R) (x : v × l → R) (p : w × l) :
    (postMatrix F *ᵥ x) p = (F *ᵥ (fun i => x (i,p.2))) p.1 := by
  simp [postMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem postMatrix_coordinates (F : Matrix w v R)
    (h : (l → R) →ₗ[R] (v → R)) :
    postMatrix F *ᵥ homCoordinates h = homCoordinates (F.mulVecLin.comp h) := by
  ext p
  rw [postMatrix_mulVec]
  rfl

theorem postMatrix_mul (F : Matrix w v R) (G : Matrix v u R) :
    postMatrix (l := l) (F*G) = postMatrix F * postMatrix G := by
  apply Matrix.mulVec_injective
  funext x p
  simp only [← Matrix.mulVec_mulVec, postMatrix_mulVec]

@[simp] theorem postMatrix_zero : postMatrix (l := l) (0 : Matrix w v R) = 0 := by
  ext p q
  simp only [postMatrix, Matrix.zero_apply, ite_self]

@[simp] theorem postMatrix_one : postMatrix (l := l) (1 : Matrix v v R) = 1 := by
  apply Matrix.mulVec_injective
  funext x p
  rw [postMatrix_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

theorem postMatrix_complex (F : Matrix w v R) (G : Matrix v u R) (h : F*G=0) :
    postMatrix (l := l) F * postMatrix (l := l) G = (0 : Matrix (w × l) (u × l) R) := by
  rw [← postMatrix_mul, h, postMatrix_zero]

/-- Exactness on full linear-map spaces is the original exactness applied
independently to every source-basis column. -/
theorem postMatrix_exact (F : Matrix w v R) (G : Matrix v u R)
    (he : LinearMap.range G.mulVecLin = LinearMap.ker F.mulVecLin) :
    LinearMap.range (postMatrix (l := l) G).mulVecLin =
      LinearMap.ker (postMatrix F).mulVecLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change postMatrix F *ᵥ (postMatrix G *ᵥ y) = 0
    ext p
    rw [postMatrix_mulVec]
    have hy : (fun i => (postMatrix G *ᵥ y) (i,p.2)) = G *ᵥ (fun j => y (j,p.2)) := by
      funext i
      exact postMatrix_mulVec G y (i,p.2)
    rw [hy]
    exact congrFun (he.le (LinearMap.mem_range_self G.mulVecLin (fun j => y (j,p.2)))) p.1
  · intro x hx
    change postMatrix F *ᵥ x = 0 at hx
    have hc : ∀ a : l, ∃ y : u → R, G *ᵥ y = fun i => x (i,a) := by
      intro a
      apply he.ge
      change F *ᵥ (fun i => x (i,a)) = 0
      funext i
      have hi := congrFun hx (i,a)
      simpa only [Matrix.mulVecLin_apply, postMatrix_mulVec, Pi.zero_apply] using hi
    choose y hy using hc
    refine ⟨fun p => y p.2 p.1, ?_⟩
    ext p
    rw [Matrix.mulVecLin_apply, postMatrix_mulVec]
    exact congrFun (hy p.2) p.1

theorem map_postMatrix {S : Type*} [CommRing S] (φ : R →+* S) (F : Matrix w v R) :
    (postMatrix (l := l) F).map φ = postMatrix (F.map φ) := by
  ext p q
  simp only [postMatrix, Matrix.map_apply]
  split_ifs <;> simp only [map_zero]

section Reynolds

variable {G : Type*} [Group G]

/-- The actual conjugation action on linear maps, expressed in finite
coordinates. This definition keeps an arbitrary source representation. -/
def homRepresentation (τ : Representation R G (l → R)) (ρ : Representation R G (v → R)) :
    Representation R G (v × l → R) :=
  (LinearEquiv.conjRingEquiv (homCoordinates (R := R) (v := v) (l := l))).toMonoidHom.comp
    (Representation.linHom τ ρ)

@[simp] theorem homRepresentation_apply (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) (g : G) (x : v × l → R) :
    homRepresentation τ ρ g x =
      homCoordinates (Representation.linHom τ ρ g (homCoordinates.symm x)) := rfl

variable [Fintype G] [Invertible (Fintype.card G : R)]

def reynoldsMatrix (τ : Representation R G (l → R)) (ρ : Representation R G (v → R)) :
    Matrix (v × l) (v × l) R :=
  LinearMap.toMatrix' (homRepresentation τ ρ).averageMap

theorem reynoldsMatrix_idempotent (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) :
    reynoldsMatrix τ ρ * reynoldsMatrix τ ρ = reynoldsMatrix τ ρ := by
  unfold reynoldsMatrix
  rw [← LinearMap.toMatrix'_comp, EquivariantHomExact.averageMap_idempotent]

theorem homPost_equivariant (τ : Representation R G (l → R))
    {ρ : Representation R G (v → R)} {σ : Representation R G (w → R)}
    (F : Matrix w v R) (hF : ∀ g, F.mulVecLin.comp (ρ g) = (σ g).comp F.mulVecLin)
    (g : G) (x : v × l → R) :
    postMatrix F *ᵥ (homRepresentation τ ρ g x) =
      homRepresentation τ σ g (postMatrix F *ᵥ x) := by
  let f : IntertwiningMap ρ σ := ⟨F.mulVecLin,hF⟩
  obtain ⟨h, rfl⟩ := (homCoordinates (R := R) (v := v) (l := l)).surjective x
  simp only [homRepresentation_apply, LinearEquiv.symm_apply_apply,
    postMatrix_coordinates]
  exact congrArg (homCoordinates (R := R) (v := w) (l := l))
    (EquivariantHomExact.homPost_intertwines τ f g h)

theorem reynoldsMatrix_natural (τ : Representation R G (l → R))
    {ρ : Representation R G (v → R)} {σ : Representation R G (w → R)}
    (F : Matrix w v R) (hF : ∀ g, F.mulVecLin.comp (ρ g) = (σ g).comp F.mulVecLin) :
    reynoldsMatrix τ σ * postMatrix F = postMatrix F * reynoldsMatrix τ ρ := by
  apply Matrix.mulVec_injective
  funext x
  simp only [← Matrix.mulVec_mulVec, reynoldsMatrix, LinearMap.toMatrix'_mulVec]
  exact (EquivariantHomExact.averageMap_natural
    (homRepresentation τ ρ) (homRepresentation τ σ) (postMatrix F).mulVecLin
    (homPost_equivariant τ F hF) x).symm

end Reynolds

end PaperVerification.EquivariantHomMatrices
