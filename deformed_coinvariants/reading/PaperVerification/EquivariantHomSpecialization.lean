module

public import PaperVerification.EquivariantHomMatrices
public import Mathlib.Tactic.Ring

/-!
# Specialization of the actual Reynolds matrices

Coordinate representations are extended by mapping their literal matrices.
The conjugation action on a linear-map space has entry
`A(g)ᵢⱼ B(g⁻¹)ᵦₐ`. Its average therefore commutes with every coefficient
homomorphism for which the group order is invertible. This supplies the
specialization step for equivariant rank comparison without assuming that
invariants or chosen bases commute with scalar extension.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

variable {R S : Type*} [CommRing R] [CommRing S]
variable {v l : Type*} [Fintype v] [Fintype l]
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq l := Classical.decEq l

def homActionMatrix (A : Matrix v v R) (B : Matrix l l R) :
    Matrix (v × l) (v × l) R :=
  fun p q => A p.1 q.1 * B q.2 p.2

theorem homActionMatrix_mulVec (A : Matrix v v R) (B : Matrix l l R)
    (x : v × l → R) :
    homActionMatrix A B *ᵥ x = flatten ((A * flatten.symm x) * B) := by
  funext p
  change (∑ q : v × l, (A p.1 q.1 * B q.2 p.2) * x q) =
    ∑ b : l, (∑ j : v, A p.1 j * x (j,b)) * B b p.2
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem map_homActionMatrix (φ : R →+* S) (A : Matrix v v R) (B : Matrix l l R) :
    (homActionMatrix A B).map φ = homActionMatrix (A.map φ) (B.map φ) := by
  ext p q
  exact map_mul φ _ _

section Representations

variable {G : Type*} [Group G]

/-- Extension of a finite-coordinate representation by its actual matrices. -/
def mapRepresentation (φ : R →+* S) (ρ : Representation R G (v → R)) :
    Representation S G (v → S) where
  toFun g := ((LinearMap.toMatrix' (ρ g)).map φ).mulVecLin
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one]
    rw [Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.mulVecLin_mul]
    rfl

@[simp] theorem mapRepresentation_toMatrix (φ : R →+* S)
    (ρ : Representation R G (v → R)) (g : G) :
    LinearMap.toMatrix' (mapRepresentation φ ρ g) = (LinearMap.toMatrix' (ρ g)).map φ :=
  LinearMap.toMatrix'_toLin' _

@[simp] theorem mapRepresentation_id (ρ : Representation R G (v → R)) :
    mapRepresentation (RingHom.id R) ρ = ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  rw [mapRepresentation_toMatrix]
  rfl

theorem mapRepresentation_comp {T : Type*} [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (ρ : Representation R G (v → R)) :
    mapRepresentation ψ (mapRepresentation φ ρ) = mapRepresentation (ψ.comp φ) ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  rw [mapRepresentation_toMatrix, mapRepresentation_toMatrix, mapRepresentation_toMatrix]
  rfl

theorem homRepresentation_toMatrix (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) (g : G) :
    LinearMap.toMatrix' (homRepresentation τ ρ g) =
      homActionMatrix (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (τ g⁻¹)) := by
  apply Matrix.mulVec_injective
  funext x
  rw [LinearMap.toMatrix'_mulVec, homRepresentation_apply, homActionMatrix_mulVec]
  change flatten (LinearMap.toMatrix' ((ρ g).comp ((homCoordinates.symm x).comp (τ g⁻¹)))) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
  have hc : LinearMap.toMatrix' (homCoordinates.symm x) = flatten.symm x :=
    LinearMap.toMatrix'.apply_symm_apply _
  rw [hc, Matrix.mul_assoc]

end Representations

section Averaging

variable {G : Type*} [Group G] [Fintype G]
  [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : S)]

theorem reynoldsMatrix_eq_sum (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) :
    reynoldsMatrix τ ρ = ⅟(Fintype.card G : R) •
      ∑ g : G, homActionMatrix (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (τ g⁻¹)) := by
  unfold reynoldsMatrix
  rw [EquivariantHomExact.averageMap_eq_sum, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact homRepresentation_toMatrix τ ρ g

theorem map_inverse_group_card (φ : R →+* S) :
    φ (⅟(Fintype.card G : R)) = ⅟(Fintype.card G : S) := by
  symm
  apply invOf_eq_right_inv
  rw [← map_natCast φ, ← map_mul, mul_invOf_self, map_one]

/-- Reynolds averaging is a literal specialization identity of finite matrices. -/
theorem map_reynoldsMatrix (φ : R →+* S) (τ : Representation R G (l → R))
    (ρ : Representation R G (v → R)) :
    (reynoldsMatrix τ ρ).map φ =
      reynoldsMatrix (mapRepresentation φ τ) (mapRepresentation φ ρ) := by
  rw [reynoldsMatrix_eq_sum, reynoldsMatrix_eq_sum]
  ext p q
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    map_mul, map_sum, map_inverse_group_card, mapRepresentation_toMatrix,
    homActionMatrix]

end Averaging

end PaperVerification.EquivariantHomMatrices
