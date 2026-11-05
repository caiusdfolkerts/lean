module

public import PaperVerification.EquivariantHomRank
public import Lean.Elab.Tactic.Omega

/-!
# Exact-fiber comparison for genuine equivariant cokernels

All averaging matrices come from the actual conjugation representation on
linear maps. Their ranks are constant under specialization because an
idempotent gives an exact complex with its complementary idempotent. The
projected first-map rank can only decrease away from an exact fiber, so the
dimension of every genuine intertwining space into the cokernel can only
increase. This works over arbitrary residue fields, without a splitting-field
assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

section Idempotents

variable {R : Type*} [CommRing R] {v : Type*} [Fintype v]
local instance : DecidableEq v := Classical.decEq v

theorem idempotent_complement_complex (P : Matrix v v R) (hP : P*P=P) :
    P*(1-P)=0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]

theorem idempotent_complement_exact (P : Matrix v v R) (hP : P*P=P) :
    LinearMap.range (1-P).mulVecLin = LinearMap.ker P.mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul, idempotent_complement_complex P hP, Matrix.mulVecLin_zero]
  · intro x hx
    refine ⟨x, ?_⟩
    change (1-P) *ᵥ x = x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change P *ᵥ x = 0 at hx
    rw [hx, sub_zero]

theorem map_idempotent_complement_exact {S : Type*} [CommRing S]
    (P : Matrix v v R) (hP : P*P=P) (ψ : R →+* S) :
    LinearMap.range ((1-P).map ψ).mulVecLin = LinearMap.ker (P.map ψ).mulVecLin := by
  have hmap : (1-P).map ψ = 1-P.map ψ := by
    ext i j
    simp only [Matrix.map_apply,Matrix.sub_apply,map_sub,Matrix.one_apply]
    split_ifs <;> simp only [map_one,map_zero]
  rw [hmap]
  apply idempotent_complement_exact
  rw [← Matrix.map_mul,hP]

/-- An idempotent matrix over a domain has the same rank over every field
specialization. This proves the needed invariant-dimension constancy. -/
theorem idempotent_rank_specialization [IsDomain R]
    {K K₀ : Type*} [Field K] [Field K₀]
    (P : Matrix v v R) (hP : P*P=P) (φ : R →+* K) (φ₀ : R →+* K₀) :
    (P.map φ).rank = (P.map φ₀).rank := by
  exact le_antisymm
    (RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields P (1-P)
      (idempotent_complement_complex P hP) φ₀ φ (map_idempotent_complement_exact P hP φ₀))
    (RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields P (1-P)
      (idempotent_complement_complex P hP) φ φ₀ (map_idempotent_complement_exact P hP φ))

end Idempotents

section Representations

variable {R S : Type*} [CommRing R] [CommRing S]
variable {G v w : Type*} [Group G] [Fintype v] [Fintype w]
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq w := Classical.decEq w

theorem map_matrix_intertwines (φ : R →+* S)
    (ρ : Representation R G (v → R)) (σ : Representation R G (w → R))
    (F : Matrix w v R) (hF : ∀ g, F.mulVecLin.comp (ρ g) = (σ g).comp F.mulVecLin)
    (g : G) :
    (F.map φ).mulVecLin.comp (mapRepresentation φ ρ g) =
      (mapRepresentation φ σ g).comp (F.map φ).mulVecLin := by
  apply LinearMap.toMatrix'.injective
  have hmat : LinearMap.toMatrix' F.mulVecLin = F := LinearMap.toMatrix'_toLin' F
  have hmat' : LinearMap.toMatrix' (F.map φ).mulVecLin = F.map φ :=
    LinearMap.toMatrix'_toLin' _
  have h := congrArg LinearMap.toMatrix' (hF g)
  simp only [LinearMap.toMatrix'_comp, hmat] at h
  simp only [LinearMap.toMatrix'_comp, hmat', mapRepresentation_toMatrix,
    ← Matrix.map_mul, h]

def mappedIntertwiner (φ : R →+* S)
    (ρ : Representation R G (v → R)) (σ : Representation R G (w → R))
    (F : Matrix w v R) (hF : ∀ g, F.mulVecLin.comp (ρ g) = (σ g).comp F.mulVecLin) :
    IntertwiningMap (mapRepresentation φ ρ) (mapRepresentation φ σ) :=
  ⟨(F.map φ).mulVecLin, map_matrix_intertwines φ ρ σ F hF⟩

end Representations

section Specialization

variable {R K K₀ : Type*} [CommRing R] [IsDomain R] [Field K] [Field K₀]
variable {G u v w l : Type*} [Group G] [Fintype G]
  [Fintype u] [Fintype v] [Fintype w] [Fintype l]
  [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : K)]
  [Invertible (Fintype.card G : K₀)]
local instance : DecidableEq u := Classical.decEq u
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq w := Classical.decEq w
local instance : DecidableEq l := Classical.decEq l

theorem equivariant_projected_rank_le_at_exact_fiber
    (τ : Representation R G (l → R)) (ρU : Representation R G (u → R))
    (ρV : Representation R G (v → R)) (ρW : Representation R G (w → R))
    (F : Matrix w v R) (D : Matrix v u R) (hFD : F*D=0)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (hD : ∀ g, D.mulVecLin.comp (ρU g) = (ρV g).comp D.mulVecLin)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hexact : LinearMap.range (D.map φ₀).mulVecLin = LinearMap.ker (F.map φ₀).mulVecLin) :
    (postMatrix (l := l) (F.map φ) *
      reynoldsMatrix (mapRepresentation φ τ) (mapRepresentation φ ρV)).rank ≤
    (postMatrix (l := l) (F.map φ₀) *
      reynoldsMatrix (mapRepresentation φ₀ τ) (mapRepresentation φ₀ ρV)).rank := by
  have he : LinearMap.range ((postMatrix (l := l) D).map φ₀).mulVecLin =
      LinearMap.ker ((postMatrix (l := l) F).map φ₀).mulVecLin := by
    rw [map_postMatrix, map_postMatrix]
    exact postMatrix_exact _ _ hexact
  have h := ProjectedRankSpecialization.rank_le_at_exact_fiber
    (postMatrix (l := l) F) (postMatrix (l := l) D)
    (reynoldsMatrix τ ρV) (reynoldsMatrix τ ρU)
    (postMatrix_complex F D hFD) (reynoldsMatrix_idempotent τ ρV)
    (reynoldsMatrix_natural τ D hD) φ₀ φ he
  simpa only [Matrix.map_mul, map_postMatrix, map_reynoldsMatrix] using h

/-- The complete equivariant linear-algebra comparison behind Lemma 2.1.
The supplied maps are literal presentations of the two cokernels; exactness
of the deformation complex is assumed only at the specified fiber. -/
theorem intertwiner_cokernel_dimension_ge_exact_fiber
    {Q Q₀ : Type*} [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K₀ Q₀]
    (τ : Representation R G (l → R)) (ρU : Representation R G (u → R))
    (ρV : Representation R G (v → R)) (ρW : Representation R G (w → R))
    (F : Matrix w v R) (D : Matrix v u R) (hFD : F*D=0)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (hD : ∀ g, D.mulVecLin.comp (ρU g) = (ρV g).comp D.mulVecLin)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hexact : LinearMap.range (D.map φ₀).mulVecLin = LinearMap.ker (F.map φ₀).mulVecLin)
    (π : Representation K G Q) (π₀ : Representation K₀ G Q₀)
    (q : IntertwiningMap (mapRepresentation φ ρW) π)
    (q₀ : IntertwiningMap (mapRepresentation φ₀ ρW) π₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hker : LinearMap.range (F.map φ).mulVecLin = LinearMap.ker q.toLinearMap)
    (hker₀ : LinearMap.range (F.map φ₀).mulVecLin = LinearMap.ker q₀.toLinearMap) :
    Module.finrank K₀ (IntertwiningMap (mapRepresentation φ₀ τ) π₀) ≤
      Module.finrank K (IntertwiningMap (mapRepresentation φ τ) π) := by
  have hrank := equivariant_projected_rank_le_at_exact_fiber
    τ ρU ρV ρW F D hFD hF hD φ φ₀ hexact
  have h₁ := equivariant_cokernel_rank_formula (mapRepresentation φ τ)
    (mappedIntertwiner φ ρV ρW F hF) q hq hker
  have h₀ := equivariant_cokernel_rank_formula (mapRepresentation φ₀ τ)
    (mappedIntertwiner φ₀ ρV ρW F hF) q₀ hq₀ hker₀
  have hc := idempotent_rank_specialization (reynoldsMatrix τ ρW)
    (reynoldsMatrix_idempotent τ ρW) φ φ₀
  simp only [map_reynoldsMatrix] at hc
  have hmat₁ : LinearMap.toMatrix' (F.map φ).mulVecLin = F.map φ :=
    LinearMap.toMatrix'_toLin' _
  have hmat₀ : LinearMap.toMatrix' (F.map φ₀).mulVecLin = F.map φ₀ :=
    LinearMap.toMatrix'_toLin' _
  simp only [mappedIntertwiner] at h₁ h₀
  rw [hmat₁] at h₁
  rw [hmat₀] at h₀
  omega

end Specialization

end PaperVerification.EquivariantHomMatrices
