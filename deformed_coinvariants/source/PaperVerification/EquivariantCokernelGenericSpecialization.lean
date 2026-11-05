module

public import PaperVerification.EquivariantCokernelSpecialization

/-!
# Every equivariant cokernel specializes to at least its generic multiplicity

This is a one-matrix rank argument. The averaging idempotent gives the actual
intertwining space; its rank is constant, whereas the rank of the projected
presentation matrix can only decrease. No exact second differential is
required. In particular the result applies at singular original parameters.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R L] [IsFractionRing R L]
variable {G v w l : Type*} [Group G] [Fintype G]
  [Fintype v] [Fintype w] [Fintype l]
  [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : K)]
  [Invertible (Fintype.card G : L)]
local instance cokernelGenericDecidableV : DecidableEq v := Classical.decEq v
local instance cokernelGenericDecidableW : DecidableEq w := Classical.decEq w
local instance cokernelGenericDecidableL : DecidableEq l := Classical.decEq l

theorem intertwiner_cokernel_dimension_ge_generic
    {Q Q₀ : Type*} [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module L Q₀]
    (τ : Representation R G (l → R)) (ρV : Representation R G (v → R))
    (ρW : Representation R G (w → R))
    (F : Matrix w v R)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (φ : R →+* K)
    (π : Representation K G Q) (π₀ : Representation L G Q₀)
    (q : IntertwiningMap (mapRepresentation φ ρW) π)
    (q₀ : IntertwiningMap (mapRepresentation (algebraMap R L) ρW) π₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hker : LinearMap.range (F.map φ).mulVecLin = LinearMap.ker q.toLinearMap)
    (hker₀ : LinearMap.range (F.map (algebraMap R L)).mulVecLin =
      LinearMap.ker q₀.toLinearMap) :
    Module.finrank L (IntertwiningMap (mapRepresentation (algebraMap R L) τ) π₀) ≤
      Module.finrank K (IntertwiningMap (mapRepresentation φ τ) π) := by
  have hrank := RankSpecialization.rank_specialization_le (L := L)
    (postMatrix (l := l) F * reynoldsMatrix τ ρV) φ
  simp only [Matrix.map_mul,map_postMatrix,map_reynoldsMatrix] at hrank
  have h₁ := equivariant_cokernel_rank_formula (mapRepresentation φ τ)
    (mappedIntertwiner φ ρV ρW F hF) q hq hker
  have h₀ := equivariant_cokernel_rank_formula (mapRepresentation (algebraMap R L) τ)
    (mappedIntertwiner (algebraMap R L) ρV ρW F hF) q₀ hq₀ hker₀
  have hc := idempotent_rank_specialization (reynoldsMatrix τ ρW)
    (reynoldsMatrix_idempotent τ ρW) φ (algebraMap R L)
  simp only [map_reynoldsMatrix] at hc
  have hmat : LinearMap.toMatrix' (F.map φ).mulVecLin = F.map φ :=
    LinearMap.toMatrix'_toLin' _
  have hmat₀ : LinearMap.toMatrix' (F.map (algebraMap R L)).mulVecLin =
      F.map (algebraMap R L) := LinearMap.toMatrix'_toLin' _
  simp only [mappedIntertwiner, hmat, hmat₀] at h₁ h₀
  omega

end PaperVerification.EquivariantHomMatrices
