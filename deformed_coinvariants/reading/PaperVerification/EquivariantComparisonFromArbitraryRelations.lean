module

public import PaperVerification.ProjectedComplexWithoutDomainAction
public import PaperVerification.EquivariantCokernelGenericSpecialization

/-!
# Equivariant comparison from arbitrary relation generators

The first matrix presents the actual equivariant cokernel.  A second matrix
certifies a polynomial complex exact at one fiber.  Its domain is permitted
to have no group action at all: projection of its image gives the required
comparison on genuine intertwining spaces.  Thus the result applies to a
basis-dependent syzygy presentation without any hidden equivariance premise.

This source is supporting mathematics and has not yet been compiled.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Matrix Representation

namespace PaperVerification.EquivariantHomMatrices

variable {R K K₀ : Type*} [CommRing R] [IsDomain R] [Field K] [Field K₀]
variable {G u v w l : Type*} [Group G] [Fintype G]
  [Fintype u] [Fintype v] [Fintype w] [Fintype l]
  [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : K)]
  [Invertible (Fintype.card G : K₀)]
local instance : DecidableEq u := Classical.decEq u
local instance : DecidableEq v := Classical.decEq v
local instance : DecidableEq w := Classical.decEq w
local instance : DecidableEq l := Classical.decEq l

theorem projected_rank_le_of_arbitrary_relations
    (τ : Representation R G (l → R))
    (ρV : Representation R G (v → R)) (ρW : Representation R G (w → R))
    (F : Matrix w v R) (D : Matrix v u R) (hFD : F*D=0)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hexact : LinearMap.range (D.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin) :
    (postMatrix (l := l) (F.map φ) *
      reynoldsMatrix (mapRepresentation φ τ) (mapRepresentation φ ρV)).rank ≤
    (postMatrix (l := l) (F.map φ₀) *
      reynoldsMatrix (mapRepresentation φ₀ τ) (mapRepresentation φ₀ ρV)).rank := by
  have he : LinearMap.range ((postMatrix (l := l) D).map φ₀).mulVecLin =
      LinearMap.ker ((postMatrix (l := l) F).map φ₀).mulVecLin := by
    rw [map_postMatrix,map_postMatrix]
    exact postMatrix_exact _ _ hexact
  have h := ProjectedComplex.rank_le_at_exact_fiber
    (postMatrix (l := l) F) (postMatrix (l := l) D)
    (reynoldsMatrix τ ρV) (reynoldsMatrix τ ρW)
    (postMatrix_complex F D hFD) (reynoldsMatrix_idempotent τ ρV)
    (reynoldsMatrix_natural τ F hF).symm φ₀ φ he
  simpa only [Matrix.map_mul,map_postMatrix,map_reynoldsMatrix] using h

/-- Every irreducible test representation is covered, and the statement is
stronger: it holds for every finite-coordinate test representation. -/
theorem intertwiner_cokernel_dimension_ge_of_arbitrary_relations
    {Q Q₀ : Type*} [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K₀ Q₀]
    (τ : Representation R G (l → R))
    (ρV : Representation R G (v → R)) (ρW : Representation R G (w → R))
    (F : Matrix w v R) (D : Matrix v u R) (hFD : F*D=0)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hexact : LinearMap.range (D.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin)
    (π : Representation K G Q) (π₀ : Representation K₀ G Q₀)
    (q : IntertwiningMap (mapRepresentation φ ρW) π)
    (q₀ : IntertwiningMap (mapRepresentation φ₀ ρW) π₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hker : LinearMap.range (F.map φ).mulVecLin = LinearMap.ker q.toLinearMap)
    (hker₀ : LinearMap.range (F.map φ₀).mulVecLin = LinearMap.ker q₀.toLinearMap) :
    Module.finrank K₀ (IntertwiningMap (mapRepresentation φ₀ τ) π₀) ≤
      Module.finrank K (IntertwiningMap (mapRepresentation φ τ) π) := by
  have hrank := projected_rank_le_of_arbitrary_relations
    τ ρV ρW F D hFD hF φ φ₀ hexact
  have h₁ := equivariant_cokernel_rank_formula (mapRepresentation φ τ)
    (mappedIntertwiner φ ρV ρW F hF) q hq hker
  have h₀ := equivariant_cokernel_rank_formula (mapRepresentation φ₀ τ)
    (mappedIntertwiner φ₀ ρV ρW F hF) q₀ hq₀ hker₀
  have hc := idempotent_rank_specialization (reynoldsMatrix τ ρW)
    (reynoldsMatrix_idempotent τ ρW) φ φ₀
  simp only [map_reynoldsMatrix] at hc
  simp only [mappedIntertwiner,LinearMap.toMatrix'_toLin'] at h₁ h₀
  omega

/-- At the fraction field, the lower comparison and the usual specialization
upper comparison are equalities. There is still no action on relation indices. -/
theorem intertwiner_cokernel_dimension_eq_generic_of_arbitrary_relations
    [Algebra R K] [IsFractionRing R K]
    {Q Q₀ : Type*} [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K₀ Q₀]
    (τ : Representation R G (l → R))
    (ρV : Representation R G (v → R)) (ρW : Representation R G (w → R))
    (F : Matrix w v R) (D : Matrix v u R) (hFD : F*D=0)
    (hF : ∀ g, F.mulVecLin.comp (ρV g) = (ρW g).comp F.mulVecLin)
    (φ₀ : R →+* K₀)
    (hexact : LinearMap.range (D.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin)
    (π : Representation K G Q) (π₀ : Representation K₀ G Q₀)
    (q : IntertwiningMap (mapRepresentation (algebraMap R K) ρW) π)
    (q₀ : IntertwiningMap (mapRepresentation φ₀ ρW) π₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hker : LinearMap.range (F.map (algebraMap R K)).mulVecLin =
      LinearMap.ker q.toLinearMap)
    (hker₀ : LinearMap.range (F.map φ₀).mulVecLin = LinearMap.ker q₀.toLinearMap) :
    Module.finrank K (IntertwiningMap (mapRepresentation (algebraMap R K) τ) π) =
      Module.finrank K₀ (IntertwiningMap (mapRepresentation φ₀ τ) π₀) := by
  apply le_antisymm
  · exact intertwiner_cokernel_dimension_ge_generic
      τ ρV ρW F hF φ₀ π₀ π q₀ q hq₀ hq hker₀ hker
  · exact intertwiner_cokernel_dimension_ge_of_arbitrary_relations
      τ ρV ρW F D hFD hF (algebraMap R K) φ₀ hexact
      π π₀ q q₀ hq hq₀ hker hker₀

end PaperVerification.EquivariantHomMatrices
