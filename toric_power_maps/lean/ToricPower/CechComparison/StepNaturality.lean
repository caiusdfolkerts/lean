module

public import ToricPower.CechComparison.BoundaryCompatibility

/-!
# Naturality passes through the actual cohomological dimension shifts

The source connecting map is an epimorphism when the middle sheaf is
flasque. Naturality of the two long exact sequences therefore forces
naturality of each comparison step. The argument works with arbitrary
actual morphisms of short exact sequences, without a functorial choice
of their flasque or injective middle terms.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDegreeOneComparison
open BondalThomsen.FiniteAffineCechAllDegreeComparison

namespace ToricPower.CechNaturality
universe u

/-- The formal cancellation argument behind both dimension-shift steps. -/
private theorem naturality_of_boundaries {C : Type*} [Category C]
    {A A' B B' D D' E E' : C}
    (source : A ⟶ B) (target : A' ⟶ B')
    (source' : D ⟶ E) (target' : D' ⟶ E')
    (first : A ⟶ A') (second : B ⟶ B')
    (first' : D ⟶ D') (second' : E ⟶ E')
    (lower : A ⟶ D) (lower' : A' ⟶ D')
    (upper : B ⟶ E) (upper' : B' ⟶ E') [Epi source]
    (ordinary : source ≫ second = first ≫ target)
    (cech : source' ≫ second' = first' ≫ target')
    (sourceComparison : source ≫ upper = lower ≫ source')
    (targetComparison : target ≫ upper' = lower' ≫ target')
    (previous : first ≫ lower' = lower ≫ first') :
    second ≫ upper' = upper ≫ second' := by
  apply (cancel_epi source).mp
  rw [← Category.assoc, ordinary, Category.assoc, targetComparison,
    ← Category.assoc, previous, Category.assoc, ← cech,
    ← Category.assoc, ← sourceComparison, Category.assoc]

variable {X : Scheme.{u}} {Index : Type u} [X.IsSeparated] [Finite Index]
  (opens : Index → X.Opens) (cover : iSup opens = ⊤)
  (affine : ∀ index, IsAffineOpen (opens index))
  {S T : ShortComplex X.Modules}
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
  [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
  [S.X₂.presheaf.IsFlasque] [T.X₂.presheaf.IsFlasque]

/-- The ordinary connecting morphism is epic for a flasque middle term. -/
theorem cohomologyBoundary_epi (exact : S.ShortExact) (degree : ℕ) :
    Epi (cohomologyBoundary exact degree) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr
    (cohomologyδ_surjective_of_isFlasque exact degree (degree + 1) rfl)

/-- Degree one is natural along every actual coefficient-sequence morphism. -/
@[reassoc]
theorem oneIso_naturality (hS : S.ShortExact) (hT : T.ShortExact) (mapping : S ⟶ T) :
    (cohomologyFunctor X 1).map mapping.τ₁ ≫
        (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine hT).hom =
      (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine hS).hom ≫
        (cechHomologyFunctor opens 1).map mapping.τ₁ := by
  letI := cohomologyBoundary_epi hS 0
  exact naturality_of_boundaries
    (cohomologyBoundary hS 0) (cohomologyBoundary hT 0)
    (schemeCechBoundary opens affine hS 0) (schemeCechBoundary opens affine hT 0)
    ((cohomologyFunctor X 0).map mapping.τ₃) ((cohomologyFunctor X 1).map mapping.τ₁)
    ((cechHomologyFunctor opens 0).map mapping.τ₃) ((cechHomologyFunctor opens 1).map mapping.τ₁)
    (zeroIso opens cover S.X₃).hom (zeroIso opens cover T.X₃).hom
    (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine hS).hom
    (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine hT).hom
    (cohomologyBoundary_naturality hS hT mapping 0)
    (cechBoundary_naturality opens affine hS hT mapping 0)
    (oneIso_boundary opens cover affine hS) (oneIso_boundary opens cover affine hT)
    (zeroIso_naturality opens cover mapping.τ₃)

omit cover in
/-- The positive-degree step retains naturality of the preceding comparison. -/
@[reassoc]
theorem higherStep_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (mapping : S ⟶ T) (degree : ℕ)
    (previousS : AddCommGrpCat.of (Cohomology S.X₃ (degree + 1)) ≅
      (schemeCechComplex opens S.X₃).homology (degree + 1))
    (previousT : AddCommGrpCat.of (Cohomology T.X₃ (degree + 1)) ≅
      (schemeCechComplex opens T.X₃).homology (degree + 1))
    (previousNatural : (cohomologyFunctor X (degree + 1)).map mapping.τ₃ ≫ previousT.hom =
      previousS.hom ≫ (cechHomologyFunctor opens (degree + 1)).map mapping.τ₃) :
    (cohomologyFunctor X (degree + 2)).map mapping.τ₁ ≫
        (higherStep opens affine hT degree previousT).hom =
      (higherStep opens affine hS degree previousS).hom ≫
        (cechHomologyFunctor opens (degree + 2)).map mapping.τ₁ := by
  letI := cohomologyBoundary_epi hS (degree + 1)
  exact naturality_of_boundaries
    (cohomologyBoundary hS (degree + 1)) (cohomologyBoundary hT (degree + 1))
    (schemeCechBoundary opens affine hS (degree + 1))
    (schemeCechBoundary opens affine hT (degree + 1))
    ((cohomologyFunctor X (degree + 1)).map mapping.τ₃)
    ((cohomologyFunctor X (degree + 2)).map mapping.τ₁)
    ((cechHomologyFunctor opens (degree + 1)).map mapping.τ₃)
    ((cechHomologyFunctor opens (degree + 2)).map mapping.τ₁)
    previousS.hom previousT.hom
    (higherStep opens affine hS degree previousS).hom
    (higherStep opens affine hT degree previousT).hom
    (cohomologyBoundary_naturality hS hT mapping (degree + 1))
    (cechBoundary_naturality opens affine hS hT mapping (degree + 1))
    (higherStep_boundary opens affine hS degree previousS)
    (higherStep_boundary opens affine hT degree previousT) previousNatural

end ToricPower.CechNaturality
