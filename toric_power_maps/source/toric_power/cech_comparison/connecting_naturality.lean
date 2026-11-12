module

public import ToricPower.CechComparison.AllDegreeComparison
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the actual Čech and sheaf-cohomology connecting maps

The ordinary sheaf-cohomology and ordinary Čech connecting maps both
respect actual morphisms of short exact sequences. Degree zero is the
canonical identification with actual global sections on both sides.
These identities are the inputs to a natural all-degree comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDegreeOneComparison

namespace ToricPower.CechNaturality
universe u
variable {X : Scheme.{u}} {Index : Type u}

/-- The actual Čech homology functor on coefficient sheaves. -/
abbrev cechHomologyFunctor (opens : Index → X.Opens) (degree : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  schemeCechComplexFunctor opens ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) degree

/-- The actual ordinary sheaf-cohomology connecting morphism. -/
def cohomologyBoundary {S : ShortComplex X.Modules} (exact : S.ShortExact) (degree : ℕ) :
    AddCommGrpCat.of (Cohomology S.X₃ degree) ⟶
      AddCommGrpCat.of (Cohomology S.X₁ (degree + 1)) :=
  AddCommGrpCat.ofHom (cohomologyδ exact degree (degree + 1) rfl)

@[reassoc]
theorem cohomologyBoundary_naturality {S T : ShortComplex X.Modules}
    (hS : S.ShortExact) (hT : T.ShortExact) (mapping : S ⟶ T) (degree : ℕ) :
    cohomologyBoundary hS degree ≫ (cohomologyFunctor X (degree + 1)).map mapping.τ₁ =
      (cohomologyFunctor X degree).map mapping.τ₃ ≫ cohomologyBoundary hT degree := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  exact cohomologyδ_naturality hS hT mapping degree (degree + 1) rfl value

/-- Naturality of the actual Čech boundary, with actual coefficient maps. -/
@[reassoc]
theorem cechBoundary_naturality [X.IsSeparated]
    (opens : Index → X.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    {S T : ShortComplex X.Modules}
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (hS : S.ShortExact) (hT : T.ShortExact) (mapping : S ⟶ T) (degree : ℕ) :
    schemeCechBoundary opens affine hS degree ≫
        (cechHomologyFunctor opens (degree + 1)).map mapping.τ₁ =
      (cechHomologyFunctor opens degree).map mapping.τ₃ ≫
        schemeCechBoundary opens affine hT degree :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((schemeCechComplexFunctor opens).mapShortComplex.map mapping)
    (schemeCechComplex_shortExact opens affine hS)
    (schemeCechComplex_shortExact opens affine hT) degree (degree + 1) rfl

/-- The canonical degree-zero ordinary cohomology identification is natural. -/
@[reassoc]
theorem cohomologyZeroIso_naturality {M N : X.Modules} (mapping : M ⟶ N) :
    (cohomologyFunctor X 0).map mapping ≫ (cohomologyZeroEquiv N).toAddCommGrpIso.hom =
      (cohomologyZeroEquiv M).toAddCommGrpIso.hom ≫ mapping.app ⊤ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  exact cohomologyZeroEquiv_cohomologyMap mapping value

/-- Degree zero agrees with actual global sections on both sides. -/
def zeroIso (opens : Index → X.Opens) (cover : iSup opens = ⊤) (M : X.Modules) :
    AddCommGrpCat.of (Cohomology M 0) ≅ (schemeCechComplex opens M).homology 0 :=
  (cohomologyZeroEquiv M).toAddCommGrpIso ≪≫ cechZeroGlobalSectionsIso opens cover M

@[reassoc]
theorem zeroIso_naturality (opens : Index → X.Opens) (cover : iSup opens = ⊤)
    {M N : X.Modules} (mapping : M ⟶ N) :
    (cohomologyFunctor X 0).map mapping ≫ (zeroIso opens cover N).hom =
      (zeroIso opens cover M).hom ≫ (cechHomologyFunctor opens 0).map mapping := by
  simp only [zeroIso, Iso.trans_hom]
  rw [← Category.assoc, cohomologyZeroIso_naturality, Category.assoc,
    cechZeroGlobalSectionsIso_naturality, ← Category.assoc]
  rfl

end ToricPower.CechNaturality
