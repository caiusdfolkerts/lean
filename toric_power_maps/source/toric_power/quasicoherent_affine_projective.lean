module

public import ToricPower.QuasicoherentCartierTensor
public import ToricPower.ModuleUnitSections
public import ToricPower.CartierRepresentation
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Actual invertible quasicoherent sheaves are projective on integral affines

The structure sheaf is projective in the actual quasicoherent category
of an affine scheme: an actual epimorphism is surjective on global
sections, and a section is exactly a morphism from the structure sheaf.
The proved Cartier tensor equivalence transports this projectivity to
Cartier sheaves. The proved Cartier representation then gives the result
for every actual invertible sheaf on an integral affine scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

local instance affineProjectiveOver (X : Scheme.{u}) :
    X.Over (Spec (.of Γ(X, ⊤))) := ⟨X.toSpecΓ⟩

/-- The actual structure sheaf as an actual quasicoherent object. -/
def quasicoherentUnitObject (X : Scheme.{u}) : QCoh X :=
  ⟨𝟙_ X.Modules, inferInstance⟩

/-- Global-section lifting proves projectivity of the actual structure
sheaf on any affine scheme. -/
theorem quasicoherentAffineUnit_projective (X : Scheme.{u}) [IsAffine X] :
    Projective (quasicoherentUnitObject X) where
  factors {M N} f e := by
    intro _
    letI : Epi e.hom := inferInstanceAs (Epi ((quasicoherentInclusion X).map e))
    obtain ⟨s, hs⟩ := affineSections_surjective_of_epi e.hom (isAffineOpen_top X)
      (Scheme.Modules.Hom.app f.hom ⊤ (1 : Γ(X, ⊤)))
    let lift : 𝟙_ X.Modules ⟶ M.obj :=
      (moduleUnitSectionsLinearEquiv Γ(X, ⊤) X M.obj).symm s
    refine ⟨ObjectProperty.homMk lift, ?_⟩
    apply ObjectProperty.hom_ext
    apply (moduleUnitSectionsLinearEquiv Γ(X, ⊤) X N.obj).injective
    change Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app lift ⊤ (1 : Γ(X, ⊤))) = Scheme.Modules.Hom.app f.hom ⊤ (1 : Γ(X, ⊤))
    have value : Scheme.Modules.Hom.app lift ⊤ (1 : Γ(X, ⊤)) = s :=
      (moduleUnitSectionsLinearEquiv Γ(X, ⊤) X M.obj).apply_symm_apply s
    rw [value]
    exact hs

/-- Cartier sheaves are projective on an integral affine scheme, by
the actual exact equivalence of quasicoherent tensor categories. -/
theorem quasicoherentAffineCartier_projective (X : Scheme.{u})
    [IsAffine X] [IsIntegral X] (D : CartierDivisor X) :
    Projective (⟨D.sheaf, inferInstance⟩ : QCoh X) := by
  letI := quasicoherentAffineUnit_projective X
  let F := (quasicoherentCartierTensorEquivalence D).functor
  letI : Projective (F.obj (quasicoherentUnitObject X)) := inferInstance
  let comparison : F.obj (quasicoherentUnitObject X) ≅
      (⟨D.sheaf, inferInstance⟩ : QCoh X) :=
    ObjectProperty.isoMk (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (ρ_ D.sheaf)
  exact Projective.of_iso comparison inferInstance

/-- Every actual invertible quasicoherent sheaf is projective on an
integral affine scheme. Cartier representability is proved upstream and
is used here to transport projectivity along an actual sheaf isomorphism. -/
theorem quasicoherentAffineInvertible_projective (X : Scheme.{u})
    [IsAffine X] [IsIntegral X] (M : QCoh X)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M.obj] :
    Projective M := by
  obtain ⟨D, ⟨comparison⟩⟩ :=
    CartierDivisor.exists_nonempty_iso_sheaf
      (⟨M.obj, inferInstance⟩ : TauCeti.AlgebraicGeometry.InvertibleSheaf X)
  letI := quasicoherentAffineCartier_projective X D
  let represented : (⟨D.sheaf, inferInstance⟩ : QCoh X) ≅ M :=
    ObjectProperty.isoMk (SheafOfModules.isQuasicoherent X.ringCatSheaf) comparison.symm
  exact Projective.of_iso represented inferInstance

end ToricPower
