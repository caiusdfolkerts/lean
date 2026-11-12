module

public import ToricPower.AffineExternalSections
public import ToricPower.SchemeExternalSectionDiagram

/-!
# The full affine exterior-section coefficient isomorphism

The component is the canonical map on the original copower generators.
Its isomorphism proof uses the specified affine coordinate tensor product
and the specified frame of each label. Naturality follows from the
canonical exterior product, so no compatibility between independently
chosen frames is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ToricPower

universe u
variable (k : Type u) [Field k]
  (A B P : CommRingCat.{u}) [Algebra k A] [Algebra k B] [Algebra k P]
  (coordinate : A ⊗[k] B ≃ₐ[k] P)
  {C : Type u} [Category.{u} C]
  (Q : C ⥤ (Spec A).Modules) (R : C ⥤ (Spec B).Modules)
  (left : ∀ c, 𝟙_ (Spec A).Modules ≅ Q.obj c)
  (right : ∀ c, 𝟙_ (Spec B).Modules ≅ R.obj c)

local notation "f" => affineExternalFirstMap k A B P coordinate
local notation "g" => affineExternalSecondMap k A B P coordinate

/-- The actual component in the two original frames. -/
def affineExternalSectionDiagramComponentIso (c : C) :
    (Cellular.covariantCopowerDiagram k
      (Q ⋙ FiniteCover.schemeBaseSections k (Spec A) ⊤)
      (R ⋙ FiniteCover.schemeBaseSections k (Spec B) ⊤)).obj c ≅
    (schemeExteriorDiagram f g Q R ⋙ FiniteCover.schemeBaseSections k (Spec P) ⊤).obj c :=
  Cellular.moduleVectorCopowerTensorIso k _ _ ≪≫
    (affineExternalSectionsLinearEquiv k A B P coordinate (left c) (right c)).toModuleIso

/-- This is the canonical component, independently of the frames used
to establish its invertibility. -/
theorem affineExternalSectionDiagramComponentIso_hom (c : C) :
    (affineExternalSectionDiagramComponentIso k A B P coordinate Q R left right c).hom =
      schemeExternalCopowerMap k f g (Q.obj c) (R.obj c) := by
  change (Cellular.moduleVectorCopowerTensorIso k _ _).hom ≫
      ModuleCat.ofHom
        (X := ModuleCat.of k (((FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (Q.obj c)) ⊗[k]
          ((FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (R.obj c))))
        (Y := (FiniteCover.schemeBaseSections k (Spec P) ⊤).obj
          (schemeExteriorSheaf f g (Q.obj c) (R.obj c)))
        (affineExternalSectionsLinearEquiv k A B P coordinate
          (left c) (right c)).toLinearMap = _
  rw [affineExternalSectionsLinearEquiv_eq]
  rfl

/-- A genuine isomorphism of complete coefficient diagrams, retaining
every map in each factor. -/
def affineExternalSectionDiagramIso :
    Cellular.covariantCopowerDiagram k
      (Q ⋙ FiniteCover.schemeBaseSections k (Spec A) ⊤)
      (R ⋙ FiniteCover.schemeBaseSections k (Spec B) ⊤) ≅
    schemeExteriorDiagram f g Q R ⋙ FiniteCover.schemeBaseSections k (Spec P) ⊤ :=
  NatIso.ofComponents (affineExternalSectionDiagramComponentIso k A B P coordinate Q R left right)
    (by
      intro c d a
      rw [affineExternalSectionDiagramComponentIso_hom,
        affineExternalSectionDiagramComponentIso_hom]
      exact (schemeExternalSectionDiagramMap k f g Q R).naturality a)

/-- The coefficient isomorphism sends every original vector generator
to the literal exterior section. -/
theorem affineExternalSectionDiagramIso_inclusion (c : C)
    (s : (FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (Q.obj c))
    (t : (FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (R.obj c)) :
    (affineExternalSectionDiagramIso k A B P coordinate Q R left right).hom.app c
      (Cellular.vectorCopowerInclusion k ((FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (Q.obj c))
        ((FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (R.obj c)) t s) =
        schemeExternalSection k f g (Q.obj c) (R.obj c) s t := by
  change (affineExternalSectionDiagramComponentIso k A B P coordinate Q R left right c).hom
    (Cellular.vectorCopowerInclusion k ((FiniteCover.schemeBaseSections k (Spec A) ⊤).obj (Q.obj c))
        ((FiniteCover.schemeBaseSections k (Spec B) ⊤).obj (R.obj c)) t s) = _
  rw [affineExternalSectionDiagramComponentIso_hom]
  exact schemeExternalCopowerMap_inclusion k f g _ _ s t

end ToricPower

end
