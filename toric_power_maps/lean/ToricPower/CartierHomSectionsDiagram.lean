module

public import ToricPower.CartierSourceFunctor
public import ToricPower.CellularHomDiagram
public import ToricPower.ModuleUnitSections
public import ToricPower.SheafTensorBaseLinear
public import ToricPower.QuasicoherentBaseLinear
public import ToricPower.FiniteAffineIntersectionSections

/-!
# Actual Cartier Hom diagrams and inverse-twist sections

The tensor adjunction identifies a morphism from a Cartier line with a
section of its inverse twist. This file retains the specified base-field
linear structures and both naturalities: actual coefficient morphisms and
every actual source-line morphism. Source maps on the section side are
the conjugate transformations of the genuine tensor adjunctions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

section LinearAdjunction

variable (k : Type*) [CommRing k]
  {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
  {F : C ⥤ D} {G : D ⥤ C} [G.Additive] [G.Linear k]

/-- The ordinary adjunction equivalence preserves the actual scalar actions. -/
def adjunctionHomLinearEquiv (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[k] (X ⟶ G.obj Y) :=
  { adj.homEquiv X Y with
    map_add' f g := by
      change adj.unit.app X ≫ G.map (f+g) =
        (adj.unit.app X ≫ G.map f) + (adj.unit.app X ≫ G.map g)
      rw [G.map_add, Preadditive.comp_add]
    map_smul' r f := by
      change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
      rw [G.map_smul, Linear.comp_smul] }

end LinearAdjunction

section AdjunctionMates

variable {C D : Type*} [Category* C] [Category* D]
  {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}

/-- Ordinary Hom adjunction commutes with the actual conjugate transformation. -/
theorem homEquiv_conjugate (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    (α : F₂ ⟶ F₁) {X : C} {Y : D} (f : F₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ f) =
      adj₁.homEquiv X Y f ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, G₂.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv adj₁ adj₂ α X,
    Category.assoc, ← (conjugateEquiv adj₁ adj₂ α).naturality f,
    Category.assoc]

end AdjunctionMates

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X]

local instance : Linear k (_root_.SheafOfModules X.ringCatSheaf) :=
  Scheme.Modules.baseLinear k X

local instance cartierInverseTensorLinear (D : CartierDivisor X) :
    (cartierTensorEquivalence D).inverse.Linear k := by
  change (tensorLeft (-D).sheaf).Linear k
  infer_instance

/-- The inherited quasicoherent Hom module is the actual sheaf Hom module. -/
def quasicoherentUnderlyingHomLinearEquiv (M N : QCoh X) :
    (M ⟶ N) ≃ₗ[k] (M.obj ⟶ N.obj) where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual tensor-adjunction transpose, including its right-unit map. -/
def cartierHomUnitLinearEquiv (D : CartierDivisor X) (M : X.Modules) :
    (D.sheaf ⟶ M) ≃ₗ[k] (𝟙_ X.Modules ⟶ (-D).sheaf ⊗ M) :=
  (Linear.homCongr k (ρ_ D.sheaf).symm (Iso.refl M)).trans
    (adjunctionHomLinearEquiv k (cartierTensorEquivalence D).toAdjunction
      (𝟙_ X.Modules) M)

theorem cartierHomUnitLinearEquiv_apply (D : CartierDivisor X) (M : X.Modules)
    (f : D.sheaf ⟶ M) :
    cartierHomUnitLinearEquiv k X D M f =
      (cartierTensorEquivalence D).toAdjunction.homEquiv (𝟙_ X.Modules) M
        ((ρ_ D.sheaf).hom ≫ f) := by
  simp only [cartierHomUnitLinearEquiv, LinearEquiv.trans_apply,
    adjunctionHomLinearEquiv, Linear.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  rfl

/-- A Cartier-source map is sent to its actual conjugate inverse-twist map. -/
theorem cartierHomUnitLinearEquiv_source {D E : CartierDivisor X}
    (f : D.sheaf ⟶ E.sheaf) (M : X.Modules) (g : E.sheaf ⟶ M) :
    cartierHomUnitLinearEquiv k X D M (f ≫ g) =
      cartierHomUnitLinearEquiv k X E M g ≫ (cartierDualTwistMap X f).app M := by
  rw [cartierHomUnitLinearEquiv_apply, cartierHomUnitLinearEquiv_apply,
    ← Category.assoc, ← rightUnitor_naturality f, Category.assoc]
  exact homEquiv_conjugate (cartierTensorEquivalence E).toAdjunction
    (cartierTensorEquivalence D).toAdjunction ((tensoringLeft X.Modules).map f)
    ((ρ_ E.sheaf).hom ≫ g)

/-- Coefficient maps act by the genuine inverse tensor functor. -/
theorem cartierHomUnitLinearEquiv_coefficient (D : CartierDivisor X)
    {M N : X.Modules} (f : M ⟶ N) (g : D.sheaf ⟶ M) :
    cartierHomUnitLinearEquiv k X D N (g ≫ f) =
      cartierHomUnitLinearEquiv k X D M g ≫ (tensorLeft (-D).sheaf).map f := by
  rw [cartierHomUnitLinearEquiv_apply, cartierHomUnitLinearEquiv_apply,
    ← Category.assoc]
  exact (cartierTensorEquivalence D).toAdjunction.homEquiv_naturality_right _ _

/-- Evaluating the adjunction transpose at one gives the actual global section. -/
def moduleUnitActualSectionsLinearEquiv (M : X.Modules) :
    (𝟙_ X.Modules ⟶ M) ≃ₗ[k] (FiniteCover.schemeBaseSections k X ⊤).obj M :=
  { (moduleUnitSectionsLinearEquiv k X M).toEquiv with
    map_add' f g := rfl
    map_smul' r f := by
      change (r • f).app ⊤ (1 : Γ(X, ⊤)) = _
      exact Scheme.Modules.base_smul_app k X r f ⊤ (1 : Γ(X, ⊤)) }

/-- The full section comparison uses the actual restricted-scalar section module. -/
def cartierHomSectionsLinearEquiv (D : CartierDivisor X) (M : X.Modules) :
    (D.sheaf ⟶ M) ≃ₗ[k]
      (FiniteCover.schemeBaseSections k X ⊤).obj ((-D).sheaf ⊗ M) :=
  (cartierHomUnitLinearEquiv k X D M).trans
    (moduleUnitActualSectionsLinearEquiv k X ((-D).sheaf ⊗ M))

theorem cartierHomSectionsLinearEquiv_source {D E : CartierDivisor X}
    (f : D.sheaf ⟶ E.sheaf) (M : X.Modules) (g : E.sheaf ⟶ M) :
    cartierHomSectionsLinearEquiv k X D M (f ≫ g) =
      (FiniteCover.schemeBaseSections k X ⊤).map ((cartierDualTwistMap X f).app M)
        (cartierHomSectionsLinearEquiv k X E M g) := by
  change (cartierHomUnitLinearEquiv k X D M (f ≫ g)).app ⊤ (1 : Γ(X, ⊤)) = _
  rw [cartierHomUnitLinearEquiv_source]
  rfl

theorem cartierHomSectionsLinearEquiv_coefficient (D : CartierDivisor X)
    {M N : X.Modules} (f : M ⟶ N) (g : D.sheaf ⟶ M) :
    cartierHomSectionsLinearEquiv k X D N (g ≫ f) =
      (FiniteCover.schemeBaseSections k X ⊤).map ((tensorLeft (-D).sheaf).map f)
        (cartierHomSectionsLinearEquiv k X D M g) := by
  change (cartierHomUnitLinearEquiv k X D N (g ≫ f)).app ⊤ (1 : Γ(X, ⊤)) = _
  rw [cartierHomUnitLinearEquiv_coefficient]
  rfl

variable {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ CartierSources X)

/-- The actual inverse-Cartier-twist section diagrams, for all coefficients. -/
def cartierSourcesSectionDiagram : QCoh X ⥤ C ⥤ ModuleCat.{u} k :=
  (P.rightOp ⋙ cartierSourcesQuasicoherentInverseTensor X ⋙
    (Functor.whiskeringRight (QCoh X) (QCoh X) (ModuleCat.{u} k)).obj
      (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤)).flip

/-- The comparison is natural in the whole source diagram and in every
quasicoherent coefficient sheaf, over the actual base field. -/
def cartierHomSectionsDiagramIso :
    Cellular.homDiagram k (P ⋙ cartierSourcesQuasicoherent X) ≅
      cartierSourcesSectionDiagram k X P :=
  NatIso.ofComponents (fun M => NatIso.ofComponents
    (fun c => ((quasicoherentUnderlyingHomLinearEquiv k X
        ((cartierSourcesQuasicoherent X).obj (P.obj (op c))) M).trans
      (cartierHomSectionsLinearEquiv k X
        (cartierSourceDivisor X (P.obj (op c))) M.obj)).toModuleIso)
    (by
      intro c d f
      ext g
      exact cartierHomSectionsLinearEquiv_source k X (P.map f.op).hom M.obj g.hom))
    (by
      intro M N f
      apply NatTrans.ext
      funext c
      ext g
      exact cartierHomSectionsLinearEquiv_coefficient k X
        (cartierSourceDivisor X (P.obj (op c))) f.hom g.hom)

end ToricPower

end
