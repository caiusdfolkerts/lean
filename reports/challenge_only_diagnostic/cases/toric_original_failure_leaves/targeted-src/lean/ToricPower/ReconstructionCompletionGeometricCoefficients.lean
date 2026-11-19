module

public import ToricPower.CovariantRepresentableEvaluation
public import ToricPower.SchemeExternalSections
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Evaluation of actual inverse-twist sections

A section of `R ⊗ E` is its actual map from the unit. Evaluation of that
map on a copower of `Q` gives a map to `(Q ⊗ R) ⊗ E`. This construction is
natural in all three factors. It supplies the geometric cellular
augmentation directly, without identifying two independently normalized
Cartier adjunctions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{u} B]

/-- Evaluation of a literal unit-source section, including its unit
and associativity maps. -/
def unitTensorEvaluation (Q R E : B) :
    vectorCopower k Q (ModuleCat.of k (𝟙_ B ⟶ R ⊗ E)) ⟶ (Q ⊗ R) ⊗ E :=
  (vectorCopowerHomEquiv k Q (ModuleCat.of k (𝟙_ B ⟶ R ⊗ E)) ((Q ⊗ R) ⊗ E)).symm
    (ModuleCat.ofHom
      ((Linear.rightComp k Q (α_ Q R E).inv).comp
        ((Linear.leftComp k (Q ⊗ (R ⊗ E)) (ρ_ Q).inv).comp
          ((tensorLeft Q).mapLinearMap k))))

@[reassoc]
theorem unitTensorEvaluation_generator (Q R E : B) (s : 𝟙_ B ⟶ R ⊗ E) :
    vectorCopowerInclusion k Q (ModuleCat.of k (𝟙_ B ⟶ R ⊗ E)) s ≫
        unitTensorEvaluation k Q R E =
      (ρ_ Q).inv ≫ Q ◁ s ≫ (α_ Q R E).inv := by
  rw [unitTensorEvaluation, vectorCopowerInclusion_desc]
  exact Category.assoc _ _ _

/-- The complete coefficient square retains the actual maps of both
label factors and the arbitrary coefficient object. -/
theorem unitTensorEvaluation_naturality {Q Q' R R' E E' : B}
    (f : Q ⟶ Q') (g : R ⟶ R') (h : E ⟶ E') :
    vectorCopowerMapObject k f (ModuleCat.of k (𝟙_ B ⟶ R ⊗ E)) ≫
        (vectorCopowerFunctor k Q').map
          (ModuleCat.ofHom (Linear.rightComp k (𝟙_ B) (g ⊗ₘ h))) ≫
        unitTensorEvaluation k Q' R' E' =
      unitTensorEvaluation k Q R E ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
  apply vectorCopower_hom_ext k Q (ModuleCat.of k (𝟙_ B ⟶ R ⊗ E))
  intro s
  rw [vectorCopowerInclusion_mapObject_assoc,
    vectorCopowerInclusion_map_assoc, unitTensorEvaluation_generator,
    unitTensorEvaluation_generator_assoc]
  change f ≫ (ρ_ Q').inv ≫ Q' ◁ (s ≫ (g ⊗ₘ h)) ≫ (α_ Q' R' E').inv =
    (ρ_ Q).inv ≫ Q ◁ s ≫ (α_ Q R E).inv ≫ ((f ⊗ₘ g) ⊗ₘ h)
  simp only [whiskerLeft_comp, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    ← tensorHom_def_assoc, associator_inv_naturality]

variable {C : Type u} [Category.{u} C] (Q R : C ⥤ B)

/-- The original inverse-twist unit Hom diagram. -/
def unitTensorSectionDiagram (E : B) : C ⥤ ModuleCat.{u} k :=
  R ⋙ tensorRight E ⋙ (linearCoyoneda k B).obj (op (𝟙_ B))

/-- Every original incidence is retained by the coefficient evaluation. -/
def unitTensorEvaluationDiagram (E : B) :
    covariantCopowerDiagram k Q (unitTensorSectionDiagram k R E) ⟶
      covariantTensorDiagram Q R ⋙ tensorRight E where
  app c := unitTensorEvaluation k (Q.obj c) (R.obj c) E
  naturality {c d} f := by
    change (vectorCopowerMapObject k (Q.map f)
        (ModuleCat.of k (𝟙_ B ⟶ R.obj c ⊗ E)) ≫
      (vectorCopowerFunctor k (Q.obj d)).map
        (ModuleCat.ofHom (Linear.rightComp k (𝟙_ B) (R.map f ▷ E)))) ≫
        unitTensorEvaluation k (Q.obj d) (R.obj d) E =
      unitTensorEvaluation k (Q.obj c) (R.obj c) E ≫ (Q.map f ⊗ₘ R.map f) ▷ E
    simpa only [Category.assoc, tensorHom_id]
      using unitTensorEvaluation_naturality k (Q.map f) (R.map f) (𝟙 E)

/-- The section diagram varies naturally over all coefficient objects. -/
def unitTensorSectionFunctor : B ⥤ C ⥤ ModuleCat.{u} k :=
  (R ⋙ tensoringLeft B).flip ⋙
    (Functor.whiskeringRight C B (ModuleCat.{u} k)).obj
      ((linearCoyoneda k B).obj (op (𝟙_ B)))

end ToricPower.Cellular

namespace ToricPower

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The section-to-unit-Hom comparison is natural on the full module
sheaf category and uses the original evaluation at one. -/
def reconstructionUnitHomSectionsIso :
    (linearCoyoneda k X.Modules).obj (op (𝟙_ X.Modules)) ≅
      FiniteCover.schemeBaseSections k X ⊤ :=
  NatIso.ofComponents (fun M => (moduleUnitActualSectionsLinearEquiv k X M).toModuleIso)
    (by
      intro M N f
      ext s
      rfl)

/-- The same actual section comparison in the full quasicoherent
subcategory. Its morphisms remain the original sheaf morphisms. -/
def reconstructionQuasicoherentUnitHomSectionsIso :
    (linearCoyoneda k (QCoh X)).obj (op (𝟙_ (QCoh X))) ≅
      quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤ :=
  NatIso.ofComponents (fun M =>
    ((quasicoherentUnderlyingHomLinearEquiv k X (𝟙_ (QCoh X)) M).trans
      (moduleUnitActualSectionsLinearEquiv k X M.obj)).toModuleIso)
    (by
      intro M N f
      ext s
      rfl)

end ToricPower

end
