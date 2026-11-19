module

public import ToricPower.CellularCovariantLabels
public import ToricPower.CellularFoundations
public import ToricPower.LinearVectorCopowerComparison
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Actual evaluation of a represented cellular coefficient

For covariant labels `Q` and `R`, every genuine incidence `c ⟶ d`
evaluates the corresponding copy of `Q(d) ⊗ R(c)` by the literal map
`Q(d) ◁ R.map f`. The resulting maps form a natural transformation.
This is the coefficient-level map used before the actual cellular
cochain functor and the actual diagonal top quotient are applied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower.Cellular

universe u v w

section FreeGenerators

variable (k : Type u) [Field k]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  {B : Type w} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} A] [HasCoproducts.{u} B]
  (F : A ⥤ B) [F.Additive] [F.Linear k]
  [PreservesColimitsOfSize.{u,u} F]

/-- For a free vector coefficient it suffices to check the actual
free generators; the copied object and its image may be arbitrary. -/
theorem map_vectorCopower_free_hom_ext (P : A) (I : Type u) {E : B}
    {f g : F.obj (vectorCopower k P ((ModuleCat.free k).obj I)) ⟶ E}
    (equal : ∀ i : I,
      F.map (vectorCopowerInclusion k P ((ModuleCat.free k).obj I) (ModuleCat.freeMk i)) ≫ f =
        F.map (vectorCopowerInclusion k P ((ModuleCat.free k).obj I)
          (ModuleCat.freeMk i)) ≫ g) : f = g := by
  let left : (ModuleCat.free k).obj I ⟶ ModuleCat.of k (F.obj P ⟶ E) :=
    ModuleCat.ofHom ((Linear.rightComp k (F.obj P) f).comp
      ((F.mapLinearMap k).comp (vectorCopowerInclusion k P ((ModuleCat.free k).obj I))))
  let right : (ModuleCat.free k).obj I ⟶ ModuleCat.of k (F.obj P ⟶ E) :=
    ModuleCat.ofHom ((Linear.rightComp k (F.obj P) g).comp
      ((F.mapLinearMap k).comp (vectorCopowerInclusion k P ((ModuleCat.free k).obj I))))
  have same : left = right := by
    apply ModuleCat.free_hom_ext
    intro i
    exact equal i
  apply map_vectorCopower_hom_ext k F P ((ModuleCat.free k).obj I)
  intro x
  exact ConcreteCategory.congr_hom same x

end FreeGenerators

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{u} B]
  (Q R : C ⥤ B) (c : C)
  [PreservesColimitsOfSize.{u,u} ((tensoringRight B).obj (R.obj c))]

/-- Pointwise tensor of the two actual covariant label diagrams. -/
def covariantTensorDiagram : C ⥤ B where
  obj d := Q.obj d ⊗ R.obj d
  map f := Q.map f ⊗ₘ R.map f
  map_id d := by simp
  map_comp f g := by simp

/-- Evaluation on one genuine cell, using the actual universal property
of vector copowers and the actual free incidence module. -/
def representedTensorEvaluation (d : C) :
    vectorCopower k (Q.obj d) ((representable k c).obj d) ⊗ R.obj c ⟶
      Q.obj d ⊗ R.obj d :=
  (vectorCopowerComparisonIso k ((tensoringRight B).obj (R.obj c))
    (Q.obj d) ((representable k c).obj d)).hom ≫
      (vectorCopowerHomEquiv k (Q.obj d ⊗ R.obj c)
        ((representable k c).obj d) (Q.obj d ⊗ R.obj d)).symm
          (ModuleCat.freeDesc (↾fun f : c ⟶ d => Q.obj d ◁ R.map f))

/-- Each original incidence generator evaluates by its original label
map, with coefficient one and no replacement of the hom-set. -/
@[reassoc]
theorem representedTensorEvaluation_generator (d : C) (f : c ⟶ d) :
    vectorCopowerInclusion k (Q.obj d) ((representable k c).obj d)
        (ModuleCat.freeMk f) ▷ R.obj c ≫ representedTensorEvaluation k Q R c d =
      Q.obj d ◁ R.map f := by
  change ((tensoringRight B).obj (R.obj c)).map
      (vectorCopowerInclusion k (Q.obj d) ((representable k c).obj d)
        (ModuleCat.freeMk f)) ≫ _ = _
  unfold representedTensorEvaluation
  rw [← Category.assoc, vectorCopowerComparisonIso_inclusion]
  change vectorCopowerInclusion k (Q.obj d ⊗ R.obj c)
      ((ModuleCat.free k).obj (c ⟶ d)) (ModuleCat.freeMk f) ≫
      (vectorCopowerHomEquiv k (Q.obj d ⊗ R.obj c)
        ((ModuleCat.free k).obj (c ⟶ d)) (Q.obj d ⊗ R.obj d)).symm
          (ModuleCat.freeDesc (↾fun g : c ⟶ d => Q.obj d ◁ R.map g)) = _
  rw [vectorCopowerInclusion_desc, ModuleCat.freeDesc_apply]
  rfl

/-- Actual incidence composition proves the full coefficient square. -/
theorem representedTensorEvaluation_natural {d e : C} (h : d ⟶ e) :
    (covariantCopowerDiagram k Q (representable k c)).map h ▷ R.obj c ≫
        representedTensorEvaluation k Q R c e =
      representedTensorEvaluation k Q R c d ≫
        (covariantTensorDiagram Q R).map h := by
  apply map_vectorCopower_free_hom_ext k ((tensoringRight B).obj (R.obj c))
    (Q.obj d) (c ⟶ d)
  intro f
  change vectorCopowerInclusion k (Q.obj d) ((representable k c).obj d)
      (ModuleCat.freeMk f) ▷ R.obj c ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight,
    covariantCopowerDiagram_map_inclusion, representable_map_freeMk,
    comp_whiskerRight, Category.assoc, representedTensorEvaluation_generator,
    ← Category.assoc]
  change Q.map h ▷ R.obj c ≫ Q.obj e ◁ R.map (f ≫ h) =
    (vectorCopowerInclusion k (Q.obj d) ((representable k c).obj d)
      (ModuleCat.freeMk f) ▷ R.obj c ≫ representedTensorEvaluation k Q R c d) ≫
        (covariantTensorDiagram Q R).map h
  rw [representedTensorEvaluation_generator]
  change Q.map h ▷ R.obj c ≫ Q.obj e ◁ R.map (f ≫ h) =
    Q.obj d ◁ R.map f ≫ (Q.map h ⊗ₘ R.map h)
  rw [Functor.map_comp, whiskerLeft_comp, ← Category.assoc,
    ← tensorHom_def, tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom]

/-- The resulting genuine natural transformation exists before any
cellular or derived identification is asserted. -/
def representedTensorEvaluationDiagram :
    covariantCopowerDiagram k Q (representable k c) ⋙
        (tensoringRight B).obj (R.obj c) ⟶ covariantTensorDiagram Q R where
  app d := representedTensorEvaluation k Q R c d
  naturality {d e} h := representedTensorEvaluation_natural k Q R c h

end ToricPower.Cellular

end
