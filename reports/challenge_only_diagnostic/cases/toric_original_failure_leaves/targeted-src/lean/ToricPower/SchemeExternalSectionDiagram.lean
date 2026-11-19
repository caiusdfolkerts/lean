module

public import ToricPower.SchemeExternalSections
public import ToricPower.ModuleVectorCopowerTensor
public import ToricPower.CellularCovariantLabels

/-! # The canonical exterior product on full coefficient diagrams -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ToricPower

universe u
variable (k : Type u) [Field k]
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (f : Z ⟶ X) (g : Z ⟶ Y)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- The canonical section map on the original categorical copower. -/
def schemeExternalCopowerMap (L : X.Modules) (M : Y.Modules) :
    Cellular.vectorCopower k ((FiniteCover.schemeBaseSections k X ⊤).obj L)
      ((FiniteCover.schemeBaseSections k Y ⊤).obj M) ⟶
        (FiniteCover.schemeBaseSections k Z ⊤).obj (schemeExteriorSheaf f g L M) :=
  (Cellular.moduleVectorCopowerTensorIso k _ _).hom ≫
    ModuleCat.ofHom
      (X := ModuleCat.of k (((FiniteCover.schemeBaseSections k X ⊤).obj L) ⊗[k]
        ((FiniteCover.schemeBaseSections k Y ⊤).obj M)))
      (Y := (FiniteCover.schemeBaseSections k Z ⊤).obj (schemeExteriorSheaf f g L M))
      (schemeExternalSectionsLinearMap k f g L M)

@[simp]
theorem schemeExternalCopowerMap_inclusion (L : X.Modules) (M : Y.Modules)
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k Y ⊤).obj M) :
    schemeExternalCopowerMap k f g L M
      (Cellular.vectorCopowerInclusion k ((FiniteCover.schemeBaseSections k X ⊤).obj L)
        ((FiniteCover.schemeBaseSections k Y ⊤).obj M) t s) =
      schemeExternalSection k f g L M s t := by
  change schemeExternalSectionsLinearMap k f g L M
    (Cellular.moduleCopowerTensorMap k ((FiniteCover.schemeBaseSections k X ⊤).obj L)
      ((FiniteCover.schemeBaseSections k Y ⊤).obj M)
      (Cellular.vectorCopowerInclusion k ((FiniteCover.schemeBaseSections k X ⊤).obj L)
        ((FiniteCover.schemeBaseSections k Y ⊤).obj M) t s)) = _
  rw [Cellular.moduleCopowerTensorMap_inclusion, schemeExternalSectionsLinearMap_tmul]

variable {C : Type u} [Category.{u} C] (Q : C ⥤ X.Modules) (R : C ⥤ Y.Modules)

/-- Actual pullback and tensor in both coefficient factors. -/
def schemeExteriorDiagram : C ⥤ Z.Modules where
  obj c := schemeExteriorSheaf f g (Q.obj c) (R.obj c)
  map a := (Scheme.Modules.pullback f).map (Q.map a) ⊗ₘ
    (Scheme.Modules.pullback g).map (R.map a)
  map_id c := by simp only [CategoryTheory.Functor.map_id, id_tensorHom_id]
  map_comp a b := by
    simp only [CategoryTheory.Functor.map_comp, tensorHom_comp_tensorHom]

/-- Every incidence map acts through the canonical exterior product. -/
def schemeExternalSectionDiagramMap :
    Cellular.covariantCopowerDiagram k
      (Q ⋙ FiniteCover.schemeBaseSections k X ⊤)
      (R ⋙ FiniteCover.schemeBaseSections k Y ⊤) ⟶
    schemeExteriorDiagram f g Q R ⋙ FiniteCover.schemeBaseSections k Z ⊤ where
  app c := schemeExternalCopowerMap k f g (Q.obj c) (R.obj c)
  naturality {c d} a := by
    apply Cellular.vectorCopower_hom_ext k _ _
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    have inclusion := ConcreteCategory.congr_hom
      (Cellular.covariantCopowerDiagram_map_inclusion k
        (Q ⋙ FiniteCover.schemeBaseSections k X ⊤)
        (R ⋙ FiniteCover.schemeBaseSections k Y ⊤) a t) s
    have first := schemeExternalCopowerMap_inclusion k f g (Q.obj d) (R.obj d)
      ((FiniteCover.schemeBaseSections k X ⊤).map (Q.map a) s)
      ((FiniteCover.schemeBaseSections k Y ⊤).map (R.map a) t)
    have middle := schemeExternalSection_naturality k f g (Q.obj c) (R.obj c)
      (Q.map a) (R.map a) s t
    have last := congrArg
      ((FiniteCover.schemeBaseSections k Z ⊤).map
        ((Scheme.Modules.pullback f).map (Q.map a) ⊗ₘ
          (Scheme.Modules.pullback g).map (R.map a)))
      (schemeExternalCopowerMap_inclusion k f g (Q.obj c) (R.obj c) s t)
    exact (congrArg (schemeExternalCopowerMap k f g (Q.obj d) (R.obj d)) inclusion).trans
      (first.trans (middle.trans last.symm))

end ToricPower

end
