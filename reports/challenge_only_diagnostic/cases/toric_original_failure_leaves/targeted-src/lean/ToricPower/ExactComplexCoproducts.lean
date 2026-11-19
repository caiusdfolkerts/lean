module

public import ToricPower.ComplexDiagramFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.Grp.AB

/-! # Exact coproducts of full complexes and natural comparisons

Exact coefficient colimits preserve objectwise quasi-isomorphisms of
arbitrary complexes. The comparison is the canonical colimit map.
Consequently a natural map between coproduct-preserving complex-valued
functors is a quasi-isomorphism on a full coproduct whenever it is one
on every summand.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex

namespace ToricPower

universe u v w z
variable {A : Type u} [Category.{v} A] [Abelian A]
  {J : Type w} [Category.{z} J]
  {ι : Type*} {shape : ComplexShape ι}

variable [HasColimitsOfShape J A]

def complexColimitIso (F : J ⥤ HomologicalComplex A shape) :
    colimit F ≅ ((colim (J := J) (C := A)).mapHomologicalComplex shape).obj
      (complexDiagramTranspose F) :=
  colimit.isoColimitCocone
    ⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩

@[reassoc]
theorem complexColimitIso_inclusion (F : J ⥤ HomologicalComplex A shape) (j : J) (q : ι) :
    (colimit.ι F j).f q ≫ (complexColimitIso F).hom.f q =
      colimit.ι (F ⋙ HomologicalComplex.eval A shape q) j := by
  have h := colimit.isoColimitCocone_ι_hom
    ⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩ j
  exact congrArg (fun f => f.f q) h

theorem complexColimitIso_naturality {F G : J ⥤ HomologicalComplex A shape} (α : F ⟶ G) :
    colim.map α ≫ (complexColimitIso G).hom =
      (complexColimitIso F).hom ≫
        ((colim (J := J) (C := A)).mapHomologicalComplex shape).map
          (complexDiagramTransposeMap α) := by
  apply colimit.hom_ext
  intro j
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f,← Category.assoc]
  change ((colimit.ι F j ≫ colim.map α).f q) ≫ _ = _
  rw [colimit.ι_map]
  simp only [HomologicalComplex.comp_f,Category.assoc,complexColimitIso_inclusion]
  change (α.app j).f q ≫ colimit.ι (G ⋙ HomologicalComplex.eval A shape q) j =
    colimit.ι (F ⋙ HomologicalComplex.eval A shape q) j ≫
      colim.map (whiskerRight α (HomologicalComplex.eval A shape q))
  exact (colimit.ι_map (whiskerRight α (HomologicalComplex.eval A shape q)) j).symm

variable [HasExactColimitsOfShape J A]

theorem complex_colimitMap_quasiIso {F G : J ⥤ HomologicalComplex A shape} (α : F ⟶ G)
    [∀ j, QuasiIso (α.app j)] : QuasiIso (colim.map α) := by
  haveI : QuasiIso (complexDiagramTransposeMap α) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    change QuasiIso (α.app j)
    infer_instance
  haveI : QuasiIso (((colim (J := J) (C := A)).mapHomologicalComplex shape).map
      (complexDiagramTransposeMap α)) := inferInstance
  have equality : colim.map α = (complexColimitIso F).hom ≫
      ((colim (J := J) (C := A)).mapHomologicalComplex shape).map
        (complexDiagramTransposeMap α) ≫ (complexColimitIso G).inv := by
    calc
      colim.map α = (colim.map α ≫ (complexColimitIso G).hom) ≫
          (complexColimitIso G).inv := by simp
      _ = _ := by rw [complexColimitIso_naturality]; simp only [Category.assoc]
  rw [equality]
  infer_instance

end ToricPower

end
