module

public import ToricPower.ArrangementPowerPushdown
public import ToricPower.ElementPushdownComplexFunctor
public import ToricPower.ElementPushdownExact

/-!
# Functorial coefficient changes in the power direct image

Every fiber consists of all lattice residues. Its finiteness is proved
by its actual definition, so an additive functor suffices to commute
with the sheet coproduct. The complex comparison applies to arbitrary
unbounded complexes and keeps their actual signed differentials.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

universe u v w z

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

local notation "C" => IncidenceObject A
local notation "B" => powerResidueFunctor A ell positive
local notation "p" => powerBranchFunctor A ell positive

instance powerResidueFunctor_finite (c : C) : Finite ((B).obj c) :=
  inferInstanceAs (Finite (LatticeResidues (Fin n) ell))

variable {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]
  {D' : Type w} [Category.{z} D'] [HasCoproducts.{0} D']

/-- The actual whole power direct image commutes with any functor
preserving finite coproducts. -/
def powerDiagramPostcomposeIso (T : D ⥤ D') [PreservesFiniteCoproducts T] :
    powerDiagramPushdown A ell positive D ⋙ (whiskeringRight C D D').obj T ≅
      (whiskeringRight C D D').obj T ⋙ powerDiagramPushdown A ell positive D' := by
  letI (E : (B).Elements ⥤ D) (c : C) :
      PreservesColimit (Discrete.functor (fun r : (B).obj c =>
        E.obj ((B).elementsMk c r))) T := by infer_instance
  exact Functor.isoWhiskerLeft
    ((whiskeringLeft (B).Elements C D).obj p)
    (ElementPushdown.postcomposeDiagramIso B T)

variable [Abelian D] [AB4OfSize.{0} D] [Abelian D'] [AB4OfSize.{0} D']
  {ι : Type*} (shape : ComplexShape ι)

instance powerDiagramPushdown_additive :
    (powerDiagramPushdown A ell positive D).Additive := by
  unfold powerDiagramPushdown
  infer_instance

/-- A whole complex functor commutes with the actual power direct image
when it is additive. No source or coefficient boundedness is required. -/
def powerComplexFunctorIso
    (F : HomologicalComplex D shape ⥤ HomologicalComplex D' shape) [F.Additive] :
    (powerDiagramPushdown A ell positive D).mapHomologicalComplex shape ⋙
        complexDiagramPostcompose (L := C) F ≅
      complexDiagramPostcompose (L := C) F ⋙
        (powerDiagramPushdown A ell positive D').mapHomologicalComplex shape := by
  letI (E : (B).Elements ⥤ HomologicalComplex D shape) (c : C) :
      PreservesColimit (Discrete.functor (fun r : (B).obj c =>
        E.obj ((B).elementsMk c r))) F := by infer_instance
  exact Functor.isoWhiskerLeft
    (((whiskeringLeft (B).Elements C D).obj p).mapHomologicalComplex shape)
    (ElementPushdown.complexFunctorIso B shape F)

end ToricPower.IntegralArrangement

end
