module

public import ToricPower.ComplexDiagramTranspose
public import Mathlib.Algebra.Homology.Additive

/-!
# Functorial transposition of complexes of diagrams

All constructions are literal: evaluation recovers the original complex,
map, and differential. In particular quasi-isomorphisms can be checked
at every diagram object without discarding the diagram's morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {L C D : Type*} [Category* L] [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {ι : Type*} {shape : ComplexShape ι}

/-- Actual transposition on natural transformations of complex-valued diagrams. -/
def complexDiagramTransposeMap {F G : L ⥤ HomologicalComplex C shape} (α : F ⟶ G) :
    complexDiagramTranspose F ⟶ complexDiagramTranspose G where
  f q :=
    { app l := (α.app l).f q
      naturality {_ _} f := congrArg (fun u => u.f q) (α.naturality f) }
  comm' q r _ := by
    apply NatTrans.ext
    funext l
    exact (α.app l).comm q r

/-- The literal transposition functor. -/
def complexDiagramTransposeFunctor :
    (L ⥤ HomologicalComplex C shape) ⥤ HomologicalComplex (L ⥤ C) shape where
  obj := complexDiagramTranspose
  map := complexDiagramTransposeMap
  map_id F := by rfl
  map_comp f g := by rfl

/-- Apply any actual complex functor to every object and every arrow of
an actual complex of diagrams. -/
def complexDiagramPostcompose (F : HomologicalComplex C shape ⥤ HomologicalComplex D shape) :
    HomologicalComplex (L ⥤ C) shape ⥤ HomologicalComplex (L ⥤ D) shape :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight L _ _).obj F ⋙ complexDiagramTransposeFunctor

/-- Evaluation of pointwise postcomposition is the original functor. -/
theorem complexDiagramPostcompose_evaluation
    (F : HomologicalComplex C shape ⥤ HomologicalComplex D shape) (l : L) :
    complexDiagramPostcompose F ⋙ ((evaluation L D).obj l).mapHomologicalComplex shape =
      ((evaluation L C).obj l).mapHomologicalComplex shape ⋙ F := rfl

/-- Actual pointwise natural transformations retain every diagram map. -/
def complexDiagramPostcomposeNatTrans
    {F G : HomologicalComplex C shape ⥤ HomologicalComplex D shape} (α : F ⟶ G) :
    complexDiagramPostcompose (L := L) F ⟶ complexDiagramPostcompose G :=
  whiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (whiskerRight ((Functor.whiskeringRight L _ _).map α) complexDiagramTransposeFunctor)

end ToricPower

end
