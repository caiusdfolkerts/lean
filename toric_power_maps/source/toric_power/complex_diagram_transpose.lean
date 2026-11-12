module

public import Mathlib.Algebra.Homology.Functor

/-!
# Complex-valued diagrams as complexes of diagrams

This is the literal converse to `HomologicalComplex.asFunctor`. It retains
every object, differential, and incidence map, and introduces no derived
replacement. It lets exact functors on coefficient diagrams act on the
whole diagram of complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D]
  {ι : Type*} {shape : ComplexShape ι}

/-- Transposition of a diagram of actual complexes. -/
def complexDiagramTranspose (F : C ⥤ HomologicalComplex D shape) :
    HomologicalComplex (C ⥤ D) shape where
  X q := F ⋙ HomologicalComplex.eval D shape q
  d q r :=
    { app := fun c => (F.obj c).d q r
      naturality := fun _ _ f => (F.map f).comm q r }
  shape q r h := by
    ext c
    exact (F.obj c).shape q r h
  d_comp_d' q r t _ _ := by
    ext c
    exact (F.obj c).d_comp_d q r t

/-- Transposition and evaluation recover the actual original diagram. -/
def complexDiagramTransposeIso (F : C ⥤ HomologicalComplex D shape) :
    (complexDiagramTranspose F).asFunctor ≅ F :=
  NatIso.ofComponents (fun c => Iso.refl (F.obj c)) (by
    intro X Y f
    ext q
    change (F.map f).f q ≫ 𝟙 _ = 𝟙 _ ≫ (F.map f).f q
    simp)

end ToricPower

end
