module

public import ToricPower.ArrangementFiniteResolution
public import ToricPower.CellularDerivedRealization

/-!
# The unbounded derived coend for the actual arrangement incidence category

The incidence category retains every lattice translation of every face.
Its strict dimension bound supplies the actual finite K-projective
replacement.  Thus the ordinary all-incidence coend has the displayed
absolute left-derived functor on the full unbounded derived category.

This module computes its value on every actual free representable.  It
does not assert a diagonal identity or full faithfulness, which require
separate geometric comparisons.

Candidate source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace ToricPower.IntegralArrangement

universe u

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type u} [Category.{0} B] [Abelian B] [Linear k B]
  [HasColimitsOfSize.{0,0} B]
  [HasDerivedCategory (IncidenceObject A ⥤ ModuleCat k)] [HasDerivedCategory B]
  (P : (IncidenceObject A)ᵒᵖ ⥤ B)

/-- The actual unbounded derived realization of the all-incidence coend. -/
def arrangementDerivedRealization :
    DerivedCategory (IncidenceObject A ⥤ ModuleCat k) ⥤ DerivedCategory B :=
  Cellular.finiteConeRealizationStageDerived k (Cellular.realization k P) (n+1)

/-- Its actual comparison with degreewise ordinary realization. -/
def arrangementDerivedRealizationComparison :
    DerivedCategory.Q ⋙ arrangementDerivedRealization A k P ⟶
      (Cellular.realization k P).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Cellular.finiteConeRealizationComparison k (Cellular.realization k P) (n+1)

/-- The full unbounded left-derived universal property, with every
resolution hypothesis discharged for the actual incidence category. -/
theorem arrangementDerivedRealization_isLeftDerivedFunctor :
    (arrangementDerivedRealization A k P).IsLeftDerivedFunctor
      (arrangementDerivedRealizationComparison A k P)
      (HomologicalComplex.quasiIso (IncidenceObject A ⥤ ModuleCat k) (.up ℤ)) :=
  Cellular.finiteConeRealization_isLeftDerivedFunctor k (Cellular.realization k P) (n+1)
    (arrangementFiniteConeResolution_quasiIso A k)

/-- Universality persists after every functor out of the actual target
derived category.  This is the genuine absolute-derived property. -/
theorem arrangementDerivedRealization_isAbsoluteLeftDerivedFunctor
    {E : Type*} [Category* E] (T : DerivedCategory B ⥤ E) :
    (arrangementDerivedRealization A k P ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q (arrangementDerivedRealization A k P) T).inv ≫
        whiskerRight (arrangementDerivedRealizationComparison A k P) T)
      (HomologicalComplex.quasiIso (IncidenceObject A ⥤ ModuleCat k) (.up ℤ)) :=
  Cellular.finiteConeRealization_isAbsoluteLeftDerivedFunctor k
    (Cellular.realization k P) (n+1) (arrangementFiniteConeResolution_quasiIso A k) T

/-- Each actual free representable, in every single degree, realizes
to the specified actual label in that degree. -/
def arrangementDerivedRealizationRepresentableIso (c : IncidenceObject A) (i : ℤ) :
    (arrangementDerivedRealization A k P).obj
        ((DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat k) i).obj
          (Cellular.representable k c)) ≅
      (DerivedCategory.singleFunctor B i).obj (P.obj (op c)) :=
  Cellular.finiteConeRealizationProjectiveIso k (Cellular.realization k P) (n+1)
    (arrangementFiniteConeResolution_quasiIso A k) (Cellular.representable k c) i ≪≫
      (DerivedCategory.singleFunctor B i).mapIso (Cellular.realizationRepresentableIso k P c)

end ToricPower.IntegralArrangement

end
