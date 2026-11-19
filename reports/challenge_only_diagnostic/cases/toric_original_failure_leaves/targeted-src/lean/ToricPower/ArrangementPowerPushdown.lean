module

public import ToricPower.ArrangementPowerIncidence
public import ToricPower.ElementDiagramPushdown
public import ToricPower.ExactDerivedConservative

/-!
# The exact direct image along all inverse power branches

Restriction along the genuine inverse-branch functor is followed by the
coproduct over every sheet.  For module coefficients this is exact and
therefore defines a functor on the full unbounded derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

/-- The actual sheetwise direct image, including the incidence carries. -/
def powerDiagramPushdown (D : Type u) [Category.{v} D] [HasCoproducts.{0} D] :
    (IncidenceObject A ⥤ D) ⥤ (IncidenceObject A ⥤ D) :=
  (Functor.whiskeringLeft (PowerIncidenceObject A ell positive) (IncidenceObject A) D).obj
      (powerBranchFunctor A ell positive) ⋙
    ElementPushdown.functor (powerResidueFunctor A ell positive)

instance powerDiagramPushdown_module_preservesFiniteLimits
    (R : Type) [CommRing R] :
    PreservesFiniteLimits (powerDiagramPushdown A ell positive (ModuleCat.{0} R)) := by
  unfold powerDiagramPushdown
  infer_instance

instance powerDiagramPushdown_module_preservesFiniteColimits
    (R : Type) [CommRing R] :
    PreservesFiniteColimits (powerDiagramPushdown A ell positive (ModuleCat.{0} R)) := by
  unfold powerDiagramPushdown
  infer_instance

instance powerDiagramPushdown_module_additive (R : Type) [CommRing R] :
    (powerDiagramPushdown A ell positive (ModuleCat.{0} R)).Additive :=
  (powerDiagramPushdown A ell positive (ModuleCat.{0} R)).additive_of_preserves_binary_products

variable (R : Type) [CommRing R]
  [HasDerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} R)]

/-- The induced functor on arbitrary unbounded complexes. -/
def powerDerivedPushdown :
    DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} R) ⥤
      DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} R) :=
  (powerDiagramPushdown A ell positive (ModuleCat.{0} R)).mapDerivedCategory

instance : (powerDerivedPushdown A ell positive R).CommShift ℤ := by
  unfold powerDerivedPushdown
  infer_instance

instance : (powerDerivedPushdown A ell positive R).IsTriangulated := by
  unfold powerDerivedPushdown
  infer_instance

end ToricPower.IntegralArrangement

end
