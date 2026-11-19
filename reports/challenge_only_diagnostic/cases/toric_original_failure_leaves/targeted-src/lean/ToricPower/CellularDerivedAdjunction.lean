module

public import ToricPower.AffineRightDerived
public import ToricPower.AffineOpenIntrinsicLabelHomExact
public import ToricPower.CellularDerivedRealization
public import ToricPower.CellularRealization
public import ToricPower.ComplexAdjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# The actual unbounded cellular derived adjunction

The left adjoint is the derived ordinary coend, computed with the finite
projective cone resolution of incidence diagrams. The right adjoint is
the derived actual label-Hom diagram, computed with the finite affine
coresolution. Both universal properties are absolute, so the ordinary
termwise adjunction descends with its unit, counit and triangle identities.

This file establishes an adjunction, not invertibility of its counit.
The latter is the separate geometric reconstruction theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Functor CochainComplex TopologicalSpace Opposite

namespace ToricPower.Cellular

universe u v

local instance cellularAdjunctionDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] {C : Type u} [Category.{u} C]
  [HasDerivedCategory (C ⥤ ModuleCat.{u} k)]
  (P : Cᵒᵖ ⥤ QCoh X)
  {I : Type v} (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  [∀ i, PreservesFiniteLimits
    (quasicoherentOpenLocalization (V i).ι ⋙ homDiagram k P)]
  [∀ i, PreservesFiniteColimits
    (quasicoherentOpenLocalization (V i).ι ⋙ homDiagram k P)]
  (l : List I) (hl : ∀ i, i ∈ l) (hV : IsOpenCover V)

/-- The concrete unbounded right-derived Hom-diagram functor. -/
abbrev labelRHomAffine : DerivedQCoh X ⥤ DerivedCategory (C ⥤ ModuleCat.{u} k) :=
  affineConeDerivedStage V (homDiagram k P) l

/-- The actual derived coend--Hom adjunction on all unbounded
complexes. Its finite-resolution premise is discharged below. -/
def realizationAffineHomAdjunction (m : ℕ)
    (hε : ∀ K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app K)) :
    finiteConeRealizationStageDerived k (realization k P) m ⊣
      labelRHomAffine k P V l := by
  letI := finiteConeRealization_isLeftDerivedFunctor k (realization k P) m hε
  letI := affineConeDerivedStage_isRightDerivedFunctor V (homDiagram k P) l hl hV
  letI := finiteConeRealization_isAbsoluteLeftDerivedFunctor
    k (realization k P) m hε (labelRHomAffine k P V l)
  letI := affineConeDerivedStage_isAbsoluteRightDerivedFunctor
    V (homDiagram k P) l hl hV
    (finiteConeRealizationStageDerived k (realization k P) m)
  exact (complexAdjunction (realizationHomAdjunction k P) (.up ℤ)).derived
    (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ))
    (HomologicalComplex.quasiIso (QCoh X) (.up ℤ))
    (finiteConeRealizationComparison k (realization k P) m)
    (affineRightDerivedUnit V (homDiagram k P) l)

/-- The finite-grade endpoint retains arbitrary coefficient modules
and arbitrary unbounded complexes. -/
def finiteGradeRealizationAffineHomAdjunction
    (grade : C → ℕ)
    (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
    (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
    [∀ c : C, Subsingleton (c ⟶ c)]
    (N : ℕ) (hbound : ∀ c : C, grade c ≤ N) :
    finiteConeRealizationStageDerived k (realization k P) (N+1) ⊣
      labelRHomAffine k P V l :=
  realizationAffineHomAdjunction k P V l hl hV (N+1)
    (finiteConeResolution_augmentation_quasiIso k grade grade_le eq_of_grade_eq N hbound)

end ToricPower.Cellular

end
