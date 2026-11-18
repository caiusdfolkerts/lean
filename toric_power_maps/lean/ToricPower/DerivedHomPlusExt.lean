module

public import ToricPower.CellularDerivedHom
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Actual bounded-below Hom diagrams, injective resolutions, and Ext

Mathlib's proved injective derivability structure supplies an actual
bounded-below complex of injective objects and an actual quasi-isomorphism
from each single object.  The actual right-derived comparison identifies
the Hom diagram with its value on that complex. Exact evaluation gives
the literal Hom complex at each label, and its cohomology is identified
with the modern derived-category Ext group.

Every resolution and comparison is constructed here. No equality between
module-sheaf Ext and underlying abelian-sheaf cohomology is assumed; that
geometric comparison belongs to `ModuleExtCohomology`.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open CochainComplex.HomComplex

namespace ToricPower

universe u v w w'

section Replacement

variable {A : Type v} [Category.{u} A] [Abelian A] [EnoughInjectives A]

/-- The actual object in degree zero, regarded as a bounded-below complex. -/
def singlePlusComplex (M : A) : CochainComplex.Plus A :=
  ⟨(CochainComplex.singleFunctor A 0).obj M, ⟨0, inferInstance⟩⟩

instance singlePlusComplex_isStrictlyGE (M : A) :
    (singlePlusComplex M).obj.IsStrictlyGE 0 := by
  change ((CochainComplex.singleFunctor A 0).obj M).IsStrictlyGE 0
  infer_instance

/-- An actual injective resolution concentrated in nonnegative degrees,
selected from Mathlib's proved injective replacement construction. -/
def singleInjectiveResolutionData (M : A) :
    { r : (CochainComplex.Plus.localizerMorphism A).RightResolution (singlePlusComplex M) //
      r.X₁.obj.IsStrictlyGE 0 } :=
  Classical.choice (by
    obtain ⟨L, hL, i, hi⟩ :=
      CochainComplex.Plus.exists_quasiIso_injective (singlePlusComplex M) 0
    exact ⟨⟨{ X₁ := L, w := i, hw := hi }, hL⟩⟩)

/-- The underlying actual right resolution. -/
def singleInjectiveResolution (M : A) :
    (CochainComplex.Plus.localizerMorphism A).RightResolution (singlePlusComplex M) :=
  (singleInjectiveResolutionData M).val

instance singleInjectiveResolution_isStrictlyGE (M : A) :
    (singleInjectiveResolution M).X₁.obj.IsStrictlyGE 0 :=
  (singleInjectiveResolutionData M).property

/-- The actual integer-indexed injective cochain complex underlying that
resolution. It is bounded below and K-injective by proved instances. -/
def singleInjectiveCochain (M : A) : CochainComplex A ℤ :=
  ((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj
    (singleInjectiveResolution M).X₁.obj

instance singleInjectiveCochain_isStrictlyGE (M : A) :
    (singleInjectiveCochain M).IsStrictlyGE 0 := by
  unfold singleInjectiveCochain
  infer_instance

instance singleInjectiveCochain_injective (M : A) (n : ℤ) :
    Injective ((singleInjectiveCochain M).X n) := by
  change Injective (((singleInjectiveResolution M).X₁.obj.X n).obj)
  exact ((singleInjectiveResolution M).X₁.obj.X n).property

instance singleInjectiveCochain_isKInjective (M : A) :
    (singleInjectiveCochain M).IsKInjective := by
  unfold singleInjectiveCochain
  infer_instance

/-- The literal single-to-resolution chain map. -/
def singleInjectiveCochainι (M : A) :
    (CochainComplex.singleFunctor A 0).obj M ⟶ singleInjectiveCochain M :=
  (singleInjectiveResolution M).w.hom

instance singleInjectiveCochainι_quasiIso (M : A) :
    QuasiIso (singleInjectiveCochainι M) :=
  (singleInjectiveResolution M).hw

variable [HasDerivedCategory A]

/-- The actual localization of the injective-resolution augmentation. -/
def singleInjectiveDerivedIso (M : A) :
    (DerivedCategory.singleFunctor A 0).obj M ≅ DerivedCategory.Q.obj (singleInjectiveCochain M) :=
  asIso (DerivedCategory.Q.map (singleInjectiveCochainι M))

variable {B : Type w} [Category.{u} B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]

/-- The actual right-derived comparison on a single object, computed on
the actual chosen injective resolution. -/
def rightDerivedPlusSingleModelIso (M : A) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (singlePlusComplex M)) ≅
      DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj
          ((InjectiveObject.ι A).mapCochainComplexPlus.obj
            (singleInjectiveResolution M).X₁)) := by
  let r := singleInjectiveResolution M
  letI : IsIso (DerivedCategory.Plus.Q.map r.w) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A) r.w r.hw
  exact F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map r.w)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj r.X₁))).symm

/-- Actual derived homology agrees with homology of the actual
degreewise image of the actual injective resolution. -/
def rightDerivedPlusSingleHomologyIso (M : A) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (singlePlusComplex M))) ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj (singleInjectiveCochain M)).homology n :=
  (DerivedCategory.Plus.homologyFunctor B n).mapIso (rightDerivedPlusSingleModelIso F M) ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _

/-- The actual single-object right-derived calculation has no negative
cohomology, since its chosen injective complex is literally zero there. -/
theorem rightDerivedPlusSingle_negativeHomology_isZero (M : A) (n : ℤ) (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (singlePlusComplex M)))) := by
  let J : CochainComplex B ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj (singleInjectiveCochain M)
  have hzero : IsZero (J.X n) := J.isZero_of_isStrictlyGE 0 n hn
  exact (HomologicalComplex.ExactAt.of_isZero hzero).isZero_homology.of_iso
    (rightDerivedPlusSingleHomologyIso F M n)

end Replacement

section HomExt

variable (R : Type u) [CommRing R]
  {A : Type v} [Category.{u} A] [Abelian A] [Linear R A]

/-- The signed linear Hom complex from a single object is isomorphic
to literal termwise linear Hom. The actual differential is preserved. -/
def linearHomFromSingleIso (P : A) (I : CochainComplex A ℤ) :
    linearHomComplex R ((CochainComplex.singleFunctor A 0).obj P) I ≅
      (((linearCoyoneda R A).obj (op P)).mapHomologicalComplex (.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleLinearEquiv (R := R) (X := P) (K := I)
      (show (0 : ℤ)+n=n by simp)).toModuleIso) (by
    intro n m hnm
    ext z
    obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (by simp)
    change Cochain.fromSingleLinearEquiv (R := R) (zero_add n)
        (Cochain.fromSingleMk f (zero_add n)) ≫ I.d n m =
      Cochain.fromSingleLinearEquiv (R := R) (zero_add m)
        (δ n m (Cochain.fromSingleMk f (zero_add n)))
    rw [Cochain.δ_fromSingleMk f (zero_add n) m m (zero_add m)]
    change Cochain.fromSingleEquiv (zero_add n)
        (Cochain.fromSingleMk f (zero_add n)) ≫ I.d n m =
      Cochain.fromSingleEquiv (zero_add m)
        (Cochain.fromSingleMk (f ≫ I.d n m) (zero_add m))
    simp only [Cochain.fromSingleEquiv_fromSingleMk])

variable [EnoughInjectives A] [HasDerivedCategory A] [HasExt.{u} A]

/-- The cohomology classes of Hom into the actual injective resolution
are the actual Ext groups. This is an additive equivalence, so it also
identifies zero and nonzero classes. -/
def injectiveHomClassExtEquiv (P M : A) (n : ℕ) :
    CohomologyClass ((CochainComplex.singleFunctor A 0).obj P)
        (singleInjectiveCochain M) (n : ℤ) ≃+ CategoryTheory.Abelian.Ext.{u} P M n :=
  (CohomologyClass.homAddEquiv
    (K := (CochainComplex.singleFunctor A 0).obj P)
    (L := singleInjectiveCochain M) (n := (n : ℤ))).trans
    ((AddEquiv.ofBijective (Functor.mapAddHom DerivedCategory.Qh)
      (CochainComplex.IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient A (.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj P))
        ((singleInjectiveCochain M)⟦(n : ℤ)⟧))).trans
    ((Linear.homCongr ℤ
      ((DerivedCategory.quotientCompQhIso A).app
        ((CochainComplex.singleFunctor A 0).obj P))
      ((DerivedCategory.quotientCompQhIso A).app
        ((singleInjectiveCochain M)⟦(n : ℤ)⟧))).toAddEquiv.trans
    ((Linear.homCongr ℤ (Iso.refl _)
      ((DerivedCategory.Q.commShiftIso (n : ℤ)).app (singleInjectiveCochain M) ≪≫
        (CategoryTheory.shiftFunctor (DerivedCategory A) (n : ℤ)).mapIso
          (singleInjectiveDerivedIso M).symm)).toAddEquiv.trans
    CategoryTheory.Abelian.Ext.homAddEquiv.symm)))

/-- Literal termwise Hom cohomology of the actual resolution computes
the actual modern derived-category Ext group. -/
def injectiveTermwiseHomExtEquiv (P M : A) (n : ℕ) :
    ((((linearCoyoneda R A).obj (op P)).mapHomologicalComplex (.up ℤ)).obj
      (singleInjectiveCochain M)).homology (n : ℤ) ≃+ CategoryTheory.Abelian.Ext.{u} P M n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (linearHomFromSingleIso R P (singleInjectiveCochain M)).symm).toLinearEquiv.toAddEquiv |>.trans
      ((HomComplex.homologyLinearEquiv R _ _ (n : ℤ)).toAddEquiv.trans
        (injectiveHomClassExtEquiv P M n))

end HomExt

namespace Cellular

variable (R : Type u) [CommRing R]
  {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Abelian A] [Linear R A]
  [EnoughInjectives A] [HasDerivedCategory A]
  [HasDerivedCategory (C ⥤ ModuleCat.{u} R)] [HasExt.{u} A]
  (P : Cᵒᵖ ⥤ A)

/-- Evaluate the actual derived Hom diagram after taking actual
homology. Exact evaluation identifies it with literal termwise Hom
cohomology on the actual injective resolution. -/
def labelRHomPlusSingleEvaluationIso (M : A) (c : C) (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor (C ⥤ ModuleCat.{u} R) n).obj
      ((labelRHomPlus R P).obj (DerivedCategory.Plus.Q.obj (singlePlusComplex M)))).obj c ≅
      ((((linearCoyoneda R A).obj (op (P.obj (op c)))).mapHomologicalComplex (.up ℤ)).obj
        (singleInjectiveCochain M)).homology n := by
  let I := singleInjectiveCochain M
  let K := ((homDiagram R P).mapHomologicalComplex (.up ℤ)).obj I
  let ev := (evaluation C (ModuleCat.{u} R)).obj c
  exact ev.mapIso (rightDerivedPlusSingleHomologyIso (homDiagram R P) M n) ≪≫
    ((K.sc n).mapHomologyIso ev).symm

/-- The requested literal coefficient dictionary for `B⁺`: in every
nonnegative degree and at every actual incidence object, its homology
is the actual Ext group from the actual label. No geometric cohomology
comparison is assumed in this theorem. -/
def labelRHomPlusSingleEvaluationExt (M : A) (c : C) (n : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (C ⥤ ModuleCat.{u} R) (n : ℤ)).obj
      ((labelRHomPlus R P).obj (DerivedCategory.Plus.Q.obj (singlePlusComplex M)))).obj c ≃+
        CategoryTheory.Abelian.Ext.{u} (P.obj (op c)) M n :=
  (labelRHomPlusSingleEvaluationIso R P M c (n : ℤ)).toLinearEquiv.toAddEquiv.trans
    (injectiveTermwiseHomExtEquiv R (P.obj (op c)) M n)

end Cellular

end ToricPower

end
