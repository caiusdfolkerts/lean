module

public import PaperVerification.FunctorExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Native Ext and derived Hom

Mathlib's `Abelian.Ext` is defined through the derived category. Its older
nonnegative `Functor.rightDerived` construction uses injective resolutions.
This file compares the two actual constructions. The comparison passes
through the genuine Hom complex and the full faithfulness of localization
on complexes of injectives; it does not identify their definitions by fiat.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace PaperVerification.ExtRightDerived

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Isomorphisms of source and target induce the additive Hom equivalence. -/
def homCongrAdd {D : Type*} [Category* D] [Preadditive D]
    {A B A' B' : D} (e : A ≅ A') (f : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- The Hom complex out of a single object is the ordinary complex obtained
by applying the additive Hom functor degreewise. -/
def homComplexFromSingleIso (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := X) (K := K) (p := 0) (q := n) (n := n) (zero_add n)).toAddCommGrpIso)
    (by
      intro n m hnm
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro z
      obtain ⟨f, rfl⟩ :=
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv
          (X := X) (K := K) (p := 0) (q := n) (n := n) (zero_add n)).symm.surjective z
      change (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n))) ≫ K.d n m =
        CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add m)
          (CochainComplex.HomComplex.δ n m
            (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n)))
      rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
        CochainComplex.HomComplex.Cochain.δ_fromSingleMk,
        CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      simp)

section DerivedCategory

variable [HasDerivedCategory C]

/-- The cohomology of the actual Hom complex computes derived-category
maps into a K-injective complex. -/
def homologyEquivDerivedHom (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex K L).homology n ≃+
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n := by
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eL := (DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app L
  exact (CochainComplex.HomComplex.homologyAddEquiv K L n).trans
    ((CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := K) (L := L) (n := n)).trans
      ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
        (CochainComplex.IsKInjective.Qh_map_bijective
          ((HomotopyCategory.quotient C _).obj K) (L⟦n⟧))).trans
        (homCongrAdd eK eL)))

end DerivedCategory

variable {Y : C} (I : InjectiveResolution Y)

/-- The actual resolution augmentation after extension from naturals to
integers, with its source identified with the original single complex. -/
def resolutionExtensionAugmentation :
    (CochainComplex.singleFunctor C 0).obj Y ⟶
      I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Y 0 0 rfl).inv ≫
    HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat

instance : QuasiIso (resolutionExtensionAugmentation I) := by
  dsimp only [resolutionExtensionAugmentation]
  infer_instance

variable [HasExt.{v} C]

/-- Native `Ext` is the cohomology of the genuine Hom complex of an actual
injective resolution. Both sides retain their ordinary mathematical meaning. -/
def extResolutionEquiv (X : C) (n : ℕ) :
    Abelian.Ext.{v} X Y n ≃+
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology n := by
  letI := HasDerivedCategory.standard C
  let K := I.cocomplex.extend ComplexShape.embeddingUpNat
  let S := (CochainComplex.singleFunctor C 0).obj X
  let e : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y) ≅
      DerivedCategory.Q.obj K :=
    asIso (DerivedCategory.Q.map (resolutionExtensionAugmentation I))
  let eShift := (shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso e
  let eComplex := homComplexFromSingleIso X K ≪≫
    PaperVerification.DerivedConcentration.mapExtendIso
      (preadditiveCoyoneda.obj (op X)) ComplexShape.embeddingUpNat I.cocomplex
  let eHomology :=
    (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).mapIso eComplex ≪≫
      HomologicalComplex.extendHomologyIso
        (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).obj I.cocomplex)
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  exact Abelian.Ext.homAddEquiv.trans
    ((homCongrAdd (Iso.refl (DerivedCategory.Q.obj S)) eShift).trans
      ((homologyEquivDerivedHom S K (n : ℤ)).symm.trans
        eHomology.addCommGroupIsoToAddEquiv))

variable [HasInjectiveResolutions C]

/-- Comparison of Mathlib's derived-category Ext with its nonnegative
right-derived additive Hom functor, in every degree. -/
def extRightDerivedEquiv (X Y : C) (n : ℕ) :
    Abelian.Ext.{v} X Y n ≃+
      ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y :=
  (extResolutionEquiv (injectiveResolution Y) X n).trans
    ((injectiveResolution Y).isoRightDerivedObj
      (preadditiveCoyoneda.obj (op X)) n).symm.addCommGroupIsoToAddEquiv

end PaperVerification.ExtRightDerived
