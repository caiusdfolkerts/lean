module

public import ToricPower.DiagramProjectiveCechDerived
public import ToricPower.LinearHomComplexExact
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Localization.Linear

/-!
# Scalar linearity of the actual projective diagram model

Every scalar action is the original one on coefficient morphisms. The
signed Hom construction and literal transposition preserve it component
by component. The genuine localization universal property transfers this
linearity to the full unbounded derived functor.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

namespace ToricPower

universe r u v w
variable (R : Type r) [CommRing R]

instance linearHomComplexFunctor_linear
    {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
    (K : CochainComplex A ℤ) : (linearHomComplexFunctor R K).Linear R where
  map_smul f a := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change z.comp (Cochain.ofHom (a • f)) (add_zero n) =
      a • z.comp (Cochain.ofHom f) (add_zero n)
    rw [Cochain.ofHom_smul, Cochain.comp_smul]

instance functorEvaluation_linear
    {L : Type*} [Category* L]
    {A : Type*} [Category* A] [Preadditive A] [Linear R A] (l : L) :
    ((evaluation L A).obj l).Linear R where
  map_smul _ _ := rfl

instance functorWhiskeringLeft_linear
    {L M : Type*} [Category* L] [Category* M]
    {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (F : L ⥤ M) :
    ((Functor.whiskeringLeft L M A).obj F).Linear R where
  map_smul _ _ := rfl

instance complexDiagramPostcompose_linear
    {L : Type*} [Category* L]
    {A : Type*} [Category* A] [Abelian A] [Linear R A]
    {D : Type*} [Category* D] [Abelian D] [Linear R D]
    {ι : Type*} {shape : ComplexShape ι}
    (F : HomologicalComplex A shape ⥤ HomologicalComplex D shape) [F.Linear R] :
    (complexDiagramPostcompose (L := L) F).Linear R where
  map_smul f a := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply NatTrans.ext
    funext l
    change (F.map ((((evaluation L A).obj l).mapHomologicalComplex shape).map (a • f))).f q =
      a • (F.map ((((evaluation L A).obj l).mapHomologicalComplex shape).map f)).f q
    calc
      _ = (F.map (a • ((((evaluation L A).obj l).mapHomologicalComplex shape).map f))).f q :=
        congrArg (fun h => (F.map h).f q)
          ((((evaluation L A).obj l).mapHomologicalComplex shape).map_smul a f)
      _ = (a • F.map ((((evaluation L A).obj l).mapHomologicalComplex shape).map f)).f q :=
        congrArg (fun h => h.f q) (F.map_smul a
          ((((evaluation L A).obj l).mapHomologicalComplex shape).map f))
      _ = _ := rfl

section Derived

variable (k : Type v) [CommRing k]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear k A]
  {C : Type w} [Category.{v} C] [Abelian C] [Linear k C]
  {L : Type v} [Category.{v} L]
  (S : A ⥤ L ⥤ C) [S.Additive] [S.Linear k]
  {Z : C} (P : ProjectiveResolution Z)

instance diagramProjectiveCoefficientComplexFunctor_linear :
    (diagramProjectiveCoefficientComplexFunctor k S P).Linear k := by
  unfold diagramProjectiveCoefficientComplexFunctor
  infer_instance

variable [HasDerivedCategory A] [HasDerivedCategory C]
  [HasDerivedCategory (L ⥤ ModuleCat.{v} k)]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

instance diagramProjectiveCoefficientDerived_linear :
    (diagramProjectiveCoefficientDerived k S P).Linear k := by
  unfold diagramProjectiveCoefficientDerived
  apply (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) k
    (diagramProjectiveCoefficientComplexFunctor k S P ⋙ DerivedCategory.Q) _).mp
  infer_instance

end Derived

end ToricPower

end
