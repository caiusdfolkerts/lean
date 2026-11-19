module

public import ToricPower.NegativeFunctorTotalInjective
public import ToricPower.NegativeFunctorTotalSingle
public import ToricPower.LinearDerivedHomComparison
public import ToricPower.LinearHomComplexFunctor

/-! # Genuine derived Hom from a finite dual model -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex

namespace ToricPower

universe u v w z r

variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [EnoughInjectives C] [HasDerivedCategory C]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  [EnoughInjectives B] [HasDerivedCategory B]
  [HasDerivedCategory (ModuleCat.{v} R)]
  (Φ : C ⥤ ChainComplex B ℕ) [Φ.Additive] (width : ℕ)
  (H : B ⥤ ModuleCat.{v} R) [H.Additive]

open NegativeFunctorTotal

def finiteDualChainPlus (M : C)
    (outside : ∀ q, width ≤ q → IsZero ((Φ.obj M).X q)) : CochainComplex.Plus B := by
  letI := total_isStrictlyGE Φ width (singleInput M) 0
  refine ⟨(Φ.obj M).extend ComplexShape.embeddingDownNat,⟨0-width,?_⟩⟩
  exact CochainComplex.isStrictlyGE_of_iso (singleInputIso Φ width M outside) _

def finiteDualRightDerivedModelIso
    (preservesInjectives : ∀ (q : ℕ) (M : C), Injective M → Injective ((Φ.obj M).X q))
    (M : C) (outside : ∀ q, width ≤ q → IsZero ((Φ.obj M).X q))
    (replacementQuasiIso : QuasiIso (NegativeFunctorTotal.map Φ width (singleInjectiveCochainι M))) :
    H.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (finiteDualChainPlus Φ width M outside)) ≅
    DerivedCategory.Plus.Q.obj
      (H.mapCochainComplexPlus.obj (plus Φ width
        ⟨singleInjectiveCochain M,⟨0,inferInstance⟩⟩)) := by
  let e : plus Φ width (singlePlusComplex M) ≅ finiteDualChainPlus Φ width M outside :=
    ObjectProperty.isoMk _ (singleInputIso Φ width M outside)
  exact H.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso e.symm) ≪≫
    rightDerivedSingleTotalIso Φ width H preservesInjectives M replacementQuasiIso

def finiteDualDerivedHomEquiv
    (preservesInjectives : ∀ (q : ℕ) (M : C), Injective M → Injective ((Φ.obj M).X q))
    (K : CochainComplex C ℤ) (M : C)
    (outside : ∀ q, width ≤ q → IsZero ((Φ.obj M).X q))
    (replacementQuasiIso : QuasiIso (NegativeFunctorTotal.map Φ width (singleInjectiveCochainι M)))
    (homModel : (H.mapHomologicalComplex (.up ℤ)).obj
        (total Φ width (singleInjectiveCochain M)) ≅
      linearHomComplex R K (singleInjectiveCochain M))
    (q : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} R) q).obj
      (H.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (finiteDualChainPlus Φ width M outside)))) ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor C 0).obj M)⟦q⟧) := by
  let model := finiteDualRightDerivedModelIso R Φ width H preservesInjectives M outside replacementQuasiIso
  let cohomology := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} R) q).mapIso model ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) q).app
      ((H.mapHomologicalComplex (.up ℤ)).obj (total Φ width (singleInjectiveCochain M))) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) q).mapIso homModel
  let target := (DerivedCategory.Q.commShiftIso q).app (singleInjectiveCochain M) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) q).mapIso (singleInjectiveDerivedIso M).symm
  exact cohomology.toLinearEquiv.trans
    ((HomComplex.homologyLinearEquiv R K (singleInjectiveCochain M) q).trans
      ((homClassDerivedLinearEquivOfKInjective R K (singleInjectiveCochain M) q).trans
        (Linear.homCongr R (Iso.refl (DerivedCategory.Q.obj K)) target)))

end ToricPower

end

