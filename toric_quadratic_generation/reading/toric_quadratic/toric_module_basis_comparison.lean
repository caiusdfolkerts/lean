module

public import PaperVerification.ToricModuleFrameGluing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

@[expose] public section

/-!
# Module comparisons constructed on an actual topological basis

Compatible module maps on basis opens extend uniquely to a map from a
module presheaf into a module sheaf. If the maps on the basis are
bijective, the extension becomes an isomorphism after actual
sheafification. No quasi-coherence or stalk comparison is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}} {ι : Type v} (B : ι→X.Opens)
    (hB : Opens.IsBasis (Set.range B))
    (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (Q : X.Modules)
    (β : ∀ i,P.obj (op (B i))→ₗ[Γ(X,B i)] Γ(Q,B i))
    (hβ : ∀ i j (h : B j≤B i) (s : P.obj (op (B i))),
      β j (P.map (homOfLE h).op s)=Q.presheaf.map (homOfLE h).op (β i s))

def basisModuleComparisonOnBasis :
    (inducedFunctor B).op⋙P.presheaf ⟶ (inducedFunctor B).op⋙Q.presheaf where
  app i := AddCommGrpCat.ofHom (β i.unop).toAddMonoidHom
  naturality i j f := by
    ext s
    exact hβ i.unop j.unop f.unop.hom.le s

def basisModuleComparisonAdditive : P.presheaf⟶Q.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
    (basisModuleComparisonOnBasis B P Q β hβ)

@[simp] theorem basisModuleComparisonAdditive_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op (B i)) s=β i s := by
  exact congrArg
    (fun f : P.presheaf.obj (op (B i)) ⟶ Q.presheaf.obj (op (B i)) => f s)
    (TopCat.Sheaf.extend_hom_app P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
      (basisModuleComparisonOnBasis B P Q β hβ) i)

theorem basisModuleComparisonAdditive_smul (U : X.Opens)
    (a : Γ(X,U)) (s : P.obj (op U)) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) (a • s)=
      a • (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) s := by
  let φ := basisModuleComparisonAdditive B hB P Q β hβ
  apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
  intro x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,hVU,hi,?_⟩
  erw [← NatTrans.naturality_apply φ (homOfLE hVU).op,
    Q.map_smul,← NatTrans.naturality_apply φ (homOfLE hVU).op]
  change φ.app (op (B i)) (P.map (homOfLE hVU).op (a • s))=
    X.presheaf.map (homOfLE hVU).op a • φ.app (op (B i)) (P.map (homOfLE hVU).op s)
  dsimp only [φ]
  rw [basisModuleComparisonAdditive_app,basisModuleComparisonAdditive_app]
  exact (congrArg (β i) (P.map_smul (homOfLE hVU).op a s)).trans
    ((β i).map_smul _ _)

/-- The extension is genuinely linear over the section ring on every
open, as follows from the actual sheaf separation axiom. -/
def basisModuleComparison : P⟶Q.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (fun U => ModuleCat.ofHom
      ({ toFun := (basisModuleComparisonAdditive B hB P Q β hβ).app U
         map_add' := map_add _
         map_smul' := basisModuleComparisonAdditive_smul B hB P Q β hβ U.unop } :
        P.obj U →ₗ[Γ(X,U.unop)] Γ(Q,U.unop)))
    (by
      intro U V f
      ext s
      exact NatTrans.naturality_apply
        (basisModuleComparisonAdditive B hB P Q β hβ) f s)

@[simp] theorem basisModuleComparison_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparison B hB P Q β hβ).app (op (B i)) s=β i s :=
  basisModuleComparisonAdditive_app B hB P Q β hβ i s

theorem basisModuleComparison_locallyInjective
    (hinj : ∀ i,Function.Injective (β i)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s t h x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,homOfLE hVU,?_,hi⟩
  apply hinj i
  change β i (P.map (homOfLE hVU).op s) = β i (P.map (homOfLE hVU).op t)
  calc
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op s) :=
      (basisModuleComparison_app B hB P Q β hβ i _).symm
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U s) :=
      PresheafOfModules.naturality_apply _ _ _
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U t) :=
      congrArg (Q.presheaf.map (homOfLE hVU).op) h
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op t) :=
      (PresheafOfModules.naturality_apply
        (basisModuleComparison B hB P Q β hβ) (homOfLE hVU).op t).symm
    _ = β i (P.map (homOfLE hVU).op t) :=
      basisModuleComparison_app B hB P Q β hβ i _

theorem basisModuleComparison_locallySurjective
    (hsurj : ∀ i,Function.Surjective (β i)) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  obtain ⟨t,ht⟩ := hsurj i (Q.presheaf.map (homOfLE hVU).op s)
  exact ⟨B i,homOfLE hVU,⟨t,(basisModuleComparison_app B hB P Q β hβ i t).trans ht⟩,hi⟩

theorem basisModuleComparison_sheafification_isIso
    (hbij : ∀ i,Function.Bijective (β i)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) := by
  letI := basisModuleComparison_locallyInjective B hB P Q β hβ (fun i=>(hbij i).1)
  letI := basisModuleComparison_locallySurjective B hB P Q β hβ (fun i=>(hbij i).2)
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (basisModuleComparison B hB P Q β hβ))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (basisModuleComparison B hB P Q β hβ) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison with the actual sheafification. -/
def basisModuleSheafificationIso (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P≅Q := by
  letI := basisModuleComparison_sheafification_isIso B hB P Q β hβ hbij
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app Q)

theorem basisModuleSheafificationIso_unit (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.val=
        basisModuleComparison B hB P Q β hβ := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv P Q).symm (basisModuleComparison B hB P Q β hβ)=
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg (adj.homEquiv P Q) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

/-- The comparison after the actual sheafification unit agrees with
its specified linear map on every member of the genuine open basis. -/
theorem basisModuleSheafificationIso_app (hbij : ∀ i,Function.Bijective (β i))
    (i : ι) (s : P.obj (op (B i))) :
    (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) = β i s := by
  have h := congrArg (fun φ : P ⟶ Q.val => φ.app (op (B i)) s)
    (basisModuleSheafificationIso_unit B hB P Q β hβ hbij)
  have h' : (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s := by
    change (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s at h
    exact h
  exact h'.trans (basisModuleComparison_app B hB P Q β hβ i s)

end PaperVerification.ToricSchemes
