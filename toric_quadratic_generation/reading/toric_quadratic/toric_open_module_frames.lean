module

public import PaperVerification.ToricInvertiblePullback

@[expose] public section

/-! # Actual open-chart frames on the corresponding open subsite -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.ModuleFrame

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- The inverse open-subsite transport is a genuine inverse on frames. -/
theorem toRestrictIso_ofRestrictIso
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    toRestrictIso (ofRestrictIso d) = d := by
  let E := overEquiv U
  let c := (overFunctorEquiv U).app M
  let v := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  have hpre : E.functor.map (ofRestrictIso d).hom = c.hom ≫ d.hom ≫ v.inv := by
    simpa only [E,c,v,ofRestrictIso,Scheme.Modules.overEquiv,
      TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit,
      Equivalence.fullyFaithfulFunctor,Iso.trans_hom,Iso.symm_hom,
      Iso.app_hom,Iso.app_inv,Functor.mapIso_hom,Functor.map_comp,Category.assoc] using
      E.fullyFaithfulFunctor.map_preimage (c.hom ≫ d.hom ≫ v.inv)
  apply Iso.ext
  change c.inv ≫ E.functor.map (ofRestrictIso d).hom ≫ v.hom = d.hom
  rw [hpre]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

/-- The forward open-site comparison evaluates the actual inverse frame. -/
theorem toRestrictIso_generator_eval (f : ModuleFrame M U) :
    (M.restrictAppIso U.ι ⊤).hom
      ((toRestrictIso f).inv.app ⊤ (1 : Γ(U.toScheme,⊤))) =
      f.generator (U.ι ''ᵁ ⊤) (U.ι_image_le ⊤) := by
  rfl

/-- The frame transported back to the open subsite has the expected section. -/
theorem ofRestrictIso_generator_eval
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((M.restrictAppIso U.ι ⊤).hom (d.inv.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
      (ofRestrictIso d).generator U le_rfl := by
  have hgen := toRestrictIso_generator_eval (ofRestrictIso d)
  rw [toRestrictIso_ofRestrictIso d] at hgen
  rw [hgen]
  rw [← (ofRestrictIso d).generator_res le_rfl (U.ι_image_le ⊤)]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (M.presheaf.map (homOfLE (U.ι_image_le ⊤)).op
      ((ofRestrictIso d).generator U le_rfl)) = _
  rw [← ConcreteCategory.comp_apply,← Functor.map_comp,← op_comp]
  have hc : eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) = 𝟙 U :=
    Subsingleton.elim _ _
  rw [hc,op_id]
  exact congrArg (fun φ=>φ ((ofRestrictIso d).generator U le_rfl))
    (M.presheaf.map_id (op U))


variable {X Y : Scheme.{u}} (j : Y⟶X) [IsOpenImmersion j]
    {M : X.Modules} (e : M.restrict j≅SheafOfModules.unit Y.ringCatSheaf)

/-- Move a chart frame through the actual isomorphism with its open
image, then through the established open-subscheme/open-subsite
equivalence. -/
def ofOpenImmersionIso : ModuleFrame M j.opensRange :=
  ofRestrictIso
    (((restrictFunctorCongr j.isoOpensRange_inv_comp).app M).symm ≪≫
      (restrictFunctorComp j.isoOpensRange.inv j).app M ≪≫
        (restrictFunctor j.isoOpensRange.inv).mapIso e ≪≫
          restrictUnitIso j.isoOpensRange.inv)

/-- The actual global section on the open image corresponding to the
chart's distinguished section. -/
def imageFrameGenerator : Γ(M,j.opensRange) :=
  M.presheaf.map (eqToHom (j.image_top_eq_opensRange).symm).op
    ((M.restrictAppIso j ⊤).hom (e.inv.app ⊤ (1 : Γ(Y,⊤))))

/-- The actual inverse structure-module restriction preserves one. -/
theorem restrictUnitIso_inv_one {Y Z : Scheme.{u}} (f : Y⟶Z)
    [IsOpenImmersion f] (V : Y.Opens) :
    (restrictUnitIso f).inv.app V (1 : Γ(Y,V)) =
      (1 : Γ(Z,f ''ᵁ V)) := by
  change (f.appIso V).inv (1 : Γ(Y,V)) = 1
  exact map_one _

set_option maxHeartbeats 2000000 in
/-- No independent scalar is introduced when the chart frame is moved
to the image open. -/
theorem ofOpenImmersionIso_generator :
    (ofOpenImmersionIso j e).generator j.opensRange le_rfl=imageFrameGenerator j e := by
  have he (V : Y.Opens) : e.inv.app V (1 : Γ(Y,V)) =
      (M.restrict j).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
        (e.inv.app ⊤ (1 : Γ(Y,⊤))) := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op (1 : Γ(Y,⊤))
    change e.inv.app V
      ((Y.presheaf.map (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op).hom 1) =
        (M.restrict j).presheaf.map (homOfLE le_top).op
          (e.inv.app ⊤ (1 : Γ(Y,⊤))) at hn
    simpa only [map_one] using hn
  have hmap : ((restrictFunctor j.isoOpensRange.inv).map e.inv).app ⊤
      (1 : Γ(Y,j.isoOpensRange.inv ''ᵁ ⊤)) =
      e.inv.app (j.isoOpensRange.inv ''ᵁ ⊤)
        (1 : Γ(Y,j.isoOpensRange.inv ''ᵁ ⊤)) := rfl
  unfold ofOpenImmersionIso
  rw [← ofRestrictIso_generator_eval]
  simp only [Iso.trans_inv,Iso.symm_inv,Iso.app_hom,Iso.app_inv,
    Functor.mapIso_inv,Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,
    restrictUnitIso_inv_one,Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  erw [hmap,he (j.isoOpensRange.inv ''ᵁ ⊤)]
  let V : Y.Opens := j.isoOpensRange.inv ''ᵁ ⊤
  let t : Γ(M,j ''ᵁ ⊤) :=
    (M.restrictAppIso j ⊤).hom (e.inv.app ⊤ (1 : Γ(Y,⊤)))
  have hi : (j.isoOpensRange.inv ≫ j) ''ᵁ (⊤ : j.opensRange.toScheme.Opens) =
      j.opensRange.ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    simp only [Scheme.Hom.coe_image]
    rw [j.isoOpensRange_inv_comp]
  change M.presheaf.map (eqToHom j.opensRange.ι_image_top.symm).op
    (M.presheaf.map (eqToHom hi.symm).op
      (M.presheaf.map (eqToHom (Scheme.Hom.comp_image j.isoOpensRange.inv j ⊤)).op
        (M.presheaf.map
          ((j.opensFunctor.map (homOfLE (show V ≤ (⊤ : Y.Opens) from le_top))).op) t))) =
    M.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op t
  have hcomp {U V W : X.Opensᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
      (s : M.presheaf.obj U) :
      M.presheaf.map g (M.presheaf.map f s) = M.presheaf.map (f ≫ g) s :=
    (congrArg (fun φ : M.presheaf.obj U ⟶ M.presheaf.obj W => φ s)
      (M.presheaf.map_comp f g)).symm
  simp only [hcomp]
  erw [hcomp]
  apply congrArg (fun φ : op (j ''ᵁ (⊤ : Y.Opens)) ⟶ op j.opensRange =>
    M.presheaf.map φ t)
  exact Subsingleton.elim _ _

end PaperVerification.ToricSchemes.ModuleFrame
