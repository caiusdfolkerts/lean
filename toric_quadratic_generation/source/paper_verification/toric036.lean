module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import paper_verification.toric034

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricModuleRestrictionSheafification
section Source_ToricModuleRestrictionSheafification

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicDifferentialSheaf
-- original header: public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

-- original header: @[expose] public section

/-!
# Actual module sheafification on an open subscheme

Restriction to an open subscheme is the literal restriction on the open
image, with scalars transported by the structure-sheaf isomorphism. It
preserves local bijections because the open-image functor is
cocontinuous. Consequently it commutes with actual module
sheafification, including its universal map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (j : X⟶Y) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true in
def openPresheafRestrict :
    PresheafOfModulesOfCommRing.{u} Y.presheaf⥤
      PresheafOfModulesOfCommRing.{u} X.presheaf :=
  let α : X.presheaf⟶j.opensFunctor.op⋙Y.presheaf :=
    { app U := (j.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

@[simp] theorem openPresheafRestrict_sheaf_val (M : Y.Modules) :
    (openPresheafRestrict j).obj M.val=(M.restrict j).val := rfl

@[simp] theorem openPresheafRestrict_map_apply
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    (U : X.Opens) (s : P.obj (op (j ''ᵁ U))) :
    ((openPresheafRestrict j).map f).app (op U) s=f.app (op (j ''ᵁ U)) s := rfl

theorem openPresheafRestrict_locallyInjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

theorem openPresheafRestrict_locallySurjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

variable (P : PresheafOfModulesOfCommRing.{u} Y.presheaf)

def openRestrictionSheafificationUnit : (openPresheafRestrict j).obj P⟶
    (Scheme.Modules.restrict
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j).val :=
  (openPresheafRestrict j).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallyInjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallySurjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (openRestrictionSheafificationUnit j P)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (openRestrictionSheafificationUnit j P))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (openRestrictionSheafificationUnit j P) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison, derived from actual sheafification of a
locally bijective restriction map. -/
def openRestrictionSheafificationIso :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((openPresheafRestrict j).obj P) ≅
        Scheme.Modules.restrict
          ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j :=
  asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (openRestrictionSheafificationUnit j P)) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app
          (Scheme.Modules.restrict
            ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j)

set_option backward.isDefEq.respectTransparency.types false in
theorem openRestrictionSheafificationIso_unit :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app ((openPresheafRestrict j).obj P) ≫
      (openRestrictionSheafificationIso j P).hom.val=
        openRestrictionSheafificationUnit j P := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q : X.Modules := Scheme.Modules.restrict
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j
  have h : (adj.homEquiv ((openPresheafRestrict j).obj P) Q).symm
      (openRestrictionSheafificationUnit j P) =
        (openRestrictionSheafificationIso j P).hom := rfl
  have he := congrArg (adj.homEquiv ((openPresheafRestrict j).obj P) Q) h.symm
  exact he.trans
    ((adj.homEquiv ((openPresheafRestrict j).obj P) Q).apply_symm_apply
      (openRestrictionSheafificationUnit j P))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openRestrictionSheafificationIso
end
end Source_ToricModuleRestrictionSheafification
-- END ORIGINAL PaperVerification.ToricModuleRestrictionSheafification


-- BEGIN ORIGINAL PaperVerification.ToricDifferentialRestriction
section Source_ToricDifferentialRestriction

-- original header: module

-- original header: public import PaperVerification.ToricModuleRestrictionSheafification

-- original header: @[expose] public section

/-!
# Kähler differentials under an actual open immersion

The comparison is induced by the actual structure-ring maps. Its
compatibility with universal derivations is retained explicitly. No
affineness, smoothness, integrality, or fan presentation is needed.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BaseSections

section Rings

variable {A B C : CommRingCat.{u}} (f : A⟶B) (g : A⟶C)
    (e : B≅C) (he : f≫e.hom=g)

include he in
theorem differentialRingIso_forward_square : 𝟙 A≫g=f≫e.hom := by
  simpa using he.symm

include he in
theorem differentialRingIso_backward_square : 𝟙 A≫f=g≫e.inv := by
  rw [←he]
  simp

def differentialRingForward :
    CommRingCat.KaehlerDifferential f⟶
      (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential g) :=
  CommRingCat.KaehlerDifferential.map (differentialRingIso_forward_square f g e he)

def differentialRingBackward :
    CommRingCat.KaehlerDifferential g⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f) :=
  CommRingCat.KaehlerDifferential.map (differentialRingIso_backward_square f g e he)

private theorem differentialRingForward_d (b : B) :
    differentialRingForward f g e he (CommRingCat.KaehlerDifferential.d b)=
      CommRingCat.KaehlerDifferential.d (e.hom b) :=
  CommRingCat.KaehlerDifferential.map_d _ _

private theorem differentialRingBackward_d (c : C) :
    differentialRingBackward f g e he (CommRingCat.KaehlerDifferential.d c)=
      CommRingCat.KaehlerDifferential.d (e.inv c) :=
  CommRingCat.KaehlerDifferential.map_d _ _

set_option backward.isDefEq.respectTransparency false in
private theorem differentialRingBackward_forward
    (x : CommRingCat.KaehlerDifferential f) :
    differentialRingBackward f g e he (differentialRingForward f g e he x)=x := by
  letI := f.hom.toAlgebra
  have hx : x∈Submodule.span B (Set.range (CommRingCat.KaehlerDifferential.d (f:=f))) := by
    change x∈Submodule.span B (Set.range (_root_.KaehlerDifferential.D A B))
    rw [_root_.KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b,rfl⟩ := hx
      rw [differentialRingForward_d,differentialRingBackward_d]
      simp
  | zero => simp [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | smul a x hx ih =>
      rw [map_smul]
      change differentialRingBackward f g e he
        (e.hom a • differentialRingForward f g e he x)=a • x
      rw [map_smul]
      change e.inv (e.hom a) • differentialRingBackward f g e he
        (differentialRingForward f g e he x)=a • x
      simp only [Iso.hom_inv_id_apply,ih]

set_option backward.isDefEq.respectTransparency false in
/-- Kähler differentials transported through the actual isomorphism of
structure rings. The source has precisely the transported scalar action. -/
def differentialRingIso :
    (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f) ≅
      CommRingCat.KaehlerDifferential g where
  hom := ModuleCat.ofHom
    (R := C)
    (X := (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f))
    (Y := CommRingCat.KaehlerDifferential g)
    { toFun := differentialRingForward f g e he
      map_add' := map_add _
      map_smul' c x := by
        change differentialRingForward f g e he (e.inv c • x)=
          c • differentialRingForward f g e he x
        rw [map_smul]
        change e.hom (e.inv c) • differentialRingForward f g e he x=_
        simp only [Iso.inv_hom_id_apply] }
  inv := differentialRingBackward f g e he
  hom_inv_id := by
    ext x
    exact differentialRingBackward_forward f g e he x
  inv_hom_id := by
    apply CommRingCat.KaehlerDifferential.ext
    intro c
    change differentialRingForward f g e he
      (differentialRingBackward f g e he (CommRingCat.KaehlerDifferential.d c)) =
        CommRingCat.KaehlerDifferential.d c
    rw [differentialRingBackward_d,differentialRingForward_d,Iso.inv_hom_id_apply]

@[simp] theorem differentialRingIso_hom_d (b : B) :
    (differentialRingIso f g e he).hom (CommRingCat.KaehlerDifferential.d b)=
      CommRingCat.KaehlerDifferential.d (e.hom b) :=
  differentialRingForward_d f g e he b

@[simp] theorem differentialRingIso_inv_d (c : C) :
    (differentialRingIso f g e he).inv (CommRingCat.KaehlerDifferential.d c)=
      CommRingCat.KaehlerDifferential.d (e.inv c) :=
  differentialRingBackward_d f g e he c

end Rings

section Schemes

variable (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (j : X⟶Y) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

set_option backward.isDefEq.respectTransparency.types false in
theorem BaseSections.scalarMap_appLE (V : Y.Opens) (U : X.Opens)
    (h : U≤j ⁻¹ᵁ V) (c : k) :
    j.appLE V U h (scalarMap k Y V c)=scalarMap k X U c := by
  have hm : Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫ j.appLE V U h =
      j.appLE ⊤ U (by simp) :=
    j.map_appLE h (homOfLE (show V ≤ ⊤ from le_top)).op
  calc
    j.appLE V U h (scalarMap k Y V c) =
        j.appLE V U h
          (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
            (scalarMap k Y ⊤ c)) :=
      congrArg (fun s : Γ(Y,V) => j.appLE V U h s)
        (scalarMap_restrict k (X := Y) (U := ⊤) (V := V) le_top c).symm
    _ = j.appLE ⊤ U (by simp) (scalarMap k Y ⊤ c) :=
      congrArg (fun q : Γ(Y,⊤) ⟶ Γ(X,U) => q.hom (scalarMap k Y ⊤ c)) hm
    _ = scalarMap k X U c := by
      change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (j.appTop (scalarMap k Y ⊤ c)) = _
      rw [scalarMap_top_natural]
      exact scalarMap_restrict k (X := X) (U := ⊤) (V := U) le_top c

theorem scalarPresheafMap_appIso (U : X.Opens) :
    (scalarPresheafMap k Y).app (op (j ''ᵁ U))≫(j.appIso U).hom=
      (scalarPresheafMap k X).app (op U) := by
  ext c
  rw [Scheme.Hom.appIso_hom']
  exact BaseSections.scalarMap_appLE k j (j ''ᵁ U) U (j.preimage_image_eq U).ge c

theorem differentialPresheaf_map_d {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    (r : X.presheaf.obj U) :
    (differentialPresheaf k X).map h
      (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r) =
        CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k X).app V) (X.presheaf.map h r) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    (scalarPresheafMap k X) h r

set_option backward.isDefEq.respectTransparency.types false in
def differentialPresheafRestrictionComponent (U : X.Opensᵒᵖ) :
    (differentialPresheaf k X).obj U ≅
      ((openPresheafRestrict j).obj (differentialPresheaf k Y)).obj U :=
  (differentialRingIso
    ((scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
    ((scalarPresheafMap k X).app U) (j.appIso U.unop)
    (scalarPresheafMap_appIso k j U.unop)).symm

theorem differentialPresheafRestrictionComponent_d (U : X.Opensᵒᵖ)
    (r : X.presheaf.obj U) :
    (differentialPresheafRestrictionComponent k j U).hom
      (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r) =
        CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
          ((j.appIso U.unop).inv r) :=
  differentialRingIso_inv_d
    ((scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
    ((scalarPresheafMap k X).app U) (j.appIso U.unop)
    (scalarPresheafMap_appIso k j U.unop) r

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialPresheafRestrictionComponent_naturality
    {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    (differentialPresheaf k X).map h ≫
        (ModuleCat.restrictScalars (X.presheaf.map h).hom).map
          (differentialPresheafRestrictionComponent k j V).hom =
      (differentialPresheafRestrictionComponent k j U).hom ≫
        ((openPresheafRestrict j).obj (differentialPresheaf k Y)).map h := by
  apply CommRingCat.KaehlerDifferential.ext (f := (scalarPresheafMap k X).app U)
  intro r
  change (differentialPresheafRestrictionComponent k j V).hom
      ((differentialPresheaf k X).map h
        (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r)) =
    (differentialPresheaf k Y).map (j.opensFunctor.op.map h)
      ((differentialPresheafRestrictionComponent k j U).hom
        (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r))
  exact
    (congrArg (differentialPresheafRestrictionComponent k j V).hom
      (differentialPresheaf_map_d k h r)).trans
    ((differentialPresheafRestrictionComponent_d k j V (X.presheaf.map h r)).trans
    ((congrArg (CommRingCat.KaehlerDifferential.d
      (f := (scalarPresheafMap k Y).app (op (j ''ᵁ V.unop))))
      (congrArg (fun q : Γ(X,U.unop) ⟶ Γ(Y,j ''ᵁ V.unop) => q.hom r)
        (j.appIso_inv_naturality h))).trans
    ((differentialPresheaf_map_d k (j.opensFunctor.op.map h)
      ((j.appIso U.unop).inv r)).symm.trans
    (congrArg ((differentialPresheaf k Y).map (j.opensFunctor.op.map h))
      (differentialPresheafRestrictionComponent_d k j U r).symm))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse comparison differentiates the inverse of the actual
structure-ring isomorphism, with its naturality proved separately. -/
def differentialPresheafRestrictionIso :
    differentialPresheaf k X≅
      (openPresheafRestrict j).obj (differentialPresheaf k Y) :=
  PresheafOfModulesOfCommRing.isoMk (R := X.presheaf)
    (M₁ := differentialPresheaf k X)
    (M₂ := (openPresheafRestrict j).obj (differentialPresheaf k Y))
    (differentialPresheafRestrictionComponent k j)
    (fun {_ _} h => differentialPresheafRestrictionComponent_naturality k j h)

@[simp] theorem differentialPresheafRestrictionIso_inv_d (U : X.Opens)
    (r : Γ(Y,j ''ᵁ U)) :
    (differentialPresheafRestrictionIso k j).inv.app (op U)
      ((differentialPresheafDerivation k Y).d r)=
        (differentialPresheafDerivation k X).d ((j.appIso U).hom r) :=
  differentialRingIso_hom_d _ _ _ _ r

/-- Intrinsic Kähler sheaves commute with restriction along every actual
open immersion over the base ring. -/
def differentialSheafRestrictIso :
    (differentialSheaf k Y).restrict j≅differentialSheaf k X :=
  (openRestrictionSheafificationIso j (differentialPresheaf k Y)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (differentialPresheafRestrictionIso k j).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSheafRestrictIso_unit :
    openRestrictionSheafificationUnit j (differentialPresheaf k Y) ≫
      (differentialSheafRestrictIso k j).hom.val =
        (differentialPresheafRestrictionIso k j).inv ≫ differentialSheafUnit k X := by
  let E := openRestrictionSheafificationIso j (differentialPresheaf k Y)
  let e := differentialPresheafRestrictionIso k j
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hE : E.hom.val ≫ E.inv.val = 𝟙 _ :=
    congrArg
      (fun f : F.obj ((openPresheafRestrict j).obj (differentialPresheaf k Y)) ⟶
        F.obj ((openPresheafRestrict j).obj (differentialPresheaf k Y)) => f.val)
      E.hom_inv_id
  change openRestrictionSheafificationUnit j (differentialPresheaf k Y) ≫
    (E.inv.val ≫ (F.map e.inv).val) = e.inv ≫ differentialSheafUnit k X
  rw [← openRestrictionSheafificationIso_unit]
  change (_ ≫ E.hom.val) ≫ (E.inv.val ≫ (F.map e.inv).val) = _
  rw [Category.assoc, ← Category.assoc E.hom.val E.inv.val, hE, Category.id_comp]
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality e.inv).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSheafRestrictIso_D (U : X.Opens) (r : Γ(Y,j ''ᵁ U)) :
    (differentialSheafRestrictIso k j).hom.app U
      (((differentialSheaf k Y).restrictAppIso j U).inv
        ((differentialSheafDerivation k Y).d (X:=op (j ''ᵁ U)) r)) =
      (differentialSheafDerivation k X).d (X:=op U) ((j.appIso U).hom r) := by
  have h := congrArg
    (fun f=>f.app (op U) ((differentialPresheafDerivation k Y).d r))
    (differentialSheafRestrictIso_unit k j)
  change (differentialSheafRestrictIso k j).hom.val.app (op U)
      ((openRestrictionSheafificationUnit j (differentialPresheaf k Y)).app (op U)
        ((differentialPresheafDerivation k Y).d r)) =
    (differentialSheafUnit k X).app (op U)
      ((differentialPresheafRestrictionIso k j).inv.app (op U)
        ((differentialPresheafDerivation k Y).d r)) at h
  rw [differentialPresheafRestrictionIso_inv_d] at h
  exact h

/-- The ordinary pullback comparison, obtained from the proved
restriction/pullback adjoint identification. -/
def differentialSheafPullbackIso :
    (Scheme.Modules.pullback j).obj (differentialSheaf k Y)≅differentialSheaf k X :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app (differentialSheaf k Y)).symm ≪≫
    differentialSheafRestrictIso k j

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.differentialSheafRestrictIso
#print axioms PaperVerification.ToricSchemes.differentialSheafPullbackIso
end
end Source_ToricDifferentialRestriction
-- END ORIGINAL PaperVerification.ToricDifferentialRestriction


-- BEGIN ORIGINAL PaperVerification.ToricExteriorRestriction
section Source_ToricExteriorRestriction

-- original header: module

-- original header: public import PaperVerification.ToricDifferentialRestriction

-- original header: @[expose] public section

/-!
# Ordinary exterior sheaves under open restriction

The exterior comparison is induced by the universal alternating map,
including degree zero. Together with actual module sheafification it
gives restriction and pullback compatibility for intrinsic top
differential sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite

section Rings

variable {R S : CommRingCat.{u}} (e : R≅S) (M : ModuleCat.{u} R) (n : ℕ)

abbrev ringExteriorRestrictedModule := (ModuleCat.restrictScalars e.inv.hom).obj M

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPullAlternating :
    ringExteriorRestrictedModule e M [⋀^Fin n]→ₗ[S]
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) where
  toFun x := exteriorPower.ιMulti R n (M := M) x
  map_update_add' x i a b := (exteriorPower.ιMulti R n (M := M)).map_update_add x i a b
  map_update_smul' x i c a := (exteriorPower.ιMulti R n (M := M)).map_update_smul x i (e.inv c) a
  map_eq_zero_of_eq' x i j h hij :=
    (exteriorPower.ιMulti R n (M := M)).map_eq_zero_of_eq x h hij

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPushAlternating :
    M [⋀^Fin n]→ₗ[R]
      (ModuleCat.restrictScalars e.hom.hom).obj
        ((ringExteriorRestrictedModule e M).exteriorPower n) where
  toFun x := exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x
  map_update_add' x i a b := (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_update_add x i a b
  map_update_smul' x i r a := by
    have h := (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_update_smul x i (e.hom r) a
    change exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) (Function.update x i (e.inv (e.hom r) • a))=
      e.hom r • exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) (Function.update x i a) at h
    change exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)
      (Function.update x i (r • a)) =
        e.hom r • exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)
          (Function.update x i a)
    simpa only [Iso.hom_inv_id_apply] using h
  map_eq_zero_of_eq' x i j h hij :=
    (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_eq_zero_of_eq x h hij

def ringExteriorPull :
    (ringExteriorRestrictedModule e M).exteriorPower n⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc (ringExteriorPullAlternating e M n)

def ringExteriorPushRaw : M.exteriorPower n⟶
    (ModuleCat.restrictScalars e.hom.hom).obj
      ((ringExteriorRestrictedModule e M).exteriorPower n) :=
  ModuleCat.exteriorPower.desc (ringExteriorPushAlternating e M n)

@[simp] private theorem ringExteriorPull_wedge
    (x : Fin n → ringExteriorRestrictedModule e M) :
    ringExteriorPull e M n (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)=
      exteriorPower.ιMulti R n (M := M) x :=
  ModuleCat.exteriorPower.desc_mk _ _

@[simp] private theorem ringExteriorPushRaw_wedge (x : Fin n→M) :
    ringExteriorPushRaw e M n (exteriorPower.ιMulti R n (M := M) x)=
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x :=
  ModuleCat.exteriorPower.desc_mk _ _

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPush :
    (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n)⟶
      (ringExteriorRestrictedModule e M).exteriorPower n :=
  ModuleCat.ofHom
    (R := S)
    (X := (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n))
    (Y := (ringExteriorRestrictedModule e M).exteriorPower n)
    { toFun := ringExteriorPushRaw e M n
      map_add' := map_add _
      map_smul' c x := by
        change ringExteriorPushRaw e M n (e.inv c • x)=
          c • ringExteriorPushRaw e M n x
        rw [map_smul]
        change e.hom (e.inv c) • ringExteriorPushRaw e M n x=_
        simp }

set_option backward.isDefEq.respectTransparency false in
private theorem ringExteriorPull_push (x : M.exteriorPower n) :
    ringExteriorPull e M n (ringExteriorPushRaw e M n x)=x := by
  have hx : x∈Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v,rfl⟩ := hx
      exact (congrArg (ringExteriorPull e M n)
        (ringExteriorPushRaw_wedge e M n v)).trans (ringExteriorPull_wedge e M n v)
  | zero => simp only [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | smul a x hx ih =>
      rw [map_smul]
      change ringExteriorPull e M n (e.hom a • ringExteriorPushRaw e M n x)=a • x
      rw [map_smul]
      change e.inv (e.hom a) • ringExteriorPull e M n
        (ringExteriorPushRaw e M n x)=a • x
      simp only [Iso.hom_inv_id_apply,ih]

/-- Exterior powers commute with an actual change of scalars through a
ring isomorphism, by their ordinary alternating universal property. -/
def ringExteriorIso :
    ((ModuleCat.restrictScalars e.inv.hom).obj M).exteriorPower n≅
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) where
  hom := ringExteriorPull e M n
  inv := ringExteriorPush e M n
  hom_inv_id := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    change ringExteriorPushRaw e M n
      (ringExteriorPull e M n
        (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)) =
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x
    exact (congrArg (ringExteriorPushRaw e M n)
      (ringExteriorPull_wedge e M n x)).trans (ringExteriorPushRaw_wedge e M n x)
  inv_hom_id := by
    ext x
    change ringExteriorPull e M n (ringExteriorPushRaw e M n x) = x
    exact ringExteriorPull_push e M n x

@[simp] theorem ringExteriorIso_hom_wedge
    (x : Fin n→(ModuleCat.restrictScalars e.inv.hom).obj M) :
    (ringExteriorIso e M n).hom (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)=
      exteriorPower.ιMulti R n (M := M) x := ringExteriorPull_wedge e M n x

@[simp] theorem ringExteriorIso_inv_wedge (x : Fin n→M) :
    (ringExteriorIso e M n).inv (exteriorPower.ιMulti R n (M := M) x)=
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x := ringExteriorPushRaw_wedge e M n x

end Rings

section Schemes

variable {X Y : Scheme.{u}} (j : X⟶Y) [IsOpenImmersion j]
    (P : PresheafOfModulesOfCommRing.{u} Y.presheaf) (n : ℕ)

def openPresheafExteriorComponent (U : X.Opensᵒᵖ) :
    ((ModuleCat.restrictScalars (j.appIso U.unop).inv.hom).obj
      (P.obj (op (j ''ᵁ U.unop)))).exteriorPower n ≅
    (ModuleCat.restrictScalars (j.appIso U.unop).inv.hom).obj
      ((P.obj (op (j ''ᵁ U.unop))).exteriorPower n) :=
  ringExteriorIso (R := Y.presheaf.obj (op (j ''ᵁ U.unop)))
    (S := X.presheaf.obj U) (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n

set_option maxHeartbeats 2000000 in
theorem openPresheafExteriorComponent_naturality
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n).map f ≫
        (ModuleCat.restrictScalars (X.presheaf.map f).hom).map
          (openPresheafExteriorComponent j P n V).hom =
      (openPresheafExteriorComponent j P n U).hom ≫
        ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n)).map f := by
  apply ModuleCat.exteriorPower.hom_ext (R := X.presheaf.obj U)
    (M := ((openPresheafRestrict j).obj P).obj U)
    (N := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
      (((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n)).obj V))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change (ringExteriorIso (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n).hom
      ((presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n).map f
        (exteriorPower.ιMulti (X.presheaf.obj U) n x)) =
    (presheafExteriorPower Y.presheaf P n).map (j.opensFunctor.op.map f)
      ((ringExteriorIso (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n).hom
        (exteriorPower.ιMulti (X.presheaf.obj U) n x))
  exact
    (congrArg (ringExteriorIso (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n).hom
      (presheafExteriorPower_map_wedge X.presheaf ((openPresheafRestrict j).obj P) n f x)).trans
    ((ringExteriorIso_hom_wedge (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n
      (fun i => ((openPresheafRestrict j).obj P).map f (x i))).trans
    ((presheafExteriorPower_map_wedge Y.presheaf P n (j.opensFunctor.op.map f) x).symm.trans
    (congrArg ((presheafExteriorPower Y.presheaf P n).map (j.opensFunctor.op.map f))
      (ringExteriorIso_hom_wedge (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n x).symm)))

set_option maxHeartbeats 2000000 in
def openPresheafExteriorIso :
    presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n≅
      (openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n) :=
  PresheafOfModulesOfCommRing.isoMk (R := X.presheaf)
    (M₁ := presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n)
    (M₂ := (openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n))
    (fun U => openPresheafExteriorComponent j P n U)
    (fun {_ _} f => openPresheafExteriorComponent_naturality j P n f)


variable (M : Y.Modules)

def sheafExteriorRestrictIso :
    (sheafExteriorPower Y M n).restrict j≅sheafExteriorPower X (M.restrict j) n :=
  (openRestrictionSheafificationIso j (presheafExteriorPower Y.presheaf M.val n)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (openPresheafExteriorIso j M.val n).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem sheafExteriorRestrictIso_unit :
    openRestrictionSheafificationUnit j (presheafExteriorPower Y.presheaf M.val n) ≫
      (sheafExteriorRestrictIso j n M).hom.val=
        (openPresheafExteriorIso j M.val n).inv ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (presheafExteriorPower X.presheaf (M.restrict j).val n) := by
  let E := openRestrictionSheafificationIso j (presheafExteriorPower Y.presheaf M.val n)
  let e := openPresheafExteriorIso j M.val n
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hE : E.hom.val ≫ E.inv.val = 𝟙 _ :=
    congrArg
      (fun f : F.obj ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf M.val n)) ⟶
        F.obj ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf M.val n)) => f.val)
      E.hom_inv_id
  change openRestrictionSheafificationUnit j (presheafExteriorPower Y.presheaf M.val n) ≫
    (E.inv.val ≫ (F.map e.inv).val) = e.inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf (M.restrict j).val n)
  rw [← openRestrictionSheafificationIso_unit]
  change (_ ≫ E.hom.val) ≫ (E.inv.val ≫ (F.map e.inv).val) = _
  rw [Category.assoc, ← Category.assoc E.hom.val E.inv.val, hE, Category.id_comp]
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality e.inv).symm

variable (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [j.IsOver (Spec (CommRingCat.of k))]

/-- Actual restriction of the ordinary top exterior power of the
intrinsic cotangent sheaf. -/
def topDifferentialSheafRestrictIso :
    (topDifferentialSheaf k Y n).restrict j≅topDifferentialSheaf k X n :=
  sheafExteriorRestrictIso j n (differentialSheaf k Y) ≪≫
    sheafExteriorPowerIso X (differentialSheafRestrictIso k j) n

/-- In particular this is the canonical transport of top differential
sheaves through every scheme isomorphism over the base. -/
def topDifferentialSheafPullbackIso :
    (Scheme.Modules.pullback j).obj (topDifferentialSheaf k Y n)≅
      topDifferentialSheaf k X n :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app
    (topDifferentialSheaf k Y n)).symm ≪≫ topDifferentialSheafRestrictIso j n k

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.topDifferentialSheafPullbackIso
end
end Source_ToricExteriorRestriction
-- END ORIGINAL PaperVerification.ToricExteriorRestriction


