module

public import PaperVerification.ToricModuleRestrictionSheafification

@[expose] public section

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
