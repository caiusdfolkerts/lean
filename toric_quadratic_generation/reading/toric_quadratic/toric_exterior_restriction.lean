module

public import PaperVerification.ToricDifferentialRestriction

@[expose] public section

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
