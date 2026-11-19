module

public import ToricPower.LinearVectorCopower
public import ToricPower.CellularFoundations
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The actual linear realization of a cellular diagram

For an actual contravariant label functor `P`, realization is the genuine
coequalizer imposing all incidence relations on vector copowers of the
labels. The full Hom universal property proves that this construction is
left adjoint to the actual Hom-diagram functor. Each actual representable
realizes to its prescribed label.

The construction works in the actual cocomplete module-sheaf category.
It is not asserted to be exact, and its derived realization and the
diagonal-to-identity comparison remain separate mathematical obligations.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  [HasColimitsOfSize.{u,u} A]
  (P : Cᵒᵖ ⥤ A)

/-- Actual incidences, retaining the entire hom-set at each pair. -/
abbrev IncidenceIndex := Σ c : C, Σ d : C, c ⟶ d

/-- The coproduct of all actual vector-labelled cell objects. -/
def realizationZero (F : C ⥤ ModuleCat.{u} k) : A :=
  ∐ (fun c : C => vectorCopower k (P.obj (op c)) (F.obj c))

/-- The coproduct of all actual incidence relation objects. -/
def realizationOne (F : C ⥤ ModuleCat.{u} k) : A :=
  ∐ (fun q : IncidenceIndex (C := C) =>
    vectorCopower k (P.obj (op q.2.1)) (F.obj q.1))

/-- One relation map acts by the actual contravariant label morphism. -/
def realizationLabelRelation (F : C ⥤ ModuleCat.{u} k) :
    realizationOne k P F ⟶ realizationZero k P F :=
  Sigma.desc (fun q : IncidenceIndex (C := C) =>
    vectorCopowerMapObject k (P.map q.2.2.op) (F.obj q.1) ≫
      Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (F.obj c)) q.1)

/-- The other relation map acts by the actual diagram incidence map. -/
def realizationVectorRelation (F : C ⥤ ModuleCat.{u} k) :
    realizationOne k P F ⟶ realizationZero k P F :=
  Sigma.desc (fun q : IncidenceIndex (C := C) =>
    (vectorCopowerFunctor k (P.obj (op q.2.1))).map (F.map q.2.2) ≫
      Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (F.obj c)) q.2.1)

/-- The actual linear coend, built as an actual coequalizer. -/
def realizationObj (F : C ⥤ ModuleCat.{u} k) : A :=
  coequalizer (realizationLabelRelation k P F) (realizationVectorRelation k P F)

/-- The actual vector-indexed generator in the coequalizer. -/
def realizationInclusion (F : C ⥤ ModuleCat.{u} k) (c : C) :
    F.obj c →ₗ[k] (P.obj (op c) ⟶ realizationObj k P F) :=
  (Linear.rightComp k (P.obj (op c))
    (Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (F.obj c)) c ≫
      coequalizer.π (realizationLabelRelation k P F) (realizationVectorRelation k P F))).comp
    (vectorCopowerInclusion k (P.obj (op c)) (F.obj c))

@[simp]
theorem realizationInclusion_apply (F : C ⥤ ModuleCat.{u} k) (c : C) (x : F.obj c) :
    realizationInclusion k P F c x =
      vectorCopowerInclusion k (P.obj (op c)) (F.obj c) x ≫
        Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (F.obj c)) c ≫
        coequalizer.π (realizationLabelRelation k P F) (realizationVectorRelation k P F) := rfl

/-- The defining incidence relation is proved from the actual
coequalizer equation and the two actual vector-copower universal maps. -/
@[reassoc]
theorem realizationInclusion_relation (F : C ⥤ ModuleCat.{u} k)
    {c d : C} (f : c ⟶ d) (x : F.obj c) :
    P.map f.op ≫ realizationInclusion k P F c x =
      realizationInclusion k P F d (F.map f x) := by
  have h := congrArg (fun a => vectorCopowerInclusion k (P.obj (op d)) (F.obj c) x ≫
      Sigma.ι (fun q : IncidenceIndex (C := C) =>
        vectorCopower k (P.obj (op q.2.1)) (F.obj q.1)) ⟨c,d,f⟩ ≫ a)
    (coequalizer.condition (realizationLabelRelation k P F) (realizationVectorRelation k P F))
  rw [realizationInclusion_apply, realizationInclusion_apply]
  simp only [realizationLabelRelation, realizationVectorRelation,
    Category.assoc, Sigma.ι_comp_desc_assoc,
    vectorCopowerInclusion_mapObject_assoc, vectorCopowerInclusion_map_assoc] at h
  exact h

/-- A morphism from realization determines an actual natural linear
Hom diagram by evaluation on each vector generator. -/
def realizationToHom {F : C ⥤ ModuleCat.{u} k} {E : A}
    (h : realizationObj k P F ⟶ E) : F ⟶ (homDiagram k P).obj E where
  app c := ModuleCat.ofHom
    ((Linear.rightComp k (P.obj (op c)) h).comp (realizationInclusion k P F c))
  naturality {c d} f := by
    ext x
    change realizationInclusion k P F d (F.map f x) ≫ h =
      P.map f.op ≫ realizationInclusion k P F c x ≫ h
    rw [← realizationInclusion_relation, Category.assoc]

@[simp]
theorem realizationToHom_app_apply {F : C ⥤ ModuleCat.{u} k} {E : A}
    (h : realizationObj k P F ⟶ E) (c : C) (x : F.obj c) :
    (realizationToHom k P h).app c x = realizationInclusion k P F c x ≫ h := rfl

/-- The cellwise map supplied by an actual natural Hom diagram. -/
def realizationDescZero {F : C ⥤ ModuleCat.{u} k} {E : A}
    (α : F ⟶ (homDiagram k P).obj E) : realizationZero k P F ⟶ E :=
  Sigma.desc (fun c => (vectorCopowerHomEquiv k (P.obj (op c)) (F.obj c) E).symm (α.app c))

/-- Naturality is exactly the coequalizer's relation. -/
theorem realizationDescZero_condition {F : C ⥤ ModuleCat.{u} k} {E : A}
    (α : F ⟶ (homDiagram k P).obj E) :
    realizationLabelRelation k P F ≫ realizationDescZero k P α =
      realizationVectorRelation k P F ≫ realizationDescZero k P α := by
  apply Sigma.hom_ext
  rintro ⟨c,d,f⟩
  apply vectorCopower_hom_ext k (P.obj (op d)) (F.obj c)
  intro x
  simp only [realizationLabelRelation, realizationVectorRelation,
    realizationDescZero, Category.assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
    vectorCopowerInclusion_mapObject_assoc, vectorCopowerInclusion_map_assoc,
    vectorCopowerInclusion_desc]
  exact (ConcreteCategory.congr_hom (α.naturality f) x).symm

/-- The actual coequalizer descent map. -/
def realizationDesc {F : C ⥤ ModuleCat.{u} k} {E : A}
    (α : F ⟶ (homDiagram k P).obj E) : realizationObj k P F ⟶ E :=
  coequalizer.desc (realizationDescZero k P α) (realizationDescZero_condition k P α)

@[reassoc]
theorem realizationInclusion_desc {F : C ⥤ ModuleCat.{u} k} {E : A}
    (α : F ⟶ (homDiagram k P).obj E) (c : C) (x : F.obj c) :
    realizationInclusion k P F c x ≫ realizationDesc k P α = α.app c x := by
  simp only [realizationInclusion_apply, realizationDesc, realizationDescZero, Category.assoc,
    coequalizer.π_desc, Sigma.ι_comp_desc, vectorCopowerInclusion_desc]
  rfl

/-- Actual realization maps are determined by their values on the
literal vector generators in every cell. -/
theorem realization_hom_ext {F : C ⥤ ModuleCat.{u} k} {E : A}
    {f g : realizationObj k P F ⟶ E}
    (h : ∀ c (x : F.obj c), realizationInclusion k P F c x ≫ f =
      realizationInclusion k P F c x ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro c
  apply vectorCopower_hom_ext k (P.obj (op c)) (F.obj c)
  intro x
  have hh := h c x
  simp only [realizationInclusion_apply, Category.assoc] at hh
  exact hh

/-- The complete actual Hom universal property of realization. -/
def realizationHomEquiv (F : C ⥤ ModuleCat.{u} k) (E : A) :
    (realizationObj k P F ⟶ E) ≃ (F ⟶ (homDiagram k P).obj E) where
  toFun := realizationToHom k P
  invFun := realizationDesc k P
  left_inv f := by
    apply realization_hom_ext k P
    intro c x
    rw [realizationInclusion_desc, realizationToHom_app_apply]
  right_inv α := by
    ext c x
    exact realizationInclusion_desc k P α c x

/-- Naturality in the target is literal composition of actual sheaf
morphisms, so it supplies the functorial left adjoint. -/
theorem realizationHomEquiv_natural (F : C ⥤ ModuleCat.{u} k)
    (E E' : A) (g : E ⟶ E') (h : realizationObj k P F ⟶ E) :
    realizationHomEquiv k P F E' (h ≫ g) =
      realizationHomEquiv k P F E h ≫ (homDiagram k P).map g := by
  ext c x
  exact (Category.assoc _ _ _).symm

/-- The genuine ordinary realization functor. No exactness or derived
comparison is built into its definition. -/
def realization : (C ⥤ ModuleCat.{u} k) ⥤ A :=
  Adjunction.leftAdjointOfEquiv (G := homDiagram k P) (realizationHomEquiv k P)
    (realizationHomEquiv_natural k P)

/-- The actual coend--Hom adjunction. -/
def realizationHomAdjunction : realization k P ⊣ homDiagram k P :=
  Adjunction.adjunctionOfEquivLeft (G := homDiagram k P) (realizationHomEquiv k P)
    (realizationHomEquiv_natural k P)

instance realization_isLeftAdjoint : (realization k P).IsLeftAdjoint :=
  (realizationHomAdjunction k P).isLeftAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

instance realization_additive : (realization k P).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- A representable realizes to the specified label, by its actual
universal property. The construction includes every distinct incidence
in the free module, rather than choosing a quotient face relation. -/
def realizationRepresentableIso (c : C) :
    (realization k P).obj (representable k c) ≅ P.obj (op c) where
  hom := realizationDesc k P (fromValue k ((homDiagram k P).obj (P.obj (op c))) c (𝟙 _))
  inv := realizationInclusion k P (representable k c) c (ModuleCat.freeMk (𝟙 c))
  hom_inv_id := by
    apply realization_hom_ext k P
    intro d x
    have hlinear :
        (Linear.rightComp k (P.obj (op d))
          (realizationDesc k P (fromValue k ((homDiagram k P).obj (P.obj (op c))) c (𝟙 _)) ≫
            realizationInclusion k P (representable k c) c (ModuleCat.freeMk (𝟙 c)))).comp
          (realizationInclusion k P (representable k c) d) =
        realizationInclusion k P (representable k c) d := by
      apply Finsupp.lhom_ext'
      intro f
      apply LinearMap.ext_ring
      change realizationInclusion k P (representable k c) d (ModuleCat.freeMk f) ≫
          (realizationDesc k P
            (fromValue k ((homDiagram k P).obj (P.obj (op c))) c (𝟙 _)) ≫
            realizationInclusion k P (representable k c) c (ModuleCat.freeMk (𝟙 c))) =
        realizationInclusion k P (representable k c) d (ModuleCat.freeMk f)
      rw [realizationInclusion_desc_assoc, fromValue_app_freeMk,
        homDiagram_obj_map_apply, Category.comp_id]
      simpa only [representable_map_freeMk, Category.id_comp] using
        realizationInclusion_relation k P (representable k c) f (ModuleCat.freeMk (𝟙 c))
    have hx := LinearMap.congr_fun hlinear x
    simp only [LinearMap.comp_apply, Linear.rightComp_apply] at hx
    exact hx.trans (Category.comp_id _).symm
  inv_hom_id := by
    rw [realizationInclusion_desc]
    exact evaluate_fromValue k ((homDiagram k P).obj (P.obj (op c))) c (𝟙 _)

end ToricPower.Cellular

end
