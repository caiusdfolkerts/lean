module

public import ToricPower.CellularRealization
public import ToricPower.LinearVectorCopowerComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Actual coend descent after a linear colimit-preserving functor

Mapping the original coproducts and coequalizer retains their genuine
universal properties. The resulting descent is characterized by its
value on every original cell/vector generator. This is the coefficient
change needed for linear density, with unrestricted vector copowers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v w

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  {B : Type w} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} A] [HasColimitsOfSize.{u,u} B]
  (F : A ⥤ B) [F.Additive] [F.Linear k] [PreservesColimitsOfSize.{u,u} F]
  (P : Cᵒᵖ ⥤ A)

@[reassoc]
theorem map_coproductInclusion_comparison {I : Type u} (X : I → A) (i : I) :
    F.map (Sigma.ι X i) ≫ (PreservesCoproduct.iso F X).hom =
      Sigma.ι (fun i => F.obj (X i)) i := by
  apply (cancel_mono (PreservesCoproduct.iso F X).inv).mp
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  exact (ι_comp_sigmaComparison F X i).symm

def mappedRealizationDescZero {M : C ⥤ ModuleCat.{u} k} {E : B}
    (α : M ⟶ (homDiagram k (P ⋙ F)).obj E) :
    F.obj (realizationZero k P M) ⟶ E :=
  (PreservesCoproduct.iso F
    (fun c : C => vectorCopower k (P.obj (op c)) (M.obj c))).hom ≫
    Sigma.desc (fun c : C =>
      (vectorCopowerComparisonIso k F (P.obj (op c)) (M.obj c)).hom ≫
        (vectorCopowerHomEquiv k (F.obj (P.obj (op c))) (M.obj c) E).symm (α.app c))

@[reassoc]
theorem mappedRealizationDescZero_generator {M : C ⥤ ModuleCat.{u} k} {E : B}
    (α : M ⟶ (homDiagram k (P ⋙ F)).obj E) (c : C) (x : M.obj c) :
    F.map (vectorCopowerInclusion k (P.obj (op c)) (M.obj c) x) ≫
      F.map (Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (M.obj c)) c) ≫
        mappedRealizationDescZero k F P α = α.app c x := by
  simp only [mappedRealizationDescZero,map_coproductInclusion_comparison_assoc,
    Sigma.ι_comp_desc,vectorCopowerComparisonIso_inclusion_assoc,
    vectorCopowerInclusion_desc]
  rfl

/-- The original incidence relations remain exactly the relation needed
for descent after applying the coefficient functor. -/
theorem mappedRealizationDescZero_condition {M : C ⥤ ModuleCat.{u} k} {E : B}
    (α : M ⟶ (homDiagram k (P ⋙ F)).obj E) :
    F.map (realizationLabelRelation k P M) ≫ mappedRealizationDescZero k F P α =
      F.map (realizationVectorRelation k P M) ≫ mappedRealizationDescZero k F P α := by
  apply (isColimitOfHasCoproductOfPreservesColimit F
    (fun q : IncidenceIndex (C := C) =>
      vectorCopower k (P.obj (op q.2.1)) (M.obj q.1))).hom_ext
  rintro ⟨⟨c,d,f⟩⟩
  apply map_vectorCopower_hom_ext k F (P.obj (op d)) (M.obj c)
  intro x
  dsimp only [Cofan.mk,Discrete.natTrans_app]
  have leftSource :
      vectorCopowerInclusion k (P.obj (op d)) (M.obj c) x ≫
        Sigma.ι (fun q : IncidenceIndex (C := C) =>
          vectorCopower k (P.obj (op q.2.1)) (M.obj q.1)) ⟨c,d,f⟩ ≫
        realizationLabelRelation k P M =
      P.map f.op ≫ vectorCopowerInclusion k (P.obj (op c)) (M.obj c) x ≫
        Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (M.obj c)) c := by
    simp only [realizationLabelRelation,Sigma.ι_comp_desc,Category.assoc,
      vectorCopowerInclusion_mapObject_assoc]
  have rightSource :
      vectorCopowerInclusion k (P.obj (op d)) (M.obj c) x ≫
        Sigma.ι (fun q : IncidenceIndex (C := C) =>
          vectorCopower k (P.obj (op q.2.1)) (M.obj q.1)) ⟨c,d,f⟩ ≫
        realizationVectorRelation k P M =
      vectorCopowerInclusion k (P.obj (op d)) (M.obj d) (M.map f x) ≫
        Sigma.ι (fun c : C => vectorCopower k (P.obj (op c)) (M.obj c)) d := by
    simp only [realizationVectorRelation,Sigma.ι_comp_desc,Category.assoc,
      vectorCopowerInclusion_map_assoc]
  have left := congrArg (fun h => F.map h ≫ mappedRealizationDescZero k F P α) leftSource
  have right := congrArg (fun h => F.map h ≫ mappedRealizationDescZero k F P α) rightSource
  simp only [Functor.map_comp,Category.assoc] at left right
  have natural : F.map (P.map f.op) ≫ α.app c x = α.app d (M.map f x) :=
    (ConcreteCategory.congr_hom (α.naturality f) x).symm
  exact left.trans ((congrArg (fun h => F.map (P.map f.op) ≫ h)
    (mappedRealizationDescZero_generator k F P α c x)).trans
      (natural.trans ((mappedRealizationDescZero_generator k F P α d (M.map f x)).symm.trans
        right.symm)))

/-- The actual mapped coequalizer descent. -/
def mappedRealizationDesc {M : C ⥤ ModuleCat.{u} k} {E : B}
    (α : M ⟶ (homDiagram k (P ⋙ F)).obj E) :
    F.obj (realizationObj k P M) ⟶ E :=
  (PreservesCoequalizer.iso F (realizationLabelRelation k P M)
    (realizationVectorRelation k P M)).inv ≫
    coequalizer.desc (mappedRealizationDescZero k F P α)
      (mappedRealizationDescZero_condition k F P α)

@[reassoc]
theorem mappedRealizationInclusion_desc {M : C ⥤ ModuleCat.{u} k} {E : B}
    (α : M ⟶ (homDiagram k (P ⋙ F)).obj E) (c : C) (x : M.obj c) :
    F.map (realizationInclusion k P M c x) ≫ mappedRealizationDesc k F P α = α.app c x := by
  simp only [realizationInclusion_apply,Functor.map_comp,Category.assoc,
    mappedRealizationDesc,map_π_preserves_coequalizer_inv_desc,
    mappedRealizationDescZero_generator]

/-- The original vector generators remain jointly detecting after the
actual colimit-preserving functor. -/
theorem mappedRealization_hom_ext {M : C ⥤ ModuleCat.{u} k} {E : B}
    {f g : F.obj (realizationObj k P M) ⟶ E}
    (equal : ∀ c (x : M.obj c),
      F.map (realizationInclusion k P M c x) ≫ f =
        F.map (realizationInclusion k P M c x) ≫ g) : f = g := by
  apply (cancel_epi (F.map (coequalizer.π (realizationLabelRelation k P M)
    (realizationVectorRelation k P M)))).mp
  apply (isColimitOfHasCoproductOfPreservesColimit F
    (fun c : C => vectorCopower k (P.obj (op c)) (M.obj c))).hom_ext
  intro c
  apply map_vectorCopower_hom_ext k F (P.obj (op c.as)) (M.obj c.as)
  intro x
  have h := equal c.as x
  simp only [realizationInclusion_apply,Functor.map_comp,Category.assoc] at h
  exact h

end ToricPower.Cellular

end
