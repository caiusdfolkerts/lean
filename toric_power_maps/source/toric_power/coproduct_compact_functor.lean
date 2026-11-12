module

public import ToricPower.CoproductProjectorMap

/-!
# Compactness transported through actual coproduct comparisons

The functor need only be full on maps from the chosen compact source.
It may preserve coproducts just on a collection of representatives of
the target category. This is the situation of derived localization on
K-projective representatives.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]

theorem coproductCompact_of_iso {X Y : C} (e : X ≅ Y)
    (compact : CoproductCompact.{u,v,w} X) : CoproductCompact.{u,v,w} Y := by
  intro I family f
  obtain ⟨s, lift, factor⟩ := compact I family (e.hom ≫ f)
  refine ⟨s, e.inv ≫ lift, ?_⟩
  rw [Category.assoc, factor, e.inv_hom_id_assoc]

theorem finiteCoproductProjector_mapIso {I : Type w} {family other : I → C}
    (e : ∀ i, family i ≅ other i) (s : Finset I) :
    finiteCoproductProjector family s ≫ (Sigma.mapIso e).hom =
      (Sigma.mapIso e).hom ≫ finiteCoproductProjector other s := by
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc]
  by_cases hi : i ∈ s
  · rw [ι_finiteCoproductProjector family s hi,
      Sigma.ι_mapIso_hom, Category.assoc,
      ι_finiteCoproductProjector other s hi]
  · rw [ι_finiteCoproductProjector_of_not_mem family s hi,
      zero_comp, Sigma.ι_mapIso_hom, Category.assoc,
      ι_finiteCoproductProjector_of_not_mem other s hi,
      comp_zero]

theorem compact_map_support
    (F : C ⥤ D) [F.Additive] {X : C}
    (compact : CoproductCompact.{u,v,w} X)
    (surjective : ∀ Y : C, Function.Surjective (F.map : (X ⟶ Y) → _))
    {I : Type w} (family : I → C)
    [PreservesColimit (Discrete.functor family) F]
    (f : F.obj X ⟶ ∐ fun i => F.obj (family i)) :
    ∃ s : Finset I,
      f ≫ finiteCoproductProjector (fun i => F.obj (family i)) s = f := by
  obtain ⟨g, equation⟩ := surjective (∐ family)
    (f ≫ (PreservesCoproduct.iso F family).inv)
  have mapped : F.map g ≫ (PreservesCoproduct.iso F family).hom = f := by
    rw [equation, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨s, support⟩ := (coproductCompact_iff_projector.mp compact) I family g
  refine ⟨s, ?_⟩
  rw [← mapped, Category.assoc, ← map_finiteCoproductProjector,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, support]

/-- Only coproducts of the specified representatives have to be preserved. -/
theorem coproductCompact_image_of_representatives
    (F : C ⥤ D) [F.Additive] (representative : ObjectProperty C)
    (exists_rep : ∀ Y : D, ∃ Z : C, representative Z ∧ Nonempty (F.obj Z ≅ Y))
    (preserves : ∀ (I : Type w) (family : I → C),
      (∀ i, representative (family i)) → PreservesColimit (Discrete.functor family) F)
    {X : C} (compact : CoproductCompact.{u,v,w} X)
    (surjective : ∀ Y : C, Function.Surjective (F.map : (X ⟶ Y) → _)) :
    CoproductCompact.{u',v',w} (F.obj X) := by
  classical
  apply coproductCompact_iff_projector.mpr
  intro I family f
  choose models members isos using fun i => exists_rep (family i)
  let e (i : I) := Classical.choice (isos i)
  letI := preserves I models members
  obtain ⟨s, support⟩ := compact_map_support F compact surjective models
    (f ≫ (Sigma.mapIso e).inv)
  refine ⟨s, ?_⟩
  have h := congrArg (fun a => a ≫ (Sigma.mapIso e).hom) support
  simpa only [Category.assoc, finiteCoproductProjector_mapIso,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

theorem coproductCompact_image
    (F : C ⥤ D) [F.Additive] [F.EssSurj]
    (preserves : ∀ (I : Type w) (family : I → C),
      PreservesColimit (Discrete.functor family) F)
    {X : C} (compact : CoproductCompact.{u,v,w} X)
    (surjective : ∀ Y : C, Function.Surjective (F.map : (X ⟶ Y) → _)) :
    CoproductCompact.{u',v',w} (F.obj X) :=
  coproductCompact_image_of_representatives F ⊤
    (fun Y => ⟨F.objPreimage Y, trivial, ⟨F.objObjPreimageIso Y⟩⟩)
    (fun I family _ => preserves I family) compact surjective

end ToricPower.CompactExtraction

end
