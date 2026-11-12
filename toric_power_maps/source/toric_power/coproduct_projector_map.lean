module

public import ToricPower.FiniteCoproductRetractions
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Finite-support projectors and coproduct-preserving functors

The canonical projector onto a finite subcoproduct is carried to the
corresponding projector under the actual categorical coproduct
comparison. This allows finite supports to be checked by evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]

theorem ι_finiteCoproductProjector_of_not_mem
    {I : Type w} (family : I → C) (s : Finset I) {i : I} (hi : i ∉ s) :
    Sigma.ι family i ≫ finiteCoproductProjector family s = 0 := by
  classical
  simp [finiteCoproductProjector, finiteCoproductRetraction, hi]

theorem map_ι_coproductIso
    (F : C ⥤ D) {I : Type w} (family : I → C)
    [PreservesColimit (Discrete.functor family) F] (i : I) :
    F.map (Sigma.ι family i) ≫ (PreservesCoproduct.iso F family).hom =
      Sigma.ι (fun i => F.obj (family i)) i :=
  (isColimitOfHasCoproductOfPreservesColimit F family).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ⟨i⟩

theorem map_finiteCoproductProjector
    (F : C ⥤ D) [F.Additive] {I : Type w} (family : I → C)
    [PreservesColimit (Discrete.functor family) F] (s : Finset I) :
    F.map (finiteCoproductProjector family s) ≫ (PreservesCoproduct.iso F family).hom =
      (PreservesCoproduct.iso F family).hom ≫
        finiteCoproductProjector (fun i => F.obj (family i)) s := by
  apply (isColimitOfHasCoproductOfPreservesColimit F family).hom_ext
  rintro ⟨i⟩
  change F.map (Sigma.ι family i) ≫ F.map (finiteCoproductProjector family s) ≫ _ =
    F.map (Sigma.ι family i) ≫ (PreservesCoproduct.iso F family).hom ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, ← Category.assoc,
    map_ι_coproductIso]
  by_cases hi : i ∈ s
  · rw [ι_finiteCoproductProjector family s hi,
      ι_finiteCoproductProjector _ s hi, map_ι_coproductIso]
  · rw [ι_finiteCoproductProjector_of_not_mem family s hi,
      ι_finiteCoproductProjector_of_not_mem _ s hi,
      CategoryTheory.Functor.map_zero, zero_comp]

theorem support_of_mapped_support
    (F : C ⥤ D) [F.Additive] {I : Type w} (family : I → C)
    [PreservesColimit (Discrete.functor family) F]
    {X : C} (f : X ⟶ ∐ family) (s : Finset I)
    (support : (F.map f ≫ (PreservesCoproduct.iso F family).hom) ≫
      finiteCoproductProjector (fun i => F.obj (family i)) s =
        F.map f ≫ (PreservesCoproduct.iso F family).hom) :
    F.map (f ≫ finiteCoproductProjector family s) = F.map f := by
  apply (cancel_mono (PreservesCoproduct.iso F family).hom).mp
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    map_finiteCoproductProjector, ← Category.assoc]
  exact support

end ToricPower.CompactExtraction

end
