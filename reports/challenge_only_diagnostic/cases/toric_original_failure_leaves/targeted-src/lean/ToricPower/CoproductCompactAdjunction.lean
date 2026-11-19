module

public import ToricPower.CoproductProjectorMap
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Left adjoints preserve compact objects when their right adjoints preserve coproducts

The proof uses the actual adjunction bijection and the canonical
finite-subcoproduct projectors. It therefore controls the original
morphism, rather than just comparing dimensions of Hom spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]

theorem coproductCompact_leftAdjoint
    {F : C ⥤ D} {G : D ⥤ C} [G.Additive] (adjunction : F ⊣ G)
    (preserves : ∀ (I : Type w) (family : I → D),
      PreservesColimit (Discrete.functor family) G)
    {X : C} (compact : CoproductCompact.{u,v,w} X) :
    CoproductCompact.{u',v',w} (F.obj X) := by
  apply coproductCompact_iff_projector.mpr
  intro I family f
  letI := preserves I family
  let g := adjunction.homEquiv X (∐ family) f
  obtain ⟨s, support⟩ := (coproductCompact_iff_projector.mp compact) I
    (fun i => G.obj (family i))
    (g ≫ (PreservesCoproduct.iso G family).hom)
  refine ⟨s, ?_⟩
  apply (adjunction.homEquiv X (∐ family)).injective
  rw [adjunction.homEquiv_naturality_right]
  change g ≫ G.map (finiteCoproductProjector family s) = g
  apply (cancel_mono (PreservesCoproduct.iso G family).hom).mp
  rw [Category.assoc, map_finiteCoproductProjector, ← Category.assoc]
  exact support

end ToricPower.CompactExtraction

end
