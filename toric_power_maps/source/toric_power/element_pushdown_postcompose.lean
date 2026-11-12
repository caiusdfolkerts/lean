module

public import ToricPower.ElementDiagramPushdown
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Postcomposition and the actual direct image of element diagrams

The comparison is the canonical map from the coproduct of the images to
the image of the coproduct.  Both incidence naturality and naturality in
the postcomposing functor are proved from its individual inclusions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v w z

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]
  {D' : Type w} [Category.{z} D'] [HasCoproducts.{0} D']

/-- The canonical comparison, including every fiber summand. -/
def postcomposeComparison (T : D ⥤ D') (E : B.Elements ⥤ D) :
    obj B (E ⋙ T) ⟶ obj B E ⋙ T where
  app c := Sigma.desc (fun r : B.obj c => T.map (inclusion B E c r))
  naturality {c d} f := by
    apply Sigma.hom_ext
    intro r
    change inclusion B (E ⋙ T) c r ≫
        (map B (E ⋙ T) f ≫ Sigma.desc (fun t => T.map (inclusion B E d t))) =
      inclusion B (E ⋙ T) c r ≫
        (Sigma.desc (fun t => T.map (inclusion B E c t)) ≫ T.map (map B E f))
    rw [inclusion_map_assoc]
    simp only [inclusion, Sigma.ι_desc, Sigma.ι_desc_assoc, Functor.comp_map]
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg T.map (inclusion_map B E f r).symm

@[reassoc]
theorem inclusion_postcomposeComparison (T : D ⥤ D')
    (E : B.Elements ⥤ D) (c : C) (r : B.obj c) :
    inclusion B (E ⋙ T) c r ≫ (postcomposeComparison B T E).app c =
      T.map (inclusion B E c r) :=
  Sigma.ι_desc _ _

instance postcomposeComparison_app_isIso (T : D ⥤ D') (E : B.Elements ⥤ D)
    (c : C)
    [PreservesColimit (Discrete.functor (fun r : B.obj c =>
      E.obj (B.elementsMk c r))) T] :
    IsIso ((postcomposeComparison B T E).app c) := by
  have comparison : (postcomposeComparison B T E).app c =
      sigmaComparison T (fun r : B.obj c => E.obj (B.elementsMk c r)) := by
    apply Sigma.hom_ext
    intro r
    change inclusion B (E ⋙ T) c r ≫ (postcomposeComparison B T E).app c = _
    rw [inclusion_postcomposeComparison]
    simpa only [inclusion, Functor.comp_obj] using
      (ι_comp_sigmaComparison T
        (fun r : B.obj c => E.obj (B.elementsMk c r)) r).symm
  rw [comparison]
  infer_instance

/-- Postcomposition commutes with direct image whenever it preserves the
actual fiber coproducts.  In particular this applies to additive functors
and finite fibers. -/
def postcomposeIso (T : D ⥤ D') (E : B.Elements ⥤ D)
    [∀ c : C, PreservesColimit (Discrete.functor (fun r : B.obj c =>
      E.obj (B.elementsMk c r))) T] :
    obj B E ⋙ T ≅ obj B (E ⋙ T) :=
  (NatIso.ofComponents (fun c => asIso ((postcomposeComparison B T E).app c))
    (fun f => (postcomposeComparison B T E).naturality f)).symm

/-- The same comparison is natural in the entire postcomposing functor,
so it can be applied to coefficient complexes and their differentials. -/
def postcomposeFunctorComparison (E : B.Elements ⥤ D) :
    (whiskeringLeft B.Elements D D').obj E ⋙ functor B ⟶
      (whiskeringLeft C D D').obj (obj B E) where
  app T := postcomposeComparison B T E
  naturality {T S} α := by
    apply NatTrans.ext
    funext c
    apply Sigma.hom_ext
    intro r
    change inclusion B (E ⋙ T) c r ≫
        (cellMap B (whiskerLeft E α) c ≫ (postcomposeComparison B S E).app c) =
      inclusion B (E ⋙ T) c r ≫
        ((postcomposeComparison B T E).app c ≫ α.app (cell B E c))
    rw [inclusion_cellMap_assoc, inclusion_postcomposeComparison,
      inclusion_postcomposeComparison_assoc]
    exact (α.naturality (inclusion B E c r)).symm

end ToricPower.ElementPushdown

end
