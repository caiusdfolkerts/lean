module

public import ToricPower.CellularCovariantLabels
public import ToricPower.LinearVectorCopowerComparison

/-!
# Actual covariant copower diagrams under a coefficient functor

Both the label action and the vector action are transported through the
canonical copower comparison. This provides the natural diagram map used
when taking genuine affine sections of cellular sheaf realizations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u v w

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} B]

/-- The original copower, functorial in the object being copied. -/
def vectorCopowerObjectFunctor (M : ModuleCat.{u} k) : B ⥤ B where
  obj P := vectorCopower k P M
  map f := vectorCopowerMapObject k f M
  map_id P := by
    apply vectorCopower_hom_ext k P M
    intro x
    simp only [vectorCopowerInclusion_mapObject, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply vectorCopower_hom_ext k _ M
    intro x
    simp only [vectorCopowerInclusion_mapObject, Category.assoc,
      vectorCopowerInclusion_mapObject_assoc]

variable (M : C ⥤ ModuleCat.{u} k)

/-- An actual label transformation acts on each original object copower. -/
def covariantCopowerLabelMap {Q Q' : C ⥤ B} (α : Q ⟶ Q') :
    covariantCopowerDiagram k Q M ⟶ covariantCopowerDiagram k Q' M where
  app c := vectorCopowerMapObject k (α.app c) (M.obj c)
  naturality {c d} f := by
    apply vectorCopower_hom_ext k (Q.obj c) (M.obj c)
    intro x
    rw [← Category.assoc, covariantCopowerDiagram_map_inclusion,
      Category.assoc, vectorCopowerInclusion_mapObject,
      vectorCopowerInclusion_mapObject_assoc,
      covariantCopowerDiagram_map_inclusion,
      ← Category.assoc, ← Category.assoc, α.naturality f]

/-- Covariant copower diagrams are functorial in their actual labels. -/
def covariantCopowerLabelFunctor : (C ⥤ B) ⥤ (C ⥤ B) where
  obj Q := covariantCopowerDiagram k Q M
  map α := covariantCopowerLabelMap k M α
  map_id Q := by
    ext c
    exact (vectorCopowerObjectFunctor k (M.obj c)).map_id (Q.obj c)
  map_comp α β := by
    ext c
    exact (vectorCopowerObjectFunctor k (M.obj c)).map_comp (α.app c) (β.app c)

variable {D : Type w} [Category.{u} D] [Preadditive D] [Linear k D]
  [HasCoproducts.{u} D] (F : B ⥤ D) [F.Additive] [F.Linear k]
  [PreservesColimitsOfSize.{u,u} F] (Q : C ⥤ B)

/-- The whole actual incidence diagram commutes with the coefficient
functor, with every label map and every vector map retained. -/
def covariantCopowerCoefficientIso :
    covariantCopowerDiagram k Q M ⋙ F ≅
      covariantCopowerDiagram k (Q ⋙ F) M :=
  NatIso.ofComponents
    (fun c => vectorCopowerComparisonIso k F (Q.obj c) (M.obj c))
    (by
      intro c d f
      change F.map (vectorCopowerMapObject k (Q.map f) (M.obj c) ≫
          (vectorCopowerFunctor k (Q.obj d)).map (M.map f)) ≫
            (vectorCopowerComparisonIso k F (Q.obj d) (M.obj d)).hom =
        (vectorCopowerComparisonIso k F (Q.obj c) (M.obj c)).hom ≫
          vectorCopowerMapObject k (F.map (Q.map f)) (M.obj c) ≫
            (vectorCopowerFunctor k (F.obj (Q.obj d))).map (M.map f)
      rw [Functor.map_comp, Category.assoc, vectorCopowerComparisonIso_map,
        ← Category.assoc, vectorCopowerComparisonIso_mapObject, Category.assoc])

/-- Naturality also holds in the arbitrary vector diagram, not merely
in the individual incidence arrows. -/
theorem covariantCopowerCoefficientIso_natural
    {M M' : C ⥤ ModuleCat.{u} k} (α : M ⟶ M') :
    Functor.whiskerRight (covariantCopowerMap k Q α) F ≫
        (covariantCopowerCoefficientIso k M' F Q).hom =
      (covariantCopowerCoefficientIso k M F Q).hom ≫
        covariantCopowerMap k (Q ⋙ F) α := by
  ext c
  exact vectorCopowerComparisonIso_map k F (Q.obj c) (α.app c)

/-- The full covariant copower functors commute with the actual linear
coefficient functor. -/
def covariantCopowerFunctorComparisonIso :
    covariantCopowerFunctor k Q ⋙ (Functor.whiskeringRight C B D).obj F ≅
      covariantCopowerFunctor k (Q ⋙ F) :=
  NatIso.ofComponents (fun M => covariantCopowerCoefficientIso k M F Q)
    (fun α => covariantCopowerCoefficientIso_natural k F Q α)

end ToricPower.Cellular

end
