module

public import ToricPower.MappedCellularRealization
public import ToricPower.CellularRealizationUnit

/-!
# Actual linear coend realization commutes with coefficient functors

A linear colimit-preserving coefficient functor commutes with the
original realization. Both directions are constructed by its genuine
coequalizer universal property. Every original vector generator is
retained, which will identify actual tensoring and evaluation maps.
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

/-- The image of the original coend generators, as an actual linear
natural transformation into the coefficientwise Hom diagram. -/
def mappedRealizationUnit (M : C ⥤ ModuleCat.{u} k) :
    M ⟶ (homDiagram k (P ⋙ F)).obj (F.obj (realizationObj k P M)) where
  app c := ModuleCat.ofHom
    { toFun x := F.map (realizationInclusion k P M c x)
      map_add' x y := by rw [_root_.map_add, F.map_add]
      map_smul' r x := by
        rw [_root_.map_smul, F.map_smul]
        rfl }
  naturality {c d} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change F.map (realizationInclusion k P M d (M.map f x)) =
      F.map (P.map f.op) ≫ F.map (realizationInclusion k P M c x)
    rw [← F.map_comp, realizationInclusion_relation]

/-- The actual forward map from mapped coequalizer descent. -/
def mappedRealizationComparison (M : C ⥤ ModuleCat.{u} k) :
    F.obj (realizationObj k P M) ⟶ realizationObj k (P ⋙ F) M :=
  mappedRealizationDesc k F P ((realizationHomAdjunction k (P ⋙ F)).unit.app M)

@[reassoc]
theorem mappedRealizationComparison_generator (M : C ⥤ ModuleCat.{u} k)
    (c : C) (x : M.obj c) :
    F.map (realizationInclusion k P M c x) ≫ mappedRealizationComparison k F P M =
      realizationInclusion k (P ⋙ F) M c x := by
  rw [mappedRealizationComparison, mappedRealizationInclusion_desc]
  exact realizationUnit_app_apply k (P ⋙ F) M c x

/-- The reverse comparison descends the original mapped generators. -/
def mappedRealizationComparisonInverse (M : C ⥤ ModuleCat.{u} k) :
    realizationObj k (P ⋙ F) M ⟶ F.obj (realizationObj k P M) :=
  realizationDesc k (P ⋙ F) (mappedRealizationUnit k F P M)

@[reassoc]
theorem mappedRealizationComparisonInverse_generator (M : C ⥤ ModuleCat.{u} k)
    (c : C) (x : M.obj c) :
    realizationInclusion k (P ⋙ F) M c x ≫ mappedRealizationComparisonInverse k F P M =
      F.map (realizationInclusion k P M c x) := by
  rw [mappedRealizationComparisonInverse, realizationInclusion_desc]
  rfl

/-- The actual coefficient comparison, with both inverse identities
proved on all unrestricted vector generators. -/
def mappedRealizationObjIso (M : C ⥤ ModuleCat.{u} k) :
    F.obj (realizationObj k P M) ≅ realizationObj k (P ⋙ F) M where
  hom := mappedRealizationComparison k F P M
  inv := mappedRealizationComparisonInverse k F P M
  hom_inv_id := by
    apply mappedRealization_hom_ext k F P
    intro c x
    rw [← Category.assoc, mappedRealizationComparison_generator,
      mappedRealizationComparisonInverse_generator, Category.comp_id]
  inv_hom_id := by
    apply realization_hom_ext k (P ⋙ F)
    intro c x
    rw [← Category.assoc, mappedRealizationComparisonInverse_generator,
      mappedRealizationComparison_generator, Category.comp_id]

/-- Naturality is checked on the original generators, so the full
comparison commutes with every actual input-diagram morphism. -/
def mappedRealizationIso : realization k P ⋙ F ≅ realization k (P ⋙ F) :=
  NatIso.ofComponents (mappedRealizationObjIso k F P) (by
    intro M N f
    apply mappedRealization_hom_ext k F P
    intro c x
    change F.map (realizationInclusion k P M c x) ≫
        F.map ((realization k P).map f) ≫ mappedRealizationComparison k F P N =
      F.map (realizationInclusion k P M c x) ≫ mappedRealizationComparison k F P M ≫
        (realization k (P ⋙ F)).map f
    rw [← F.map_comp_assoc, realizationInclusion_map,
      mappedRealizationComparison_generator,
      ← Category.assoc, mappedRealizationComparison_generator,
      realizationInclusion_map])

end ToricPower.Cellular

end
