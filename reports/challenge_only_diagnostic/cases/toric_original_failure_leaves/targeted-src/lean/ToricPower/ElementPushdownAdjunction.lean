module

public import ToricPower.ElementPushdownExact
public import ToricPower.ExactDerivedAdjunction

/-!
# The genuine covering direct-image adjunction

The coproduct over every element of a fiber is left adjoint to
restriction along the actual projection of the category of elements.
The unit inserts a single sheet, and the counit sums the sheet maps.
The exact adjunction descends to arbitrary unbounded derived objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]

/-- Restriction retains each actual element and each lifted incidence. -/
def restriction : (C ⥤ D) ⥤ (B.Elements ⥤ D) :=
  (whiskeringLeft B.Elements C D).obj (Elements.π B)

def unit : 𝟭 (B.Elements ⥤ D) ⟶ functor B ⋙ restriction B where
  app E :=
    { app c := inclusion B E c.obj c.val
      naturality {_ _} f := (inclusion_map_lifted B E f).symm }
  naturality {_ _} α := by
    apply NatTrans.ext
    funext c
    exact (inclusion_cellMap B α c.obj c.val).symm

def counit : restriction B ⋙ functor B ⟶ 𝟭 (C ⥤ D) where
  app F :=
    { app c := Sigma.desc (fun _ : B.obj c => 𝟙 (F.obj c))
      naturality {c d} f := by
        apply Sigma.hom_ext
        intro r
        change inclusion B ((restriction B).obj F) c r ≫
            (map B ((restriction B).obj F) f ≫ Sigma.desc (fun _ => 𝟙 (F.obj d))) =
          inclusion B ((restriction B).obj F) c r ≫
            (Sigma.desc (fun _ => 𝟙 (F.obj c)) ≫ F.map f)
        rw [inclusion_map_assoc]
        simp only [inclusion, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, Category.id_comp,
          Category.comp_id]
        change F.map f ≫ 𝟙 (F.obj d) = 𝟙 (F.obj c) ≫ F.map f
        rw [Category.comp_id,Category.id_comp] }
  naturality {F G} α := by
    apply NatTrans.ext
    funext c
    apply Sigma.hom_ext
    intro r
    change inclusion B ((restriction B).obj F) c r ≫
        (cellMap B ((restriction B).map α) c ≫ Sigma.desc (fun _ => 𝟙 (G.obj c))) =
      inclusion B ((restriction B).obj F) c r ≫
        (Sigma.desc (fun _ => 𝟙 (F.obj c)) ≫ α.app c)
    rw [inclusion_cellMap_assoc]
    simp only [inclusion, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, Category.id_comp,
      Category.comp_id]
    change α.app c ≫ 𝟙 (G.obj c) = 𝟙 (F.obj c) ≫ α.app c
    rw [Category.comp_id,Category.id_comp]

/-- The literal whole-fiber coproduct and literal restriction are adjoint. -/
def adjunction : functor B (D := D) ⊣ restriction B where
  unit := unit B
  counit := counit B
  left_triangle_components E := by
    apply NatTrans.ext
    funext c
    apply Sigma.hom_ext
    intro r
    change inclusion B E c r ≫
      (cellMap B ((unit B).app E) c ≫ _) = _
    rw [inclusion_cellMap_assoc]
    simp only [counit, inclusion, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      Category.assoc, Category.comp_id]
    rfl
  right_triangle_components F := by
    apply NatTrans.ext
    funext c
    change inclusion B ((restriction B).obj F) c.obj c.val ≫
      Sigma.desc (fun _ : B.obj c.obj => 𝟙 (F.obj c.obj)) = 𝟙 _
    exact Sigma.ι_comp_desc _ _

variable [Abelian D] [AB4OfSize.{0} D]

instance restriction_limits : PreservesFiniteLimits (restriction B (D := D)) := by
  unfold restriction
  infer_instance

instance restriction_colimits : PreservesFiniteColimits (restriction B (D := D)) := by
  unfold restriction
  infer_instance

instance restriction_additive : (restriction B (D := D)).Additive := by
  unfold restriction
  infer_instance

variable [HasDerivedCategory (C ⥤ D)] [HasDerivedCategory (B.Elements ⥤ D)]

/-- The same adjunction for actual unbounded complexes and their
quasi-isomorphism localizations. -/
def derivedAdjunction :
    (functor B (D := D)).mapDerivedCategory ⊣
      (restriction B (D := D)).mapDerivedCategory :=
  exactDerivedAdjunction (adjunction B)

end ToricPower.ElementPushdown

end
