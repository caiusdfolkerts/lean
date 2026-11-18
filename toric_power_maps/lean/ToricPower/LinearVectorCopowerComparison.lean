module

public import ToricPower.LinearVectorCopower
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual vector copowers commute with linear coproduct-preserving functors

The comparison uses the original unrestricted basis coproduct. Its
formula on every vector inclusion proves naturality in both the copied
object and the vector coefficient, without a finite-dimensional premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u v w

variable (k : Type u) [Field k]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  {B : Type w} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} A] [HasCoproducts.{u} B]
  (F : A ⥤ B) [F.Additive] [F.Linear k]
  [PreservesColimitsOfSize.{u,u} F]

/-- The canonical comparison of the original basis coproducts. -/
def vectorCopowerComparisonIso (P : A) (M : ModuleCat.{u} k) :
    F.obj (vectorCopower k P M) ≅ vectorCopower k (F.obj P) M :=
  PreservesCoproduct.iso F (fun _ : Module.Free.ChooseBasisIndex k M => P)

/-- Mapping every genuine vector inclusion commutes with the comparison. -/
@[reassoc]
theorem vectorCopowerComparisonIso_inclusion (P : A) (M : ModuleCat.{u} k)
    (x : M) :
    F.map (vectorCopowerInclusion k P M x) ≫
        (vectorCopowerComparisonIso k F P M).hom =
      vectorCopowerInclusion k (F.obj P) M x := by
  let actual := (Linear.rightComp k (F.obj P)
    (vectorCopowerComparisonIso k F P M).hom).comp
      ((F.mapLinearMap k).comp (vectorCopowerInclusion k P M))
  have equal : actual = vectorCopowerInclusion k (F.obj P) M := by
    apply (Module.Free.chooseBasis k M).ext
    intro i
    change F.map (vectorCopowerInclusion k P M (Module.Free.chooseBasis k M i)) ≫
      (vectorCopowerComparisonIso k F P M).hom =
        vectorCopowerInclusion k (F.obj P) M (Module.Free.chooseBasis k M i)
    rw [vectorCopowerInclusion_basis, vectorCopowerInclusion_basis]
    apply (cancel_mono (vectorCopowerComparisonIso k F P M).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change F.map (Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => P) i) =
      Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => F.obj P) i ≫
        sigmaComparison F (fun _ : Module.Free.ChooseBasisIndex k M => P)
    exact (ι_comp_sigmaComparison F _ i).symm
  exact DFunLike.congr_fun equal x

/-- The mapped vector inclusions still jointly detect all maps. -/
theorem map_vectorCopower_hom_ext (P : A) (M : ModuleCat.{u} k) {E : B}
    {f g : F.obj (vectorCopower k P M) ⟶ E}
    (equal : ∀ x : M, F.map (vectorCopowerInclusion k P M x) ≫ f =
      F.map (vectorCopowerInclusion k P M x) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit F
    (fun _ : Module.Free.ChooseBasisIndex k M => P)).hom_ext
  intro i
  change F.map (Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => P) i.as) ≫ f =
    F.map (Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => P) i.as) ≫ g
  simpa only [vectorCopowerInclusion_basis] using
    equal (Module.Free.chooseBasis k M i.as)

/-- The comparison retains the actual change of vector coefficient. -/
@[reassoc]
theorem vectorCopowerComparisonIso_map (P : A)
    {M N : ModuleCat.{u} k} (f : M ⟶ N) :
    F.map ((vectorCopowerFunctor k P).map f) ≫
        (vectorCopowerComparisonIso k F P N).hom =
      (vectorCopowerComparisonIso k F P M).hom ≫
        (vectorCopowerFunctor k (F.obj P)).map f := by
  apply map_vectorCopower_hom_ext k F P M
  intro x
  rw [← Category.assoc, ← Functor.map_comp,
    vectorCopowerInclusion_map, vectorCopowerComparisonIso_inclusion,
    ← Category.assoc, vectorCopowerComparisonIso_inclusion,
    vectorCopowerInclusion_map]

/-- The comparison also retains the actual arrow of copied objects. -/
@[reassoc]
theorem vectorCopowerComparisonIso_mapObject {P Q : A} (f : P ⟶ Q)
    (M : ModuleCat.{u} k) :
    F.map (vectorCopowerMapObject k f M) ≫
        (vectorCopowerComparisonIso k F Q M).hom =
      (vectorCopowerComparisonIso k F P M).hom ≫
        vectorCopowerMapObject k (F.map f) M := by
  apply map_vectorCopower_hom_ext k F P M
  intro x
  rw [← Category.assoc, ← Functor.map_comp,
    vectorCopowerInclusion_mapObject, Functor.map_comp,
    Category.assoc, vectorCopowerComparisonIso_inclusion,
    ← Category.assoc, vectorCopowerComparisonIso_inclusion,
    vectorCopowerInclusion_mapObject]

/-- A natural isomorphism in every vector coefficient. -/
def vectorCopowerFunctorComparisonIso (P : A) :
    vectorCopowerFunctor k P ⋙ F ≅ vectorCopowerFunctor k (F.obj P) :=
  NatIso.ofComponents (vectorCopowerComparisonIso k F P)
    (fun f => vectorCopowerComparisonIso_map k F P f)

end ToricPower.Cellular

end
