module

public import ToricPower.InternalDualUnitFrames

/-!
# Canonical inverse-cell frames under strong monoidal pullback

Naturality of the original internal-dual comparison and the original
finite-sum projections identify each inverse-cell generator with its
literal dual basis vector. The statement applies to actual scheme
pullback; all frame compatibility is an equality of original maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Monoidal]
  {I : Type} [Fintype I] (L M : I → C)
  [∀ i, HasLeftDual (L i)] [HasLeftDual (⨁ L)]
  (inverse : ∀ i, M i ≅ (internalDual C).obj (op (L i)))
  (frame : ∀ i, 𝟙_ D ≅ F.obj (L i))
  (totalFrame : (⨁ (fun _ : I => 𝟙_ D)) ≅ F.obj (⨁ L))

/-- The actual inverse label is trivialized by dualizing the specified
original label frame through the canonical pullback comparison. -/
def inverseCellPullbackFrame (i : I) : F.obj (M i) ≅ 𝟙_ D :=
  F.mapIso (inverse i) ≪≫
    asIso ((internalDualComparison F).app (op (L i))) ≪≫
      (internalDual D).mapIso (frame i).op ≪≫ internalDualUnitIso D

/-- The corresponding specified frame of the full actual internal dual. -/
def totalInternalDualPullbackFrame :
    F.obj ((internalDual C).obj (op (⨁ L))) ≅ ⨁ (fun _ : I => 𝟙_ D) :=
  asIso ((internalDualComparison F).app (op (⨁ L))) ≪≫
    internalDualInUnitFrames totalFrame

/-- Every original inverse-cell inclusion becomes the same-index
dual basis inclusion. No matrix entries are chosen independently. -/
theorem inverseCellPullbackFrame_generator (i : I)
    (projections : ∀ j : I,
      totalFrame.hom ≫ F.map (biproduct.π L j) =
        biproduct.π (fun _ : I => 𝟙_ D) j ≫ (frame j).hom) :
    (inverseCellPullbackFrame F L M inverse frame i).inv ≫
      F.map ((inverse i).hom ≫ (internalDual C).map (biproduct.π L i).op) ≫
        (totalInternalDualPullbackFrame F L totalFrame).hom =
      biproduct.ι (fun _ : I => 𝟙_ D) i := by
  apply (cancel_epi (inverseCellPullbackFrame F L M inverse frame i).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply biproduct.hom_ext
  intro j
  simp only [totalInternalDualPullbackFrame, internalDualInUnitFrames,
    Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    internalDualUnitBiproductIso_hom_π]
  have natural : F.map ((internalDual C).map (biproduct.π L i).op) ≫
      (internalDualComparison F).app (op (⨁ L)) =
    (internalDualComparison F).app (op (L i)) ≫
      (internalDual D).map (F.map (biproduct.π L i)).op :=
    (internalDualComparison F).naturality (biproduct.π L i).op
  rw [Functor.map_comp, Category.assoc,
    ← Category.assoc (F.map ((internalDual C).map (biproduct.π L i).op))
      ((internalDualComparison F).app (op (⨁ L))), natural, Category.assoc]
  change F.map (inverse i).hom ≫ (internalDualComparison F).app (op (L i)) ≫
      (internalDual D).map (F.map (biproduct.π L i)).op ≫
        (internalDual D).map totalFrame.hom.op ≫
          (internalDual D).map (biproduct.ι (fun _ : I => 𝟙_ D) j).op ≫
            (internalDualUnitIso D).hom = _
  rw [← Functor.map_comp_assoc, ← op_comp,
    ← Functor.map_comp_assoc, ← op_comp,
    projections]
  by_cases same : j = i
  · subst j
    rw [biproduct.ι_π_self_assoc]
    simp only [inverseCellPullbackFrame, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, Iso.op_hom, Category.assoc, biproduct.ι_π_self, Category.comp_id]
  · rw [biproduct.ι_π_ne_assoc _ same, zero_comp, op_zero,
      Functor.map_zero, zero_comp, comp_zero, comp_zero]
    rw [biproduct.ι_π_ne _ (Ne.symm same), comp_zero]

end ToricPower

end
