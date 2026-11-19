module

public import ToricPower.CompactCoproductComponents
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The map defining a sequential mapping telescope

For a sequence `F`, the telescope map on the actual coproduct is `1 - s`,
where `s` sends the `n`th summand to the next summand using the transition
map. Its action on maps from a compact object is injective. The shifted
version is proved using the actual shift equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{0} C]

def telescopeMap (F : ℕ ⥤ C) : (∐ F.obj) ⟶ ∐ F.obj :=
  𝟙 _ - Sigma.desc (fun n =>
    F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1))

@[reassoc]
theorem ι_telescopeMap (F : ℕ ⥤ C) (n : ℕ) :
    Sigma.ι F.obj n ≫ telescopeMap F =
      Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1) := by
  simp [telescopeMap, Preadditive.comp_sub, Sigma.ι_comp_desc]

theorem telescopeMap_projection_zero (F : ℕ ⥤ C) :
    telescopeMap F ≫ coproductProjection F.obj 0 = coproductProjection F.obj 0 := by
  apply Sigma.hom_ext
  intro n
  rw [ι_telescopeMap_assoc, Preadditive.sub_comp]
  simp

theorem telescopeMap_projection_succ (F : ℕ ⥤ C) (n : ℕ) :
    telescopeMap F ≫ coproductProjection F.obj (n + 1) =
      coproductProjection F.obj (n + 1) - coproductProjection F.obj n ≫
        F.map (homOfLE (Nat.le_succ n)) := by
  apply Sigma.hom_ext
  intro i
  rw [ι_telescopeMap_assoc, Preadditive.sub_comp, Preadditive.comp_sub]
  by_cases equal : i = n
  · subst i
    simp [Category.assoc, coproduct_ι_projection_same_assoc]
  · have successorDifferent : i + 1 ≠ n + 1 := by omega
    simp [Category.assoc, coproduct_ι_projection_ne_assoc, equal, successorDifferent]

/-- The telescope map is injective on morphisms from a compact source.
Coordinate recursion alone would be insufficient without finite support. -/
theorem telescopeMap_comp_injective {X : C}
    (compact : CoproductCompact.{u, v, 0} X) (F : ℕ ⥤ C)
    (f : X ⟶ ∐ F.obj) (killed : f ≫ telescopeMap F = 0) : f = 0 := by
  apply compact.eq_zero_of_projections F.obj f
  intro n
  induction n with
  | zero =>
      have equation := congrArg (fun g => g ≫ coproductProjection F.obj 0) killed
      simpa only [Category.assoc, telescopeMap_projection_zero, zero_comp] using equation
  | succ n induction =>
      have equation := congrArg
        (fun g => g ≫ coproductProjection F.obj (n + 1)) killed
      rw [Category.assoc, telescopeMap_projection_succ, Preadditive.comp_sub,
        ← Category.assoc, induction, zero_comp, sub_zero, zero_comp] at equation
      exact equation

/-- The shifted telescope map is injective on maps from `X` whenever
the negative shift of `X` is compact. -/
theorem shifted_telescopeMap_comp_injective {X : C}
    (compact : CoproductCompact.{u, v, 0} (X⟦(-1 : ℤ)⟧)) (F : ℕ ⥤ C)
    (f : X ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (killed : f ≫ (telescopeMap F)⟦(1 : ℤ)⟧' = 0) : f = 0 := by
  let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  let g : X⟦(-1 : ℤ)⟧ ⟶ ∐ F.obj := f⟦(-1 : ℤ)⟧' ≫ e.hom.app _
  have killed' : g ≫ telescopeMap F = 0 := by
    dsimp only [g]
    have natural : (telescopeMap F)⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫ e.hom.app (∐ F.obj) =
        e.hom.app (∐ F.obj) ≫ telescopeMap F := e.hom.naturality (telescopeMap F)
    rw [Category.assoc, ← natural]
    change f⟦(-1 : ℤ)⟧' ≫ (telescopeMap F)⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫
      e.hom.app _ = 0
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, killed,
      CategoryTheory.Functor.map_zero, zero_comp]
  have zeroG := telescopeMap_comp_injective compact F g killed'
  apply (shiftFunctor C (-1 : ℤ)).map_injective
  rw [CategoryTheory.Functor.map_zero]
  apply (cancel_mono (e.hom.app (∐ F.obj))).mp
  simpa only [zero_comp] using zeroG

end ToricPower.CompactExtraction

end
