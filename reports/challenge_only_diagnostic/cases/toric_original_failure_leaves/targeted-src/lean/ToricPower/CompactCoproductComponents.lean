module

public import ToricPower.CoproductFiniteFactorization

/-!
# Finite-support maps are detected by coproduct coordinates

An arbitrary coproduct has coordinate projections in a category with zero
morphisms. These need not jointly detect all maps into the coproduct. They
do detect maps with finite support, which is exactly what compactness gives.
This distinction is used in the mapping-telescope argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v w
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} C]

/-- The coordinate projection from an actual coproduct, defined by its
values on the summands. -/
def coproductProjection {I : Type w} (family : I → C) (i : I) :
    (∐ family) ⟶ family i := by
  classical
  exact Sigma.desc (fun j => if h : j = i then eqToHom (congrArg family h) else 0)

@[simp, reassoc]
theorem coproduct_ι_projection_same {I : Type w} (family : I → C) (i : I) :
    Sigma.ι family i ≫ coproductProjection family i = 𝟙 (family i) := by
  simp [coproductProjection, Sigma.ι_comp_desc]

@[simp, reassoc]
theorem coproduct_ι_projection_ne {I : Type w} (family : I → C) {i j : I}
    (different : i ≠ j) : Sigma.ι family i ≫ coproductProjection family j = 0 := by
  simp [coproductProjection, Sigma.ι_comp_desc, different]

theorem finiteCoproductInclusion_projection {I : Type w} (family : I → C)
    (s : Finset I) (i : s) :
    (biproduct.isoCoproduct (fun j : s => family j)).hom ≫
        finiteCoproductInclusion family s ≫ coproductProjection family i =
      biproduct.π (fun j : s => family j) i := by
  classical
  apply biproduct.hom_ext'
  intro j
  by_cases equal : j = i
  · subst j
    simp [biproduct.isoCoproduct_hom, finiteCoproductInclusion,
      Sigma.ι_comp_desc]
  · have different : (j : I) ≠ (i : I) := fun h => equal (Subtype.ext h)
    simp [biproduct.isoCoproduct_hom, finiteCoproductInclusion,
      Sigma.ι_comp_desc, equal, different]

/-- Coordinate projections detect a map from a compact source. The proof
uses finite support before using the finite biproduct universal property. -/
theorem CoproductCompact.eq_zero_of_projections {X : C}
    (compact : CoproductCompact.{u, v, w} X) {I : Type w} (family : I → C)
    (f : X ⟶ ∐ family) (zero : ∀ i, f ≫ coproductProjection family i = 0) : f = 0 := by
  classical
  obtain ⟨s, lift, factor⟩ := compact I family f
  let e := biproduct.isoCoproduct (fun i : s => family i)
  have vanish : lift ≫ e.inv = 0 := by
    apply biproduct.hom_ext
    intro i
    rw [zero_comp, ← finiteCoproductInclusion_projection family s i]
    simp only [Category.assoc, e, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, factor, zero]
  have liftZero : lift = 0 := by
    rw [← cancel_mono e.inv, vanish, zero_comp]
  rw [← factor, liftZero, zero_comp]

end ToricPower.CompactExtraction

end
