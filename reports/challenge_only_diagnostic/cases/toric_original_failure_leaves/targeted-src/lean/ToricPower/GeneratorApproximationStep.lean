module

public import ToricPower.CoproductFiniteFactorization
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The actual universal approximation and kernel-killing extension

The first approximation is the coproduct of every map from a shift of
the proposed generator. The next approximation forms the distinguished
cone of the coproduct of all such maps killed by the current map to the
target. Both constructions use actual morphisms and actual coproducts.
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
  [HasCoproducts.{w} C] [LocallySmall.{w} C]

variable (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]

theorem coproductObjects_shift (n : ℤ) {Y : C} (member : coproductObjects.{u, v, w} Q Y) :
    coproductObjects.{u, v, w} Q (Y⟦n⟧) := by
  obtain ⟨I, family, members, ⟨e⟩⟩ := member
  exact ⟨I, fun i => (family i)⟦n⟧, (fun i => Q.le_shift n _ (members i)),
    ⟨(PreservesCoproduct.iso (shiftFunctor C n) family).symm ≪≫
      (shiftFunctor C n).mapIso e⟩⟩

/-- The full indexing type of all maps from all shifts of one object. -/
def ShiftedMapIndex (G X : C) : Type w := Σ n : ℤ, Shrink.{w} (G⟦n⟧ ⟶ X)

def shiftedMapValue (G X : C) (i : ShiftedMapIndex.{u, v, w} G X) : G⟦i.1⟧ ⟶ X :=
  (equivShrink (G⟦i.1⟧ ⟶ X)).symm i.2

/-- The actual coproduct of all shifted-generator maps surjects onto
the Hom group from every shift of the generator. -/
theorem exists_generator_approximation (G X : C) (member : Q G) :
    ∃ (Y : C) (p : Y ⟶ X), coproductObjects.{u, v, w} Q Y ∧
      ∀ (n : ℤ) (f : G⟦n⟧ ⟶ X), ∃ (lift : G⟦n⟧ ⟶ Y), lift ≫ p = f := by
  let family : ShiftedMapIndex.{u, v, w} G X → C := fun i => G⟦i.1⟧
  let p : (∐ family) ⟶ X := Sigma.desc (shiftedMapValue G X)
  refine ⟨∐ family, p, ⟨ShiftedMapIndex.{u, v, w} G X, family,
    (fun i => Q.le_shift i.1 _ member), ⟨Iso.refl _⟩⟩, ?_⟩
  intro n f
  refine ⟨Sigma.ι family ⟨n, equivShrink _ f⟩, ?_⟩
  simp [p, Sigma.ι_comp_desc, shiftedMapValue]

/-- All shifted-generator maps into Y whose composite with p is zero. -/
def ShiftedKernelIndex (G : C) {X Y : C} (p : Y ⟶ X) : Type w :=
  Σ n : ℤ, Shrink.{w} { f : G⟦n⟧ ⟶ Y // f ≫ p = 0 }

def shiftedKernelValue (G : C) {X Y : C} (p : Y ⟶ X)
    (i : ShiftedKernelIndex.{u, v, w} G p) : G⟦i.1⟧ ⟶ Y :=
  ((equivShrink { f : G⟦i.1⟧ ⟶ Y // f ≫ p = 0 }).symm i.2).val

theorem shiftedKernelValue_comp (G : C) {X Y : C} (p : Y ⟶ X)
    (i : ShiftedKernelIndex.{u, v, w} G p) : shiftedKernelValue G p i ≫ p = 0 :=
  ((equivShrink { f : G⟦i.1⟧ ⟶ Y // f ≫ p = 0 }).symm i.2).property

/-- Kill every shifted-generator map in the kernel using one actual
distinguished cone, while retaining exact finite factorization of maps
from the specified compact source class. -/
theorem exists_killing_extension
    (contained : Q ≤ P) (compact : ∀ X, P X → CoproductCompact.{u, v, w} X)
    (G : C) (member : Q G) {X Y : C} (p : Y ⟶ X)
    (factor : factorizationTargets P Q Y) :
    ∃ (Y' : C) (transition : Y ⟶ Y') (p' : Y' ⟶ X),
      factorizationTargets P Q Y' ∧ transition ≫ p' = p ∧
      ∀ (n : ℤ) (f : G⟦n⟧ ⟶ Y), f ≫ p = 0 → f ≫ transition = 0 := by
  let family : ShiftedKernelIndex.{u, v, w} G p → C := fun i => G⟦i.1⟧
  let evaluation : (∐ family) ⟶ Y := Sigma.desc (shiftedKernelValue G p)
  have killed : evaluation ≫ p = 0 := by
    apply Sigma.hom_ext
    intro i
    simpa only [evaluation, Sigma.ι_comp_desc_assoc, comp_zero] using
      shiftedKernelValue_comp G p i
  obtain ⟨Y', transition, boundary, distinguished⟩ :=
    distinguished_cocone_triangle evaluation
  let T : Triangle C := Triangle.mk evaluation transition boundary
  obtain ⟨p', equation⟩ := T.yoneda_exact₂ distinguished p killed
  have coproductMember : coproductObjects.{u, v, w} Q (∐ family) :=
    ⟨ShiftedKernelIndex.{u, v, w} G p, family,
      (fun i => Q.le_shift i.1 _ member), ⟨Iso.refl _⟩⟩
  have newFactor : factorizationTargets P Q Y' :=
    factorizationTargets_extension P Q contained T.rotate
      (rot_of_distTriang T distinguished) factor
      (coproductObjects_factorization P Q compact _
        (coproductObjects_shift Q 1 coproductMember))
  refine ⟨Y', transition, p', newFactor, equation.symm, ?_⟩
  intro n f zero
  have component : Sigma.ι family ⟨n, equivShrink _ ⟨f, zero⟩⟩ ≫ evaluation = f := by
    simp [evaluation, Sigma.ι_comp_desc, shiftedKernelValue]
  rw [← component, Category.assoc]
  rw [show evaluation ≫ transition = 0 from comp_distTriang_mor_zero₁₂ T distinguished,
    comp_zero]

end ToricPower.CompactExtraction

end

