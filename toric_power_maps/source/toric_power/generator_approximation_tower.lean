module

public import ToricPower.GeneratorApproximationStep
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# A genuine sequential generator approximation

The stages and transition maps are constructed recursively from the
universal coproduct and the actual kernel-killing distinguished cone.
Every map from a shifted generator into the target lifts to stage zero,
and every such map killed in the target is killed by the next transition.
Each stage retains the proved finite-factorization property.
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

structure ApproximationStage (P Q : ObjectProperty C) (X : C) where
  obj : C
  projection : obj ⟶ X
  factor : factorizationTargets P Q obj

structure ApproximationStep (G : C) {P Q : ObjectProperty C} {X : C}
    (previous : ApproximationStage P Q X) where
  next : ApproximationStage P Q X
  transition : previous.obj ⟶ next.obj
  compatible : transition ≫ next.projection = previous.projection
  kills : ∀ (n : ℤ) (f : G⟦n⟧ ⟶ previous.obj),
    f ≫ previous.projection = 0 → f ≫ transition = 0

/-- The complete actual approximation tower and its verified properties. -/
structure GeneratorApproximation (P Q : ObjectProperty C) (G X : C) where
  sequence : ℕ ⥤ C
  projection : ∀ n, sequence.obj n ⟶ X
  compatible : ∀ n, sequence.map (homOfLE (Nat.le_succ n)) ≫ projection (n + 1) =
    projection n
  initial : ∀ (n : ℤ) (f : G⟦n⟧ ⟶ X),
    ∃ (lift : G⟦n⟧ ⟶ sequence.obj 0), lift ≫ projection 0 = f
  kills : ∀ (i : ℕ) (n : ℤ) (f : G⟦n⟧ ⟶ sequence.obj i),
    f ≫ projection i = 0 → f ≫ sequence.map (homOfLE (Nat.le_succ i)) = 0
  factor : ∀ i, factorizationTargets P Q (sequence.obj i)

variable (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]

/-- Existence of the tower uses no localization or approximation axiom:
its stages are the literal coproducts and distinguished cones constructed
in GeneratorApproximationStep. -/
theorem generatorApproximation_nonempty
    (contained : Q ≤ P) (compact : ∀ X, P X → CoproductCompact.{u, v, w} X)
    (G X : C) (member : Q G) : Nonempty (GeneratorApproximation P Q G X) := by
  obtain ⟨Y, p, memberY, initial⟩ := exists_generator_approximation Q G X member
  let start : ApproximationStage P Q X :=
    ⟨Y, p, coproductObjects_factorization P Q compact Y memberY⟩
  have nextExists (S : ApproximationStage P Q X) : Nonempty (ApproximationStep G S) := by
    obtain ⟨Y', transition, p', factor, compatible, kills⟩ :=
      exists_killing_extension P Q contained compact G member S.projection S.factor
    exact ⟨⟨⟨Y', p', factor⟩, transition, compatible, kills⟩⟩
  let step (S : ApproximationStage P Q X) := Classical.choice (nextExists S)
  let stages : ℕ → ApproximationStage P Q X :=
    Nat.rec start (fun _ S => (step S).next)
  let transition (n : ℕ) : (stages n).obj ⟶ (stages (n + 1)).obj :=
    (step (stages n)).transition
  let sequence : ℕ ⥤ C := Functor.ofSequence transition
  refine ⟨{
    sequence := sequence
    projection := fun n => (stages n).projection
    compatible := ?_
    initial := initial
    kills := ?_
    factor := fun n => (stages n).factor
  }⟩
  · intro n
    change (Functor.ofSequence transition).map _ ≫ _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (step (stages n)).compatible
  · intro i n f killed
    change f ≫ (Functor.ofSequence transition).map _ = 0
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (step (stages i)).kills n f killed

end ToricPower.CompactExtraction

end

