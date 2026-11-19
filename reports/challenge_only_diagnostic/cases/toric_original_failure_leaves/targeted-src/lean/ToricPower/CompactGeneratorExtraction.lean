module

public import ToricPower.CompactCoproductUniverse
public import ToricPower.GeneratorApproximationTower
public import ToricPower.GeneratorDetectsIsomorphisms
public import ToricPower.TelescopeCompactFactorization

/-!
# Finite extraction from a genuine right generator

This proves the compact-generator extraction argument using the actual
universal approximation tower, its mapping telescope, and the exact
finite-factorization lemmas. The ambient category is not assumed to be
bounded. Compactness is the explicit finite-subcoproduct condition.

The theorem is phrased for a triangulated source class P and a thick
collection Q contained in P. If Q contains a genuine right generator and
every object of P is compact, then every object of P belongs to Q. The
application to a concrete derived category must prove the coproduct,
compactness, and right-generation hypotheses.
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
  [Q.IsStableUnderRetracts]

/-- Exact finite extraction from right generation in the unbounded
ambient category. All coproducts, cones, maps, and retracts are actual
objects and morphisms of C. -/
theorem le_of_rightGenerator
    (contained : Q ≤ P) (compact : ∀ X, P X → CoproductCompact.{u, v, w} X)
    (G : C) (member : Q G) (generator : IsRightGenerator G) : P ≤ Q := by
  letI : HasCoproducts.{0} C := has_smallest_coproducts_of_hasCoproducts
  have smallCompact (Y : C) (hY : P Y) : CoproductCompact.{u, v, 0} Y :=
    (compact Y hY).small
  intro X hX
  let approximation := Classical.choice
    (generatorApproximation_nonempty P Q contained compact G X member)
  let T := Classical.choice (telescope_nonempty approximation.sequence)
  obtain ⟨comparison, comparisonEq⟩ :=
    T.exists_desc approximation.projection approximation.compatible
  have generatorMember (n : ℤ) : P (G⟦n⟧) :=
    P.le_shift n G (contained G member)
  have comparisonBijective (n : ℤ) :
      Function.Bijective (fun f : G⟦n⟧ ⟶ T.obj => f ≫ comparison) := by
    constructor
    · have zeroCriterion (f : G⟦n⟧ ⟶ T.obj) (zero : f ≫ comparison = 0) : f = 0 := by
        obtain ⟨j, lift, factor⟩ := T.factor_from_compact
          (smallCompact _ (generatorMember n))
          (smallCompact _ (P.le_shift (-1 : ℤ) _ (generatorMember n))) f
        have killed : lift ≫ approximation.projection j = 0 := by
          rw [← comparisonEq j, ← Category.assoc, factor, zero]
        have killedNext := approximation.kills j n lift killed
        rw [← factor, ← T.transition_ι j, ← Category.assoc, killedNext, zero_comp]
      intro f g equality
      change f ≫ comparison = g ≫ comparison at equality
      apply sub_eq_zero.mp
      apply zeroCriterion
      rw [Preadditive.sub_comp, equality, sub_self]
    · intro f
      obtain ⟨lift, factor⟩ := approximation.initial n f
      refine ⟨lift ≫ T.ι 0, ?_⟩
      change (lift ≫ T.ι 0) ≫ comparison = f
      rw [Category.assoc, comparisonEq, factor]
  haveI : IsIso comparison := isIso_of_generator_hom_bijective G generator
    comparison comparisonBijective
  obtain ⟨j, lift, factor⟩ := T.factor_from_compact
    (smallCompact X hX) (smallCompact _ (P.le_shift (-1 : ℤ) _ hX)) (inv comparison)
  have retract : Retract X (approximation.sequence.obj j) := {
    i := lift
    r := approximation.projection j
    retract := by
      rw [← comparisonEq j, ← Category.assoc, factor, IsIso.inv_hom_id]
  }
  exact prop_of_retract_of_factorization P Q hX (approximation.factor j) retract

end ToricPower.CompactExtraction

end

