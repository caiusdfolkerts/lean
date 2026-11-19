module

public import ToricPower.FiniteTriangulatedFactorization
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite factorization of compact sources through coproduct extensions

The compactness condition below is the explicit finite-subcoproduct
factorization condition for every actual coproduct. The argument proves
that a compact source mapping into any finite extension of coproducts of
`Q` factors through an actual object of `Q`, provided `Q` is triangulated.
A retract of such a finite stage consequently belongs to `Q` when `Q`
is closed under retracts. The telescope step is kept separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v w
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]

/-- The canonical inclusion of an actual finite subcoproduct. -/
def finiteCoproductInclusion {I : Type w} (family : I → C) (s : Finset I) :
    (∐ fun i : s => family i) ⟶ ∐ family :=
  Sigma.desc (fun i : s => Sigma.ι family i)

/-- Compactness in the finite-support form: every map into an arbitrary
coproduct factors through one of its actual finite subcoproducts. -/
def CoproductCompact (X : C) : Prop :=
  ∀ (I : Type w) (family : I → C) (f : X ⟶ ∐ family),
    ∃ (s : Finset I) (lift : X ⟶ ∐ fun i : s => family i),
      lift ≫ finiteCoproductInclusion family s = f

/-- Actual arbitrary coproducts of objects in the indicated collection,
including isomorphic choices of the coproduct object. -/
def coproductObjects (Q : ObjectProperty C) : ObjectProperty C :=
  fun Y => ∃ (I : Type w) (family : I → C),
    (∀ i, Q (family i)) ∧ Nonempty ((∐ family) ≅ Y)

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]

/-- A triangulated collection contains the actual finite coproducts of
its objects. This uses their ordinary finite biproduct comparisons. -/
theorem prop_finiteCoproduct {I : Type w} [Finite I] (family : I → C)
    (members : ∀ i, Q (family i)) : Q (∐ family) := by
  apply Q.prop_of_iso (biproduct.isoCoproduct family)
  apply Q.prop_of_iso (biproduct.isoProduct family).symm
  exact Q.prop_product members

/-- Compact sources factor through finite coproducts of actual objects
of `Q`. The explicit coproduct comparison retains the original map. -/
theorem coproductObjects_factorization
    (compact : ∀ X, P X → CoproductCompact.{u, v, w} X) :
    coproductObjects.{u, v, w} Q ≤ factorizationTargets P Q := by
  rintro Y ⟨I, family, members, ⟨e⟩⟩ X hX f
  obtain ⟨s, lift, factor⟩ := compact X hX I family (f ≫ e.inv)
  refine ⟨∐ (fun i : s => family i), prop_finiteCoproduct Q _ (fun i => members i),
    lift, finiteCoproductInclusion family s ≫ e.hom, ?_⟩
  rw [← Category.assoc, factor, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Every map from a compact source into a finite extension of arbitrary
coproducts factors through one actual object of the triangulated collection. -/
theorem finiteCoproductExtensions_factorization
    (contained : Q ≤ P) (compact : ∀ X, P X → CoproductCompact.{u, v, w} X)
    (n : ℕ) :
    (coproductObjects.{u, v, w} Q).extensionProductIter n ≤ factorizationTargets P Q :=
  factorizationTargets_extensionProductIter P Q contained (coproductObjects Q)
    (coproductObjects_factorization P Q compact) n

/-- The exact finite-stage retract extraction used in the compact
single-generator theorem. No telescope approximation is assumed here. -/
theorem prop_of_compact_retract_finiteCoproductExtensions [Q.IsStableUnderRetracts]
    (contained : Q ≤ P) (compact : ∀ X, P X → CoproductCompact.{u, v, w} X)
    {X Y : C} (hX : P X) (n : ℕ)
    (stage : (coproductObjects.{u, v, w} Q).extensionProductIter n Y)
    (retract : Retract X Y) : Q X :=
  prop_of_retract_of_factorization P Q hX
    (finiteCoproductExtensions_factorization P Q contained compact n Y stage) retract

end ToricPower.CompactExtraction

end
