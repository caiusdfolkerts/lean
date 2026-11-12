module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness detected by an exact family of functors

If a family of exact functors detects the zero object, it detects
exactness of short complexes through their actual homology. In
particular, exactness of a functor can be checked after that family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z a b t

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  {I : Type t} {E : I → Type a} [∀ i, Category.{b} (E i)] [∀ i, Abelian (E i)]
  (G : ∀ i, D ⥤ E i) [∀ i, (G i).Additive]
  [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
  (detect : ∀ M : D, (∀ i, IsZero ((G i).obj M)) → IsZero M)

include detect

/-- Joint detection of zero objects detects the actual homology obstruction. -/
theorem exact_of_jointly_detect_zero (S : ShortComplex D)
    (localExact : ∀ i, (S.map (G i)).Exact) : S.Exact := by
  apply S.exact_iff_isZero_homology.mpr
  apply detect S.homology
  intro i
  exact (S.mapHomologyIso (G i)).isZero_iff.mp
    ((S.map (G i)).exact_iff_isZero_homology.mp (localExact i))

/-- Both finite limits and finite colimits are detected by the same
actual exact family; no global exactness hypothesis is inserted. -/
theorem exactFunctor_of_jointly_detect_zero (F : C ⥤ D) [F.Additive]
    [∀ i, PreservesFiniteLimits (F ⋙ G i)]
    [∀ i, PreservesFiniteColimits (F ⋙ G i)] :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  apply ((Functor.exact_tfae F).out 2 4).mp
  intro S hS
  apply exact_of_jointly_detect_zero G detect (S.map F)
  intro i
  change (S.map (F ⋙ G i)).Exact
  exact hS.map (F ⋙ G i)

end ToricPower

end
