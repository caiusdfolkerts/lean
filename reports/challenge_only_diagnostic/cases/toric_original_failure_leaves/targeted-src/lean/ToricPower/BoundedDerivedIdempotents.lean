module

public import ToricPower.BoundedDerivedEssentialImage
public import ToricPower.DerivedBoundedRetracts
public import ToricPower.RetractClosedIdempotents
public import ToricPower.FullyFaithfulThickImage
public import ToricPower.TriangulatedIdempotents

/-!
# Split idempotents in the literal bounded derived source

The exact bounded-derived essential-image theorem identifies every
ambient retract by its bounded coherent homology. Idempotents therefore
split in the essential image, and the actual fully faithful inclusion
transports those splittings back to the bounded derived source category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful]
  [(boundedDerivedInclusion F).Full] [(boundedDerivedInclusion F).Faithful]

theorem exactFunctor_essImage_stableUnderRetracts :
    F.essImage.IsStableUnderRetracts := by
  simpa only [ObjectProperty.map_top] using
    fullyFaithful_map_stableUnderRetracts F (⊤ : ObjectProperty A)

/-- The derived retract has bounded homology in the original abelian
image; truncation induction supplies its actual bounded-source lift. -/
theorem boundedDerived_essImage_stableUnderRetracts :
    (boundedDerivedInclusion F).essImage.IsStableUnderRetracts := by
  letI := exactFunctor_essImage_stableUnderRetracts F
  constructor
  intro X Y r member
  obtain ⟨bounded, homology⟩ := (boundedDerived_essImage_iff F Y).mp member
  apply (boundedDerived_essImage_iff F X).mpr
  refine ⟨derived_bounded_of_retract r bounded, ?_⟩
  intro q
  exact F.essImage.prop_of_retract
    (r.map (DerivedCategory.homologyFunctor B q)) (homology q)

include F

/-- This concludes in the literal `DerivedCategory.Bounded A`, not in
its formal Karoubi envelope or an assumed category of perfect objects. -/
theorem boundedDerived_idempotentComplete_of_embedding
    [IsIdempotentComplete (DerivedCategory B)] :
    IsIdempotentComplete (DerivedCategory.Bounded A) := by
  letI := boundedDerived_essImage_stableUnderRetracts F
  letI : IsIdempotentComplete (boundedDerivedInclusion F).EssImageSubcategory := inferInstance
  exact (CategoryTheory.Idempotents.isIdempotentComplete_iff_of_equivalence
    (boundedDerivedInclusion F).toEssImage.asEquivalence).mpr inferInstance

/-- Actual countable coproducts in the ambient derived category suffice,
using the already checked idempotent-telescope construction. -/
theorem boundedDerived_idempotentComplete_of_countableCoproducts
    [HasCoproducts.{0} (DerivedCategory B)] :
    IsIdempotentComplete (DerivedCategory.Bounded A) := by
  letI : IsIdempotentComplete (DerivedCategory B) :=
    CompactExtraction.idempotentComplete_of_countableCoproducts
  exact boundedDerived_idempotentComplete_of_embedding F

end ToricPower

end
