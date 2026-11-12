module

public import ToricPower.ToricCoherentDerivedEmbedding
public import ToricPower.BoundedDerivedIdempotents

/-!
# The literal coherent derived image and its idempotents

The already proved geometric epimorphism lifting gives the fully faithful
bounded coherent inclusion. Its essential image is exactly bounded
quasi-coherent complexes with coherent homology. When the ambient
unbounded derived category has countable coproducts, actual retracts lift
back to the literal bounded coherent category and its idempotents split.
The coproduct input remains explicit for the later reconstruction step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric

namespace ToricPower

universe u v

local instance coherentImageDerivedCategory (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (Coh X) := HasDerivedCategory.standard _

local instance quasicoherentImageDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Exact equality of the geometric essential image with bounded
complexes whose actual homology sheaves are coherent. -/
theorem toricBoundedCoherent_essImage_iff
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (K : DerivedQCoh fan.algebraicRealization) :
    letI := toricScheme_isNoetherian fan
    (boundedCoherentToQuasicoherent fan.algebraicRealization).essImage K ↔
      DerivedCategory.TStructure.t.bounded K ∧
        derivedHomologyIn (coherentToQuasicoherent fan.algebraicRealization).essImage K := by
  letI := toricScheme_isNoetherian fan
  let fullyFaithful := toricBoundedCoherentToQuasicoherentFullyFaithful fan nonempty regular
  letI : (boundedDerivedInclusion (coherentToQuasicoherent
      fan.algebraicRealization)).Full := fullyFaithful.full
  exact boundedDerived_essImage_iff (coherentToQuasicoherent fan.algebraicRealization) K

/-- The source is the original bounded derived category of actual
coherent sheaves. No Karoubi completion or perfect-category replacement
is hidden in this statement. -/
theorem toricDbCoh_isIdempotentComplete_of_countableCoproducts
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    [HasCoproducts.{0} (DerivedQCoh fan.algebraicRealization)] :
    letI := toricScheme_isNoetherian fan
    IsIdempotentComplete (DbCoh fan.algebraicRealization) := by
  letI := toricScheme_isNoetherian fan
  let fullyFaithful := toricBoundedCoherentToQuasicoherentFullyFaithful fan nonempty regular
  letI : (boundedDerivedInclusion (coherentToQuasicoherent
      fan.algebraicRealization)).Full := fullyFaithful.full
  letI : (boundedDerivedInclusion (coherentToQuasicoherent
      fan.algebraicRealization)).Faithful := fullyFaithful.faithful
  exact boundedDerived_idempotentComplete_of_countableCoproducts
    (coherentToQuasicoherent fan.algebraicRealization)

end ToricPower

end
