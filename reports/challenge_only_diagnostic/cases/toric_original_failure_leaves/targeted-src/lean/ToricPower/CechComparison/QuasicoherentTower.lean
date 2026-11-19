module

public import ToricPower.CechComparison.Adapters

section CechComparisonSource00


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.FiniteQuasicoherentCohomologyTower

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

def IsCohomologicallyAcyclic (coefficient : Source.Modules) : Prop :=
  ∀ degree : ℕ, Subsingleton (Cohomology coefficient (degree + 1))

theorem isCohomologicallyAcyclic_of_isFlasque (coefficient : Source.Modules)
    [coefficient.presheaf.IsFlasque] : IsCohomologicallyAcyclic coefficient :=
  fun degree => Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque coefficient degree

structure QuasicoherentResolutionStep (coefficient : Source.Modules) where
  middle : Source.Modules
  next : Source.Modules
  middle_quasicoherent : middle.IsQuasicoherent
  next_quasicoherent : next.IsQuasicoherent
  inclusion : coefficient ⟶ middle
  projection : middle ⟶ next
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

structure QuasicoherentResolutionTower (coefficient : Source.Modules) where
  object : ℕ → Source.Modules
  initial : object 0 ≅ coefficient
  middle : ℕ → Source.Modules
  object_quasicoherent : ∀ stage, (object stage).IsQuasicoherent
  middle_quasicoherent : ∀ stage, (middle stage).IsQuasicoherent
  inclusion : ∀ stage, object stage ⟶ middle stage
  projection : ∀ stage, middle stage ⟶ object (stage + 1)
  zero : ∀ stage, inclusion stage ≫ projection stage = 0
  shortExact : ∀ stage,
    (ShortComplex.mk (inclusion stage) (projection stage) (zero stage)).ShortExact

namespace QuasicoherentResolutionTower

variable {coefficient : Source.Modules}

def successiveCoefficient (quasicoherent : coefficient.IsQuasicoherent)
    (extension : ∀ current : Source.Modules, current.IsQuasicoherent →
      QuasicoherentResolutionStep current) :
    ℕ → {current : Source.Modules // current.IsQuasicoherent}
  | 0 => ⟨coefficient, quasicoherent⟩
  | stage + 1 =>
      let previous := successiveCoefficient quasicoherent extension stage
      let step := extension previous.val previous.property
      ⟨step.next, step.next_quasicoherent⟩

def ofSteps (quasicoherent : coefficient.IsQuasicoherent)
    (extension : ∀ current : Source.Modules, current.IsQuasicoherent →
      QuasicoherentResolutionStep current) : QuasicoherentResolutionTower coefficient where
  object stage := (successiveCoefficient quasicoherent extension stage).val
  initial := Iso.refl _
  middle stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).middle
  object_quasicoherent stage := (successiveCoefficient quasicoherent extension stage).property
  middle_quasicoherent stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).middle_quasicoherent
  inclusion stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).inclusion
  projection stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).projection
  zero stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).zero
  shortExact stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).shortExact

abbrev sequence (tower : QuasicoherentResolutionTower coefficient) (stage : ℕ) :
    ShortComplex Source.Modules :=
  ShortComplex.mk (tower.inclusion stage) (tower.projection stage) (tower.zero stage)

theorem sequence_shortExact (tower : QuasicoherentResolutionTower coefficient) (stage : ℕ) :
    (tower.sequence stage).ShortExact := tower.shortExact stage

-- Explicit source EOF scope closures.
end QuasicoherentResolutionTower
end
end FiniteQuasicoherentCohomologyTower
end BondalThomsen
end

end CechComparisonSource00
