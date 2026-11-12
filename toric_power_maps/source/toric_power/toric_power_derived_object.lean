module

public import ToricPower.PrincipalStatements
public import ToricPower.ArrangementDerivedCech
public import ToricPower.ToricCoherentDerivedEmbedding

/-!
# The literal bounded coherent power object in the unbounded ambient category

Embedding a coherent sheaf in degree zero and applying the actual exact
finite pushforward agrees with the ordinary power-map direct image.
The comparison below connects the geometric detection theorem to the
precise object used in the paper's principal statement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

local instance powerObjectCoherentDerived (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (Coh X) := HasDerivedCategory.standard _
local instance powerObjectQuasicoherentDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

/-- The actual bounded coherent embedding commutes with degree-zero
sheaves, through the genuine derived single-functor comparison. -/
def coherentSingleQuasicoherentIso (X : Scheme.{u}) [IsLocallyNoetherian X] (M : Coh X) :
    (boundedCoherentToQuasicoherent X).obj (coherentSingle X M) ≅
      (DerivedCategory.singleFunctor (QCoh X) 0).obj ((coherentToQuasicoherent X).obj M) :=
  ((coherentToQuasicoherent X).mapDerivedCategorySingleFunctor 0).app M

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (hne : fan.cones.Nonempty) (b : fan.Ray → ℤ)

/-- The original bounded coherent power object embeds as the actual
derived pushforward of the same Cartier line, without any replacement
of the original bounded coherent category. -/
def toricDbPowerInvariantQuasicoherentIso (ell : ℕ) (positive : 0 < ell) :
    letI : Nonempty fan.cones := hne.coe_sort
    letI := toricScheme_isNoetherian fan
    letI := toricScheme_isIntegral fan hne
    letI := toricPowerMap_finite fan regular ell positive
    (boundedCoherentToQuasicoherent fan.algebraicRealization).obj
      (toricDbPowerObject fan regular hne
        (invariantCartierDivisor fan hne.coe_sort regular b) ell positive) ≅
    (quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
        (arrangementCartierCoefficient fan regular b)) := by
  letI : Nonempty fan.cones := hne.coe_sort
  letI := toricScheme_isNoetherian fan
  letI := toricScheme_isIntegral fan hne
  letI := toricPowerMap_finite fan regular ell positive
  let D := invariantCartierDivisor fan hne.coe_sort regular b
  let M : Coh fan.algebraicRealization :=
    ⟨toricPowerDivisorSheaf fan hne D ell,
      toricPowerDivisorSheaf_isFinitePresentation fan regular hne D ell positive⟩
  exact coherentSingleQuasicoherentIso fan.algebraicRealization M ≪≫
    (((quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategorySingleFunctor 0).app
      (arrangementCartierCoefficient fan regular b)).symm

end ToricPower

end
