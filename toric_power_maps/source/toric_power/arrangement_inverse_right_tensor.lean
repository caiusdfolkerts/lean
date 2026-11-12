module

public import ToricPower.ArrangementRightCoefficientFunctor
public import ToricPower.CartierSourceInternalHom

/-!
# Internal Hom of the actual inverse-right labels

The source-natural inverse Cartier tensor comparison identifies
`Hom(R(c), J)` with the original right label `P₀(c) ⊗ J`, for arbitrary
module-sheaf coefficients `J`. Both sides retain the literal negative
incidence characters. Double negation is performed in the small
coefficient category before actual sheaf realization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightCartierDiagram fan nonempty regular basis rays

/-- The full internal-Hom comparison, natural in every source and
arbitrary coefficient sheaf. -/
def arrangementInverseRightInternalHomIso :
    (R).op ⋙ MonoidalClosed.internalHom ≅
      P₀ ⋙ tensoringLeft (X).Modules := by
  letI := toricSchemeIntegral fan nonempty
  let D := arrangementInverseRightCoefficientDiagram fan basis rays
  let source : D ⋙ ToricMonomial.sources fan nonempty regular ⋙
      cartierSourcesQuasicoherent X ⋙ quasicoherentInclusion X ≅ R :=
    arrangementInverseRightRealizationIso fan basis rays nonempty regular
  let sourceHom := Functor.isoWhiskerRight (NatIso.op source) MonoidalClosed.internalHom
  let inverse := Functor.isoWhiskerLeft (D ⋙ ToricMonomial.sources fan nonempty regular).op
    (cartierSourcesInverseInternalHomIso X)
  let monomial := Functor.isoWhiskerLeft D.op (ToricMonomial.inverseTensorIso fan nonempty regular)
  let coefficients := Functor.isoWhiskerRight
    (arrangementInverseRightDualCoefficientIso fan basis rays)
    (ToricMonomial.realization fan nonempty regular ⋙ tensoringLeft (X).Modules)
  let realization := Functor.isoWhiskerRight
    (arrangementRightCoefficientRealizationIso fan basis rays nonempty regular)
    (tensoringLeft (X).Modules)
  exact sourceHom ≪≫ inverse.symm ≪≫ monomial ≪≫ coefficients ≪≫ realization

/-- In particular, the actual target of the represented transpose is
precisely the original right label tensored with the genuine top line. -/
def arrangementInverseRightInternalHomAtIso (J : (X).Modules) :
    (R).op ⋙ MonoidalClosed.internalHom.flip.obj J ≅
      P₀ ⋙ (tensoringRight (X).Modules).obj J :=
  Functor.isoWhiskerRight
    (arrangementInverseRightInternalHomIso fan basis rays nonempty regular)
    ((evaluation (X).Modules (X).Modules).obj J)

end ToricPower

end
