module

public import ToricPower.DiagonalGlobalAugmentation
public import ToricPower.SchemePullbackTensorQuasicoherent
public import ToricPower.CovariantRepresentableEvaluation

/-!
# Canonical restriction of the actual exterior kernel to the diagonal

The existing exterior-product comparison is invertible as soon as one
factor is quasicoherent. Its forward map is the original oplax tensor
comparison followed by the original pullback composition isomorphisms.
The diagram statement keeps the actual factor maps on every incidence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan

/-- This is invertibility of the specified exterior restriction map,
not merely an unspecified isomorphism of its endpoints. -/
instance diagonalPullbackExternalMap_isIso (M P : (X).Modules) [M.IsQuasicoherent] :
    IsIso (diagonalPullbackExternalMap fan M P) := by
  letI := pullbackTensorComparisonLeft_isIso (toricDiagonal fan)
    ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj M)
    ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj P)
  unfold diagonalPullbackExternalMap
  infer_instance

def diagonalPullbackExternalIso (M P : (X).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (toricDiagonal fan)).obj
      ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj M ⊗
        (Scheme.Modules.pullback (toricDiagonalSecond fan)).obj P) ≅ M ⊗ P :=
  asIso (diagonalPullbackExternalMap fan M P)

variable {C : Type} [Category.{0} C]
  (Q R : C ⥤ fan.algebraicRealization.Modules)

/-- The genuine exterior-product label diagram, with both original
pullback maps and no independently postulated differential. -/
def exteriorLabelDiagram : C ⥤ (Y).Modules :=
  Cellular.covariantTensorDiagram
    (Q ⋙ Scheme.Modules.pullback (toricDiagonalFirst fan))
    (R ⋙ Scheme.Modules.pullback (toricDiagonalSecond fan))

/-- The canonical exterior restriction is natural in every incidence,
including its actual Cartier characters. -/
def diagonalPullbackExteriorDiagramIso
    (quasicoherent : ∀ c : C, (Q.obj c).IsQuasicoherent) :
    exteriorLabelDiagram fan Q R ⋙ Scheme.Modules.pullback (toricDiagonal fan) ≅
      Cellular.covariantTensorDiagram Q R :=
  NatIso.ofComponents (fun c => by
    letI := quasicoherent c
    exact diagonalPullbackExternalIso fan (Q.obj c) (R.obj c))
    (fun f => diagonalPullbackExternalMap_natural fan (Q.map f) (R.map f))

end ToricPower

end
