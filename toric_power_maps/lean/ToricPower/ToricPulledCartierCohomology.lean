module

public import ToricPower.ToricPulledCartierCech
public import ToricPower.CechToricCohomology
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Cohomology of the literal pullback of a toric Cartier line

This theorem compares ordinary Zariski cohomology of two actual sheaves:
the Cartier line defined by composing local characters, and the literal
pullback along the actual toric scheme map. The comparison is obtained
from their natural isomorphism of ordinary Čech complexes, whose local
maps were proved compatible on every face. Neither fan need be complete,
and the scheme map need not be dominant.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe v
variable {N N' : Type} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}
namespace ToricCharacterAtlas

/-- All-degree cohomology comparison for the genuine sheaf pullback along
an arbitrary toric fan morphism. -/
def pullbackCohomologyIso (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (degree : ℕ) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    AddCommGrpCat.of (Cohomology
      ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf degree) ≅
    AddCommGrpCat.of (Cohomology
      ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf) degree) := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  letI := toricScheme_isNoetherian source
  letI := source.algebraicRealization_isSeparated
  letI := ((atlas.pullback mapping).cartierDivisor sourceNonempty).isInvertible_sheaf
  letI := (atlas.cartierDivisor targetNonempty).isInvertible_sheaf
  let charts := toricFiniteCechCharts source
  let opens := toricCechChartOpen source charts
  have cover := (toricCechChartOpen_covers source charts
    (toricFiniteCechCharts_surjective source)).iSup_eq_top
  have affine := toricCechChartOpen_isAffine source charts
  exact BondalThomsen.FiniteAffineCechAllDegreeComparison.cechSchemeCohomologyIso opens
      cover affine ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf degree ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
      (atlas.pullbackCechComplexIso sourceNonempty targetNonempty mapping charts) ≪≫
    (BondalThomsen.FiniteAffineCechAllDegreeComparison.cechSchemeCohomologyIso opens
      cover affine ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf) degree).symm

end ToricCharacterAtlas
end ToricPower
