module

public import ToricPower.ToricPulledCartierSections
public import ToricPower.SheafSectionOpenTransport
public import ToricPower.CechSectionComparison
public import ToricPower.CechToricCover

/-!
# The Čech complex of an actual toric Cartier pullback

For an arbitrary fan morphism, the line sheaf defined by pulling back
local equation characters has the same full ordinary Čech complex as the
literal module-sheaf pullback. The comparison uses actual local frames,
actual face maps, and the actual chart intersections. No dominance or
function-field map is assumed, so subtorus inclusions are covered.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TauCeti.Toric Opposite
open BondalThomsen.FiniteAffineCechHigherComparison
namespace ToricPower
universe v
variable {N N' : Type} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}
namespace ToricCharacterAtlas

variable (atlas : ToricCharacterAtlas target)
  (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
  (mapping : FanHom source target) {Index : Type} (charts : Index → source.cones)

/-- The comparison on an actual finite intersection of toric charts. -/
def pullbackCechCoefficientIso (degree : ℕ) (tuple : Fin (degree + 1) → Index) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    cechSectionCoefficient (toricCechChartOpen source charts)
      ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf degree tuple ≅
    cechSectionCoefficient (toricCechChartOpen source charts)
      ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf) degree tuple := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  exact moduleSectionComparisonTransport
    (toricCechIntersection_eq_chart source charts degree tuple)
    (atlas.pullbackChartSectionsIso sourceNonempty targetNonempty mapping
      (toricCechCone source charts degree tuple))

/-- The finite-intersection comparison commutes with every actual tuple
selection and hence with every actual Čech differential. -/
theorem pullbackCechCoefficientIso_selection {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1)) (tuple : Fin (next + 1) → Index) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    let original := ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf
    let pulled := (Scheme.Modules.pullback mapping.algebraicMap).obj
      (atlas.cartierDivisor targetNonempty).sheaf
    (atlas.pullbackCechCoefficientIso sourceNonempty targetNonempty mapping charts
      degree (tuple ∘ selection)).hom ≫
      cechSectionRestriction (toricCechChartOpen source charts) pulled selection tuple =
    cechSectionRestriction (toricCechChartOpen source charts) original selection tuple ≫
      (atlas.pullbackCechCoefficientIso sourceNonempty targetNonempty mapping charts next tuple).hom := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  let actual := (Limits.Pi.lift (fun column : Fin (degree + 1) =>
    Limits.Pi.π (toricCechChartOpen source charts ∘ tuple) (selection column))).le
  let included := toricCechCone_le_selection source charts selection tuple
  exact moduleSectionComparisonTransport_restrict
    (toricCechIntersection_eq_chart source charts degree (tuple ∘ selection))
    (toricCechIntersection_eq_chart source charts next tuple) actual
    (toricChart_opensRange_mono source included)
    (atlas.pullbackChartSectionsIso sourceNonempty targetNonempty mapping
      (toricCechCone source charts degree (tuple ∘ selection)))
    (atlas.pullbackChartSectionsIso sourceNonempty targetNonempty mapping
      (toricCechCone source charts next tuple))
    (atlas.pullbackChartSectionsIso_restrict sourceNonempty targetNonempty mapping
      (toricCechCone source charts degree (tuple ∘ selection))
      (toricCechCone source charts next tuple) included)

/-- Isomorphism of the complete actual Čech complexes. -/
def pullbackCechComplexIso :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    schemeCechComplex (toricCechChartOpen source charts)
      ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf ≅
    schemeCechComplex (toricCechChartOpen source charts)
      ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf) := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  exact cechSectionComplexIso (toricCechChartOpen source charts)
    (atlas.pullbackCechCoefficientIso sourceNonempty targetNonempty mapping charts)
    (atlas.pullbackCechCoefficientIso_selection sourceNonempty targetNonempty mapping charts)

end ToricCharacterAtlas
end ToricPower
