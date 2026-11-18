module

public import ToricPower.ToricBoundaryAtlas
public import ToricPower.CartierBoundarySectionExtension

/-!
# Extending quasi-coherent sections from every smooth toric chart

The reduced invariant boundary of a chart is Cartier on a smooth toric
variety. Its explicit regular equations and finite pole clearing extend
an arbitrary quasi-coherent section as a map from an actual line bundle.
No completeness, global generation, or torsion-free hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Every actual local section is the image of a local basis of a global
Cartier line bundle. The map and the frame belong to the ordinary sheaf
category. -/
theorem toricSection_exists_cartier_extension (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (σ : fan.cones) (M : fan.algebraicRealization.Modules) [M.IsQuasicoherent]
    (s : Γ(M, (fan.affineToricChartι σ).opensRange)) :
    letI := toricSchemeIntegral fan nonempty
    ∃ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
      (frame : (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf).over
          (fan.affineToricChartι σ).opensRange ≅
        D.sheaf.over (fan.affineToricChartι σ).opensRange)
      (mapping : D.sheaf ⟶ M),
      frame.hom ≫ mapping.over (fan.affineToricChartι σ).opensRange =
        overSectionHom M (fan.affineToricChartι σ).opensRange s := by
  letI := toricSchemeIntegral fan nonempty
  let atlas := (toricChartBoundaryAtlas fan regular σ).cartierEquationAtlas nonempty
  letI : Finite atlas.Index := inferInstanceAs (Finite fan.cones)
  apply atlas.exists_cartier_section_extension
    (fun τ => isAffineOpen_opensRange (fan.affineToricChartι τ))
    (fun τ υ => ?_) σ (toricBoundaryRegularEquation fan regular σ)
    (toricBoundaryRegularEquation_basicOpen fan regular σ)
    (toricBoundaryRegularEquation_transition fan nonempty regular σ)
    (toricBoundaryRegularEquation_self fan regular σ) M s
  change IsAffineOpen
    ((fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι υ).opensRange)
  rw [← chart_opensRange_intersection fan τ υ]
  exact isAffineOpen_opensRange (fan.affineToricChartι (τ ⊓ υ))

end ToricPower

end
