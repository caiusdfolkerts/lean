module

public import ToricPower.DiagonalProductCharts
public import ToricPower.ArrangementInverseExteriorLabels

/-! # The original overlap maps over the coefficient field

The chart triangles determine the scalar structures of the overlap
and diagonal chart maps. These instances retain those actual maps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

instance reconstructionOverlapLeft_isOver :
    (fan.affineToricOverlapLeft σ τ).IsOver (Spec (.of ℂ)) := by
  rw [Scheme.Hom.isOver_iff,
    ← comp_over (fan.affineToricChartι σ) (Spec (.of ℂ)),
    ← Category.assoc, fan.affineToricOverlapLeft_comp_affineToricChartι, comp_over]

instance reconstructionOverlapRight_isOver :
    (fan.affineToricOverlapRight σ τ).IsOver (Spec (.of ℂ)) := by
  rw [Scheme.Hom.isOver_iff,
    ← comp_over (fan.affineToricChartι τ) (Spec (.of ℂ)),
    ← Category.assoc, fan.affineToricOverlapRight_comp_affineToricChartι, comp_over]

instance reconstructionDiagonalChart_isOver :
    (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))).IsOver
      (Spec (.of ℂ)) := by
  rw [Scheme.Hom.isOver_iff,
    ← comp_over (diagonalProductChartι fan basis rays σ τ) (Spec (.of ℂ)),
    ← Category.assoc, ← (diagonalProductChart_isPullback fan basis rays σ τ).w]
  change (fan.affineToricChartι (σ ⊓ τ) ≫ toricDiagonal fan) ≫ _ = _
  rw [Category.assoc, comp_over, comp_over]
  rfl

end ToricPower

end
