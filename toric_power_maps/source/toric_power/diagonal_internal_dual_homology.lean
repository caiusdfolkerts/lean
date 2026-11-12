module

public import ToricPower.DiagonalInternalDual
public import ToricPower.DualDiagonalToricSheafResolution
public import ToricPower.SheafQuasiIsoLocal

/-!
# Global concentration of the actual internal-dual diagonal

The explicit affine dual calculation is transported through the actual
pullback comparison and detected on the genuine product open cover.
Consequently the whole sheaf internal-dual complex has homology only in
the ambient lattice rank. The resulting augmentation is the canonical
quotient to that actual homology sheaf.

The local top-homology coordinates retain the independently defined
boundary-weight module. Identification of its transition maps with the
boundary line on the diagonal is a further, separate comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Y" => toricDiagonalProduct fan
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays

/-- Every actual global internal-dual homology sheaf away from ambient
rank is zero, with no completeness or projectivity assumption. -/
theorem diagonalGlobalInternalDual_isZero_homology
    (q : ℕ) (different : q ≠ n) : IsZero ((K).homology q) := by
  apply (Scheme.Modules.isZero_iff_pullback_openCover
    (diagonalCoordinateOpenCover fan basis rays) ((K).homology q)).mpr
  intro p
  let P := Scheme.Modules.pullback (diagonalProductChartι fan basis rays p.1 p.2)
  have localZero : IsZero
      (((P.mapHomologicalComplex (.up ℕ)).obj K).homology q) :=
    ((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapIso
      (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays p.1 p.2)).isZero_iff.mpr
        (toricDiagonalInternalDual_isZero_homology fan regular basis rays p.1 p.2 q different)
  exact (((K).sc q).mapHomologyIso P).isZero_iff.mp localZero

/-- The actual finite dual complex has no term beyond ambient rank. -/
theorem diagonalGlobalInternalDual_isZero_X_above
    (q : ℕ) (above : n < q) : IsZero ((K).X q) :=
  (internalDual (Y).Modules).map_isZero
    (diagonalGlobalSheafTerm_isZero_of_dim_lt fan nonempty regular basis rays q above).op

theorem diagonalGlobalInternalDual_top_differential : (K).d n (n+1) = 0 :=
  (diagonalGlobalInternalDual_isZero_X_above fan nonempty regular basis rays
    (n+1) (Nat.lt_succ_self n)).eq_of_tgt _ _

/-- The actual top quotient, without replacing its homology sheaf by
an asserted or locally specified target. -/
def diagonalGlobalInternalDualTopAugmentation :
    K ⟶ (HomologicalComplex.single (Y).Modules (.up ℕ) n).obj ((K).homology n) :=
  augmentationOfTopHomology K n
    (diagonalGlobalInternalDual_top_differential fan nonempty regular basis rays) (𝟙 _)

/-- The actual canonical global augmentation is a quasi-isomorphism. -/
theorem diagonalGlobalInternalDualTopAugmentation_quasiIso :
    QuasiIso (diagonalGlobalInternalDualTopAugmentation fan nonempty regular basis rays) :=
  augmentationOfTopHomology_quasiIso K n
    (diagonalGlobalInternalDual_top_differential fan nonempty regular basis rays)
    (Iso.refl _) (diagonalGlobalInternalDual_isZero_homology fan nonempty regular basis rays)

variable (σ τ : fan.cones)

local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)

/-- The local coordinates of the genuine global top homology sheaf,
with the full product-ring action on the boundary module. -/
def diagonalGlobalInternalDualTopChartIso :
    (P).obj ((K).homology n) ≅ tilde (dualDiagonalBoundaryModule A S T ℂ) :=
  (((K).sc n).mapHomologyIso P).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) n).mapIso
      (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ) ≪≫
        toricDiagonalInternalDualTopIso fan regular basis rays σ τ

end ToricPower
