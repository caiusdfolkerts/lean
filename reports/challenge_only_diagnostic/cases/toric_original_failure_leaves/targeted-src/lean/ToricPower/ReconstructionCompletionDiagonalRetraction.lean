module

public import ToricPower.DiagonalPulledCellularInclusions
public import ToricPower.DiagonalTopQuotient
public import ToricPower.SchemeExternalSectionRetraction

/-! # The actual top-cell quotient after diagonal retraction

The coefficient comparison already used by the geometric augmentation
is the inverse of the specified exterior retraction followed by the
pullback of the original exterior coefficient map. No new quotient is
chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan

/-- The specified exterior retraction is invertible for the actual
quasicoherent first factor. Its map is retained literally. -/
def reconstructionDiagonalRetractionIso (M P : (X).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (toricDiagonal fan)).obj
      (schemeExteriorSheaf (toricDiagonalFirst fan) (toricDiagonalSecond fan) M P) ≅ M ⊗ P :=
  diagonalPullbackExternalIso fan M P

theorem reconstructionDiagonalRetractionIso_hom (M P : (X).Modules)
    [M.IsQuasicoherent] :
    (reconstructionDiagonalRetractionIso fan M P).hom =
      schemeExternalSectionRetractionMap (toricDiagonal fan)
        (toricDiagonalFirst fan) (toricDiagonalSecond fan)
        (pullback.diagonal_fst fan.algebraicRealizationStructureMap)
        (pullback.diagonal_snd fan.algebraicRealizationStructureMap) M P := by
  rfl

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "M" => diagonalExteriorDualDiagram fan nonempty regular basis rays
local notation "Pull" => Scheme.Modules.pullback (toricDiagonal fan)

local instance reconstructionDiagonalLeftQuasicoherent (c : C) :
    ((Q).obj c).IsQuasicoherent := by
  letI := toricSchemeIntegral fan nonempty
  letI := (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).isInvertible_sheaf
  change (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).sheaf.IsQuasicoherent
  infer_instance

/-- Each actual inverse coefficient comparison is the inverse of the
actual exterior retraction, followed by the pulled original coefficient. -/
@[reassoc]
theorem reconstructionDiagonalCoefficient_retraction (c : C)
    (H : (Y).Modules) (γ : (M).obj c ⟶ H) :
    (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app c ≫
        (Pull).map γ =
      (reconstructionDiagonalRetractionIso fan ((Q).obj c) ((R).obj c)).inv ≫
        (Pull).map
          ((diagonalExteriorCoefficientIso fan nonempty regular basis rays).inv.app c ≫ γ) := by
  simp only [diagonalPulledInverseCoefficientIso, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rfl

/-- In particular, the specified original top quotient has exactly
the coefficient map used by the arbitrary-section retraction square. -/
@[reassoc]
theorem reconstructionDiagonalTop_retraction (d : NormalizedCell A n) :
    (diagonalPulledInverseCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
        (Pull).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays d) =
      (reconstructionDiagonalRetractionIso fan ((Q).obj ⟨n,d⟩) ((R).obj ⟨n,d⟩)).inv ≫
        (Pull).map
          ((diagonalExteriorCoefficientIso fan nonempty regular basis rays).inv.app ⟨n,d⟩ ≫
            diagonalInverseCellTopQuotient fan nonempty regular basis rays d) :=
  reconstructionDiagonalCoefficient_retraction fan nonempty regular basis rays ⟨n,d⟩ _ _

end ToricPower

end
