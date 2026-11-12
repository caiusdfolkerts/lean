module

public import ToricPower.ArrangementNormalizedSources
public import ToricPower.ArrangementCartierSources
public import ToricPower.CellularHomAdjunction
public import ToricPower.QuasicoherentCartierLinear

/-!
# Boundary normalization of the actual source and Hom diagrams

Cartier multiplication identifies the normalized source with the
original source tensored by the boundary line. The actual tensor
adjunction then identifies their full Hom diagrams, naturally in all
source incidences and arbitrary quasicoherent coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
local notation "D" => invariantCartierDivisor fan nonempty regular (fun _ => 1)
local notation "P" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "PN" => normalizedCartierQuasicoherentSources fan nonempty regular basis rays

/-- Actual rational Cartier multiplication identifies the entire
normalized source diagram with the boundary tensor of the original. -/
def normalizedCartierBoundaryTensorIso :
    letI := toricSchemeIntegral fan nonempty
    P ⋙ (quasicoherentCartierTensorEquivalence D).functor ≅ PN := by
  letI := toricSchemeIntegral fan nonempty
  exact NatIso.ofComponents (fun c => ObjectProperty.isoMk _
    (invariantCartierTensorIso fan nonempty regular (fun _ => 1)
      (diagonalRightCoefficients fan basis rays c.unop.2))) (by
        intro c d f
        apply ObjectProperty.hom_ext
        change ((D).sheaf ◁ toricCartierMonomialMap fan nonempty regular
            (diagonalRightCoefficients fan basis rays c.unop.2)
            (diagonalRightCoefficients fan basis rays d.unop.2)
            (-basis.equivFun.symm f.unop.val) _) ≫
            (invariantCartierTensorIso fan nonempty regular (fun _ => 1)
              (diagonalRightCoefficients fan basis rays d.unop.2)).hom =
          (invariantCartierTensorIso fan nonempty regular (fun _ => 1)
              (diagonalRightCoefficients fan basis rays c.unop.2)).hom ≫
            toricCartierMonomialMap fan nonempty regular _ _
              (-basis.equivFun.symm f.unop.val) _
        simpa only [toricCartierMonomialMap_id, zero_add, id_tensorHom] using
          toricCartierMonomialMap_tensor fan nonempty regular
            (fun _ => 1) (fun _ => 1)
            (diagonalRightCoefficients fan basis rays c.unop.2)
            (diagonalRightCoefficients fan basis rays d.unop.2)
            0 (-basis.equivFun.symm f.unop.val) (by intro ρ; simp)
            (arrangementRightCharacter_regular fan basis rays f.unop))

/-- The original tensor adjunction gives the exact normalized Hom
diagram, with both naturalities retained. -/
def normalizedCartierHomBoundaryIso :
    letI := toricSchemeIntegral fan nonempty
    Cellular.homDiagram ℂ PN ≅
      (quasicoherentCartierTensorEquivalence D).inverse ⋙ Cellular.homDiagram ℂ P := by
  letI := toricSchemeIntegral fan nonempty
  exact Cellular.homDiagramPrecomposeIso ℂ
      (normalizedCartierBoundaryTensorIso fan nonempty regular basis rays).symm ≪≫
    Cellular.homDiagramAdjunctionIso ℂ P
      (quasicoherentCartierTensorEquivalence D).toAdjunction

end ToricPower

end
