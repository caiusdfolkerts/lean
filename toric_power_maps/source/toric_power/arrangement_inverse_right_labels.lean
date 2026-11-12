module

public import ToricPower.ArrangementCochainLabels

/-! # Actual inverse-right Cartier labels

These are the unchanged inverse coefficients and original translated
incidence maps. They are independent of the dual-diagonal complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays

/-- The inverse of the literal right Cartier coefficient. -/
def arrangementDualRightCoefficients (c : C) : fan.Ray → ℤ :=
  -diagonalRightCoefficients fan basis rays c.2

/-- The covariant inverse-right diagram uses the actual negative
character on each original translated incidence. -/
def arrangementDualRightCartierDiagram : C ⥤ (X).Modules where
  obj c := by
    letI := toricSchemeIntegral fan nonempty
    exact (invariantCartierDivisor fan nonempty regular
      (arrangementDualRightCoefficients fan basis rays c)).sheaf
  map {c d} f := by
    letI := toricSchemeIntegral fan nonempty
    exact toricCartierMonomialMap fan nonempty regular
      (arrangementDualRightCoefficients fan basis rays c)
      (arrangementDualRightCoefficients fan basis rays d)
      (-(basis.equivFun.symm f.val)) (by
        intro ρ
        have h := (diagonalEntryRegular_of_incidence fan basis rays f).2 ρ
        change 0 ≤ -(diagonalRightCoefficients fan basis rays d.2 ρ) -
          -(diagonalRightCoefficients fan basis rays c.2 ρ) +
            (-(basis.equivFun.symm f.val)) (fanRayPrimitiveGenerator fan ρ)
        simp only [AddMonoidHom.neg_apply]
        omega)
  map_id c := by
    letI := toricSchemeIntegral fan nonempty
    simp only [incidence_id_val, map_zero, neg_zero, toricCartierMonomialMap_id]
  map_comp f g := by
    letI := toricSchemeIntegral fan nonempty
    rw [toricCartierMonomialMap_comp]
    simp only [incidence_comp_val, map_add, neg_add]

end ToricPower

end
