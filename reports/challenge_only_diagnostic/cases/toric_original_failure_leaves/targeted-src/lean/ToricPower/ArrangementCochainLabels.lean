module

public import ToricPower.ArrangementCartierDiagram
public import ToricPower.CellularCovariantLabels
public import ToricPower.DivisorWeightAdditive

/-!
# The actual Cartier labels in cellular realization

The covariant label at a cell is the Cartier sheaf with coefficients
`ceil(-A x)`. An incidence with translation `a` acts by the actual rational
character `χ^a`. These are the inverse Cartier labels of the reflected
factor of the diagonal complex.

Inserting this genuine sheaf-valued functor into the finite cellular
construction defines `A_cell`. The top-class comparison and diagonal
reconstruction are separate theorems, not hypotheses of the construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

/-- The literal coefficients of `Q(x)=L(-x)⁻¹`, including all walls. -/
def arrangementDualLeftCoefficients (c : C) : fan.Ray → ℤ :=
  -diagonalLeftCoefficients fan basis rays c.2

@[simp]
theorem arrangementDualLeftCoefficients_apply (c : C) (ρ : fan.Ray) :
    arrangementDualLeftCoefficients fan basis rays c ρ =
      reflectedCeiling A c.2.val (rays.symm ρ) := by
  simp only [arrangementDualLeftCoefficients, Pi.neg_apply, diagonalLeftCoefficients, neg_neg]

/-- The covariant Cartier label is a genuine invariant Cartier sheaf. -/
def arrangementDualLeftSheaf (c : C) : fan.algebraicRealization.Modules :=
  letI := toricSchemeIntegral fan nonempty
  (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).sheaf

/-- This coefficient construction is the actual inverse Cartier sheaf
of the reflected diagonal label, by proved divisor additivity. -/
def arrangementDualLeftInverseIso (c : C) :
    letI := toricSchemeIntegral fan nonempty
    arrangementDualLeftSheaf fan nonempty regular basis rays c ≅
      (-(invariantCartierDivisor fan nonempty regular
        (diagonalLeftCoefficients fan basis rays c.2))).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
    (invariantCartierDivisor_neg fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c.2)))

/-- Every incidence acts by its actual positive character. Both
functor laws follow from multiplication in the rational-function sheaf. -/
def arrangementDualLeftCartierDiagram : C ⥤ fan.algebraicRealization.Modules where
  obj := arrangementDualLeftSheaf fan nonempty regular basis rays
  map {c d} f := by
    letI := toricSchemeIntegral fan nonempty
    exact toricCartierMonomialMap fan nonempty regular
      (arrangementDualLeftCoefficients fan basis rays c)
      (arrangementDualLeftCoefficients fan basis rays d)
      (basis.equivFun.symm f.val) (by
        intro ρ
        have h := (diagonalEntryRegular_of_incidence fan basis rays f).1 ρ
        change 0 ≤ -(diagonalLeftCoefficients fan basis rays d.2 ρ) -
          -(diagonalLeftCoefficients fan basis rays c.2 ρ) +
          basis.equivFun.symm f.val (fanRayPrimitiveGenerator fan ρ)
        omega)
  map_id c := by
    letI := toricSchemeIntegral fan nonempty
    simp only [incidence_id_val, map_zero, toricCartierMonomialMap_id]
    rfl
  map_comp f g := by
    letI := toricSchemeIntegral fan nonempty
    rw [toricCartierMonomialMap_comp]
    simp only [incidence_comp_val, map_add]

/-- The actual finite complex of Cartier sheaves and vector copowers
attached to an arbitrary covariant cellular diagram. -/
def arrangementCellularSheafRealization :
    (C ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex fan.algebraicRealization.Modules ℕ := by
  letI : HasFiniteBiproducts fan.algebraicRealization.Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact arrangementCellularRealization A ℂ
    (arrangementDualLeftCartierDiagram fan nonempty regular basis rays)

end ToricPower
