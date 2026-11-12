module

public import ToricPower.ArrangementCartierSources
public import ToricPower.CechToricLinearMonomial

/-!
# The whole arrangement Čech diagram with its actual complex scalars

Inverse Cartier tensoring produces the literal difference coefficients.
The natural isomorphism below retains all actual incidence maps at the
level of complete complex-linear cochain complexes. On full Laurent
coordinates an incidence of translation `a` acts by `m ↦ m-a`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  {Index : Type} (charts : Index → fan.cones)

local notation "C" => IncidenceObject (fanArrangementMatrix fan basis rays)

/-- Ordinary complex-linear Čech complexes of the actual difference sheaves. -/
def arrangementDifferenceLinearCechDiagram (d : fan.Ray → ℤ) :
    C ⥤ CochainComplex (ModuleCat ℂ) ℕ :=
  arrangementDifferenceCoefficientDiagram fan regular basis rays d ⋙
    schemeLinearCechComplexFunctor ℂ fan.algebraicRealization (toricCechChartOpen fan charts)

/-- Full-character Laurent coordinates for every actual label. -/
def arrangementDifferenceLinearLaurentDiagram (d : fan.Ray → ℤ) :
    C ⥤ CochainComplex (ModuleCat ℂ) ℕ :=
  conjugateFunctorObjects
    (arrangementDifferenceLinearCechDiagram fan regular basis rays charts d)
    (fun c => toricCechLaurentLinearComplex fan charts
      (d - diagonalRightCoefficients fan basis rays c.2))
    (fun c => toricCechLinearComplexIso fan charts
      (d - diagonalRightCoefficients fan basis rays c.2) nonempty regular)

/-- A genuine natural isomorphism of the full complex-linear diagrams. -/
def arrangementDifferenceLinearCechLaurentIso (d : fan.Ray → ℤ) :
    arrangementDifferenceLinearCechDiagram fan regular basis rays charts d ≅
      arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts d :=
  conjugateFunctorObjectsIso _ _ _

/-- Every actual incidence shifts the complete character lattice by its
negative translation and retains every complex coefficient. -/
theorem arrangementDifferenceLinearLaurentDiagram_map_coefficients (d : fan.Ray → ℤ)
    {c e : C} (f : c ⟶ e) (q : ℕ) (tuple : Fin (q+1) → Index)
    (p : ((arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts d).obj c).X q) :
    ((((arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts d).map f).f
      q p) tuple).val =
      Finsupp.mapDomain (fun m : N →+ ℤ => -(basis.equivFun.symm f.val) + m) (p tuple).val :=
  toricCechLaurentLinearMonomialMap_coefficients fan charts nonempty regular
    (d - diagonalRightCoefficients fan basis rays c.2)
    (d - diagonalRightCoefficients fan basis rays e.2)
    (-(basis.equivFun.symm f.val))
    (toricMonomialNonnegative_inverseTwist fan
      (diagonalRightCoefficients fan basis rays e.2)
      (diagonalRightCoefficients fan basis rays c.2) d
      (-(basis.equivFun.symm f.val)) (arrangementRightCharacter_regular fan basis rays f)) q tuple p

end ToricPower
