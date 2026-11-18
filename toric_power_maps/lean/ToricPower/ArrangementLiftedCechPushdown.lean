module

public import ToricPower.ArrangementLiftedCech
public import ToricPower.ArrangementLinearCech
public import ToricPower.CechLinearCharacterSum
public import ToricPower.WeightedIncidenceComplexPushdown

/-!
# The actual compact-lift diagram pushes down to the actual Čech diagram

The lift uses every weight, indexed by the negative of the chosen basis.
Direct image sums all lifts of a cell. Its coordinate comparison is the
literal monomial expansion of the actual Laurent section, and the proof
of naturality checks every translated incidence. Thus no loop or
generisation action is inferred merely from matching stalk dimensions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

/-- The weight convention determined by actual inverse-label monomials. -/
def arrangementNegativeCharacterEquiv : (Fin n → ℤ) ≃ (N →+ ℤ) :=
  basis.equivFun.symm.toEquiv.trans (Equiv.neg _)

variable {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (b : fan.Ray → ℤ)

/-- Direct image of the complete complex-valued lift. -/
def arrangementLiftedCechPushdown : C ⥤ CochainComplex (ModuleCat ℂ) ℕ :=
  weightedComplexPushdown A ℂ (arrangementLiftedCech fan basis rays charts b)

/-- The full fiber sum is the actual Laurent complex at this cell. -/
def arrangementLiftedCechPushdownCellIso (c : C) :
    (arrangementLiftedCechPushdown fan basis rays charts b).obj c ≅
      toricCechLaurentLinearComplex fan charts
        (b - diagonalRightCoefficients fan basis rays c.2) :=
  weightedComplexPushdownCellIso A ℂ
      (arrangementLiftedCech fan basis rays charts b) c ≪≫
    toricCechLinearCharacterSumIso fan charts
      (b - diagonalRightCoefficients fan basis rays c.2)
      (arrangementNegativeCharacterEquiv basis)

/-- On one lift the comparison inserts exactly its actual character. -/
theorem arrangementLiftedCechPushdownCellIso_single (c : C) (q : ℕ)
    (m : Fin n → ℤ)
    (x : ((arrangementLiftedCech fan basis rays charts b).obj (c,m)).X q) :
    (arrangementLiftedCechPushdownCellIso fan basis rays charts b c).hom.f q
        (DFinsupp.single m x) =
      toricCechLinearWeightDegreeInclusion fan charts
        (b - diagonalRightCoefficients fan basis rays c.2)
        (-(basis.equivFun.symm m)) q x := by
  change (toricCechLinearCharacterSumMap fan charts
      (b - diagonalRightCoefficients fan basis rays c.2)
      (arrangementNegativeCharacterEquiv basis)).f q (DFinsupp.single m x) = _
  exact toricCechLinearCharacterSumMap_single fan charts
    (b - diagonalRightCoefficients fan basis rays c.2)
    (arrangementNegativeCharacterEquiv basis) q m x

variable [Nonempty fan.cones] (regular : fan.IsRegular)

/-- Every translated incidence is checked on every scalar monomial. -/
theorem arrangementLiftedCechPushdownCellIso_naturality {c d : C} (f : c ⟶ d) :
    (arrangementLiftedCechPushdown fan basis rays charts b).map f ≫
        (arrangementLiftedCechPushdownCellIso fan basis rays charts b d).hom =
      (arrangementLiftedCechPushdownCellIso fan basis rays charts b c).hom ≫
        (arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts b).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply DFinsupp.lhom_ext
  intro m x
  change (arrangementLiftedCechPushdownCellIso fan basis rays charts b d).hom.f q
      (((weightedComplexPushdown A ℂ (arrangementLiftedCech fan basis rays charts b)).map
        f).f q (DFinsupp.single m x)) =
    ((arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts b).map f).f q
      ((arrangementLiftedCechPushdownCellIso fan basis rays charts b c).hom.f q
        (DFinsupp.single m x))
  rw [weightedComplexPushdown_map_single,
    arrangementLiftedCechPushdownCellIso_single,
    arrangementLiftedCechPushdownCellIso_single]
  funext tuple
  apply Subtype.ext
  rw [arrangementDifferenceLinearLaurentDiagram_map_coefficients,
    toricCechLinearWeightDegreeInclusion_val,
    toricCechLinearWeightDegreeInclusion_val, Finsupp.mapDomain_single]
  have weight : -(basis.equivFun.symm (m + f.val)) =
      -(basis.equivFun.symm f.val) + -(basis.equivFun.symm m) := by
    rw [map_add, neg_add_rev]
  change Finsupp.single (-(basis.equivFun.symm (m + f.val))) (x tuple).val =
    Finsupp.single (-(basis.equivFun.symm f.val) + -(basis.equivFun.symm m)) (x tuple).val
  exact congrArg (fun a => Finsupp.single a (x tuple).val) weight

/-- Full scalar-linear natural comparison, including every differential,
every incidence translation, and every character. -/
def arrangementLiftedCechPushdownLaurentIso :
    arrangementLiftedCechPushdown fan basis rays charts b ≅
      arrangementDifferenceLinearLaurentDiagram fan regular basis rays charts b :=
  NatIso.ofComponents
    (arrangementLiftedCechPushdownCellIso fan basis rays charts b)
    (fun f => arrangementLiftedCechPushdownCellIso_naturality
      fan basis rays charts b regular f)

/-- The unrestricted weighted lift pushes down to the actual sheaf Čech
diagram, with its specified complex scalar action. -/
def arrangementLiftedCechPushdownActualIso :
    arrangementLiftedCechPushdown fan basis rays charts b ≅
      arrangementDifferenceLinearCechDiagram fan regular basis rays charts b :=
  arrangementLiftedCechPushdownLaurentIso fan basis rays charts b regular ≪≫
    (arrangementDifferenceLinearCechLaurentIso fan regular basis rays charts b).symm

end ToricPower

end
