module

public import ToricPower.ArrangementDerivedCech
public import ToricPower.ArrangementNormalizedAdjunction
public import ToricPower.ArrangementLiftedCechSupport

/-!
# The full compact lift of the normalized Hom diagram of a Cartier line

The actual inverse boundary tensor sends `O(b)` to `O(b−1)`.
The previously constructed all-character Čech lift therefore represents
the normalized right adjoint with the prescribed shift by the lattice
rank. Completeness proves compactness of its cohomological carrier.
Neither the character family nor its Čech cochains are truncated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "W" => WeightedIncidenceObject A
local notation "E" => quasicoherentCartierTensorEquivalence (arrangementBoundaryDivisor fan regular)
local notation "B" => arrangementToricDerivedHom fan nonempty regular basis rays
local notation "charts" => toricMeetChartEquiv fan

local instance normalizedLift_integral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance normalizedLift_chartIndexFintype : Fintype (ToricMeetChartIndex fan) := Fintype.ofFinite _
local instance normalizedLift_derivedQCoh : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance normalizedLift_derivedCells : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- This is the actual rational-section multiplication isomorphism. -/
def arrangementBoundaryInverseLineIso (b : fan.Ray → ℤ) :
    (E).inverse.obj (arrangementCartierCoefficient fan regular b) ≅
      arrangementCartierCoefficient fan regular (b - (fun _ => 1)) :=
  (SheafOfModules.isQuasicoherent (X).ringCatSheaf).fullyFaithfulι.preimageIso
    (invariantInverseTensorIso fan nonempty regular (fun _ => 1) b)

/-- The literal full weighted lift, with the boundary coefficient
included and every integral character retained. -/
def arrangementNormalizedLiftedCech (b : fan.Ray → ℤ) :
    W ⥤ CochainComplex (ModuleCat ℂ) ℕ :=
  arrangementLiftedCech fan basis rays charts (b - (fun _ => 1))

/-- The genuine normalized right adjoint is the direct image of the
full lift, with exactly the paper's dimension shift. -/
def arrangementNormalizedRHomWeightedPushdownIso (b : fan.Ray → ℤ) :
    (arrangementNormalizedDerivedHom fan regular basis rays).obj
        ((DerivedCategory.singleFunctor Q 0).obj (arrangementCartierCoefficient fan regular b)) ≅
      (DerivedCategory.Q.obj (complexDiagramTranspose
        (arrangementLiftedCechPushdown fan basis rays charts (b - (fun _ => 1)) ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))))⟦(n : ℤ)⟧ := by
  let G := (E).inverse.mapDerivedCategory ⋙ B
  let M := arrangementCartierCoefficient fan regular b
  let e : G.obj ((DerivedCategory.singleFunctor Q 0).obj M) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (arrangementLiftedCechPushdown fan basis rays charts (b - (fun _ => 1)) ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))) :=
    (B).mapIso (((E).inverse.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (B).mapIso ((DerivedCategory.singleFunctor Q 0).mapIso
        (arrangementBoundaryInverseLineIso fan regular b)) ≪≫
      arrangementRHomAffineWeightedPushdownIso fan regular basis rays (b - (fun _ => 1))
  change G.obj (((DerivedCategory.singleFunctor Q 0).obj M)⟦-(-(n : ℤ))⟧) ≅ _
  rw [neg_neg]
  exact (G.commShiftIso (n : ℤ)).app ((DerivedCategory.singleFunctor Q 0).obj M) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso e

include regular in
/-- All nonzero cell/character homologies of the normalized lift lie
in a finite set, simultaneously in all Čech degrees. -/
theorem arrangementNormalizedLiftedSupport_finite
    (complete : fan.IsComplete) (b : fan.Ray → ℤ) :
    (arrangementLiftedCechSupport fan basis rays charts (b - (fun _ => 1))).Finite :=
  arrangementLiftedCechSupport_finite fan basis rays charts (charts).surjective regular complete
    ((charts).symm (Classical.choice nonempty)) (b - (fun _ => 1))

include regular in
/-- The geometric carrier is the union of the actual translated closed
cells, and is compact by the full all-character cohomology theorem. -/
theorem arrangementNormalizedLiftedCarrier_isCompact
    (complete : fan.IsComplete) (b : fan.Ray → ℤ) :
    IsCompact (arrangementLiftedCechCompactCarrier fan basis rays charts (b - (fun _ => 1))) :=
  arrangementLiftedCechCompactCarrier_isCompact fan basis rays charts (charts).surjective
    regular complete ((charts).symm (Classical.choice nonempty)) (b - (fun _ => 1))

end ToricPower

end
