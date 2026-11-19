module

public import ToricPower.ArrangementNormalizedBranchDetection
public import ToricPower.FanUniformShrinking
public import ToricPower.MaximalSupportFanNormal
public import ToricPower.ArrangementShrunkShiftedDetection
public import ToricPower.ClosedScalarShiftedRestriction

/-!
# Uniform detection from the actual affine-slice scalar tests

The tests are chosen once on the finite set of eligible normalized cells.
A single threshold then works for every larger integer and every
unbounded source satisfying the original fan's local Morse condition.
The tests and the Morse condition are explicit mathematical premises in
this assembly lemma; their geometric verification is separate.
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

local notation "A" => fanArrangementMatrix fan basis rays

local instance uniformDetectionDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance uniformDetectionDerivedScalar :
    HasDerivedCategory.{1} (ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
local instance uniformDetectionDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance uniformDetectionDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The original closed affine-plane scalar test on the full Cartier
lift, with no selected finite set of characters replacing that lift. -/
def NormalizedScalarSliceTest (b : fan.Ray → ℤ)
    (c : NormalCoveredNormalizedCell fan regular basis rays) (m : Fin n → ℤ) : Prop :=
  ∃ q : ℤ, ∃ f :
    (Cellular.closedConstantFunctor ℂ
      (universalAffineSliceSupport A (normalizedUniversalCell A c.val).2.val.2 m)
      (universalAffineSliceSupport_downward A (normalizedUniversalCell A c.val).2.val.2 m)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} ℂ) 0).obj (ModuleCat.of ℂ ℂ)) ⟶
      (DerivedCategory.Q.obj (normalizedUniversalLiftComplex fan basis rays b))⟦q⟧, f ≠ 0

/-- A common threshold works for every later integer, independently of
the unbounded source and the degree of its nonzero stalk. -/
theorem eventual_diagram_detection_of_slice_tests
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (tests : ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
      ∃ m : Fin n → ℤ, NormalizedScalarSliceTest fan regular basis rays b c m) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ ell : ℕ, threshold ≤ ell →
      ∀ E : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ,
        ¬ E.Acyclic →
        HasFanLocalMorseSupport fan regular basis rays (universalPeriodicComplex A ℂ E) →
        ∃ positive : 0 < ell, ∃ q : ℤ,
          ∃ f : (powerDerivedPushdown A ell positive ℂ).obj (DerivedCategory.Q.obj E) ⟶
            ((arrangementNormalizedDerivedHom fan regular basis rays).obj
              ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
                (arrangementCartierCoefficient fan regular b)))⟦q⟧, f ≠ 0 := by
  classical
  choose m scalarDegree test testNonzero using tests
  let carrier := normalizedUniversalLiftCarrier fan basis rays b
  let P := normalizedUniversalLiftClosedSupport fan basis rays b
  let K := normalizedUniversalLiftComplex fan basis rays b
  let downP := normalizedUniversalLiftClosedSupport_downward fan basis rays b
  obtain ⟨threshold,positiveThreshold,shrink⟩ := normalizedCells_uniform_shrinking
    fan regular basis rays m carrier
    (normalizedUniversalLiftCarrier_isCompact fan regular basis rays complete b).isBounded
  refine ⟨threshold,positiveThreshold,?_⟩
  intro ell large E nonzero morse
  have positive : 0 < ell := positiveThreshold.trans_le large
  obtain ⟨c,nonzeroCell,maximal⟩ := exists_normalized_maximal_support A ℂ E nonzero
  let lifted := normalizedUniversalCell A c
  have covered := maximalSupport_fanNormal_cover fan regular basis rays
    (universalPeriodicComplex A ℂ E) morse lifted nonzeroCell maximal
  let chosen : NormalCoveredNormalizedCell fan regular basis rays := ⟨c,covered⟩
  obtain ⟨v₀,u,center,compatible,inside⟩ := shrink ell large chosen
  have insideCells : ∀ d : UniversalIncidenceObject A, P d →
      powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
        localStar (augmentedForms A) (cellCenter (augmentedForms A) lifted.2) := by
    intro d hd
    exact inside _ (hd (cell_subset_closedCell _ _ _ (cellCenter_mem _ d.2)))
  let selected := lifted.2.val.2
  obtain ⟨restrictedTest,restrictedNonzero⟩ := Cellular.restrict_shifted_nonzero_closed_scalar_test
    ℂ P (universalAffineSliceSupport A selected (m chosen)) downP
    (universalAffineSliceSupport_downward A selected (m chosen)) K
    (normalizedUniversalLiftComplex_acyclic_outside fan basis rays b)
    (scalarDegree chosen) (test chosen) (testNonzero chosen)
  obtain ⟨q,f,hf⟩ := exists_nonzero_from_shrunk_branch_shifted_test A ℂ lifted P downP
    ell positive u insideCells selected rfl (m chosen) v₀ center compatible
    (universalPeriodicComplex A ℂ E) K nonzeroCell maximal
    (normalizedUniversalLiftComplex_acyclic_outside fan basis rays b)
    (scalarDegree chosen) restrictedTest restrictedNonzero
  obtain ⟨r,g,hg⟩ := exists_nonzero_normalized_power_of_geometric_branch
    fan regular basis rays complete b ell positive E u q f hf
  exact ⟨positive,r,g,hg⟩

end ToricPower

end
