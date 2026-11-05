module
prelude
public import RootedSubsumedForest0865DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_32 : dispositionTest 32 = true := by decide +kernel

theorem disposition_at_33 : dispositionTest 33 = true := by decide +kernel

theorem disposition_at_34 : dispositionTest 34 = true := by decide +kernel


theorem disposition_at_35 : dispositionTest 35 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 35).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1651.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1651) = true
  rw [Nonrational.OldTerminalMatches.M025.r1651_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_32 : Interval dispositionTest 32 33 := by
  intro i hlo hhi
  have h : i = 32 := by omega
  subst i
  exact disposition_at_32


theorem disposition_interval_33 : Interval dispositionTest 33 34 := by
  intro i hlo hhi
  have h : i = 33 := by omega
  subst i
  exact disposition_at_33


theorem disposition_interval_34 : Interval dispositionTest 34 35 := by
  intro i hlo hhi
  have h : i = 34 := by omega
  subst i
  exact disposition_at_34


theorem disposition_interval_35 : Interval dispositionTest 35 36 := by
  intro i hlo hhi
  have h : i = 35 := by omega
  subst i
  exact disposition_at_35

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
