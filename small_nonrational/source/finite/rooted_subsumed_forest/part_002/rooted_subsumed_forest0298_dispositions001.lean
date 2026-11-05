module
prelude
public import RootedSubsumedForest0298DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem disposition_at_32 : dispositionTest 32 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 32).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0375.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0375) = true
  rw [Nonrational.OldTerminalMatches.M005.r0375_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_33 : dispositionTest 33 = true := by decide +kernel


theorem disposition_at_34 : dispositionTest 34 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 34).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0376.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0376) = true
  rw [Nonrational.OldTerminalMatches.M005.r0376_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_35 : dispositionTest 35 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 35).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0377.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0377) = true
  rw [Nonrational.OldTerminalMatches.M005.r0377_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_36 : dispositionTest 36 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 36).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0378.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0378) = true
  rw [Nonrational.OldTerminalMatches.M005.r0378_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_37 : dispositionTest 37 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 37).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0379.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0379) = true
  rw [Nonrational.OldTerminalMatches.M005.r0379_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_38 : dispositionTest 38 = true := by decide +kernel

theorem disposition_at_39 : dispositionTest 39 = true := by decide +kernel


theorem disposition_at_40 : dispositionTest 40 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 40).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0380.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0380) = true
  rw [Nonrational.OldTerminalMatches.M005.r0380_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_41 : dispositionTest 41 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 41).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M005.r0381.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M005.r0381) = true
  rw [Nonrational.OldTerminalMatches.M005.r0381_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_42 : dispositionTest 42 = true := by decide +kernel

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


theorem disposition_interval_36 : Interval dispositionTest 36 37 := by
  intro i hlo hhi
  have h : i = 36 := by omega
  subst i
  exact disposition_at_36


theorem disposition_interval_37 : Interval dispositionTest 37 38 := by
  intro i hlo hhi
  have h : i = 37 := by omega
  subst i
  exact disposition_at_37


theorem disposition_interval_38 : Interval dispositionTest 38 39 := by
  intro i hlo hhi
  have h : i = 38 := by omega
  subst i
  exact disposition_at_38


theorem disposition_interval_39 : Interval dispositionTest 39 40 := by
  intro i hlo hhi
  have h : i = 39 := by omega
  subst i
  exact disposition_at_39


theorem disposition_interval_40 : Interval dispositionTest 40 41 := by
  intro i hlo hhi
  have h : i = 40 := by omega
  subst i
  exact disposition_at_40


theorem disposition_interval_41 : Interval dispositionTest 41 42 := by
  intro i hlo hhi
  have h : i = 41 := by omega
  subst i
  exact disposition_at_41


theorem disposition_interval_42 : Interval dispositionTest 42 43 := by
  intro i hlo hhi
  have h : i = 42 := by omega
  subst i
  exact disposition_at_42

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
