module
prelude
public import RootedSubsumedForest0303DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem disposition_at_96 : dispositionTest 96 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 96).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0438.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0438) = true
  rw [Nonrational.OldTerminalMatches.M006.r0438_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_97 : dispositionTest 97 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 97).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0439.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0439) = true
  rw [Nonrational.OldTerminalMatches.M006.r0439_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_98 : dispositionTest 98 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 98).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0440.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0440) = true
  rw [Nonrational.OldTerminalMatches.M006.r0440_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_99 : dispositionTest 99 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 99).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0441.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0441) = true
  rw [Nonrational.OldTerminalMatches.M006.r0441_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_100 : dispositionTest 100 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 100).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0442.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0442) = true
  rw [Nonrational.OldTerminalMatches.M006.r0442_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_101 : dispositionTest 101 = true := by decide +kernel

theorem disposition_at_102 : dispositionTest 102 = true := by decide +kernel

theorem disposition_at_103 : dispositionTest 103 = true := by decide +kernel

theorem disposition_at_104 : dispositionTest 104 = true := by decide +kernel

theorem disposition_interval_96 : Interval dispositionTest 96 97 := by
  intro i hlo hhi
  have h : i = 96 := by omega
  subst i
  exact disposition_at_96


theorem disposition_interval_97 : Interval dispositionTest 97 98 := by
  intro i hlo hhi
  have h : i = 97 := by omega
  subst i
  exact disposition_at_97


theorem disposition_interval_98 : Interval dispositionTest 98 99 := by
  intro i hlo hhi
  have h : i = 98 := by omega
  subst i
  exact disposition_at_98


theorem disposition_interval_99 : Interval dispositionTest 99 100 := by
  intro i hlo hhi
  have h : i = 99 := by omega
  subst i
  exact disposition_at_99


theorem disposition_interval_100 : Interval dispositionTest 100 101 := by
  intro i hlo hhi
  have h : i = 100 := by omega
  subst i
  exact disposition_at_100


theorem disposition_interval_101 : Interval dispositionTest 101 102 := by
  intro i hlo hhi
  have h : i = 101 := by omega
  subst i
  exact disposition_at_101


theorem disposition_interval_102 : Interval dispositionTest 102 103 := by
  intro i hlo hhi
  have h : i = 102 := by omega
  subst i
  exact disposition_at_102


theorem disposition_interval_103 : Interval dispositionTest 103 104 := by
  intro i hlo hhi
  have h : i = 103 := by omega
  subst i
  exact disposition_at_103


theorem disposition_interval_104 : Interval dispositionTest 104 105 := by
  intro i hlo hhi
  have h : i = 104 := by omega
  subst i
  exact disposition_at_104

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
