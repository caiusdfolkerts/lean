module
prelude
public import RootedSubsumedForest0302DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem disposition_at_128 : dispositionTest 128 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 128).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0425.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0425) = true
  rw [Nonrational.OldTerminalMatches.M006.r0425_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_129 : dispositionTest 129 = true := by decide +kernel

theorem disposition_at_130 : dispositionTest 130 = true := by decide +kernel


theorem disposition_at_131 : dispositionTest 131 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 131).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0426.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0426) = true
  rw [Nonrational.OldTerminalMatches.M006.r0426_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_132 : dispositionTest 132 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 132).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0427.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0427) = true
  rw [Nonrational.OldTerminalMatches.M006.r0427_checked, Bool.and_true]
  decide +kernel

theorem disposition_interval_128 : Interval dispositionTest 128 129 := by
  intro i hlo hhi
  have h : i = 128 := by omega
  subst i
  exact disposition_at_128


theorem disposition_interval_129 : Interval dispositionTest 129 130 := by
  intro i hlo hhi
  have h : i = 129 := by omega
  subst i
  exact disposition_at_129


theorem disposition_interval_130 : Interval dispositionTest 130 131 := by
  intro i hlo hhi
  have h : i = 130 := by omega
  subst i
  exact disposition_at_130


theorem disposition_interval_131 : Interval dispositionTest 131 132 := by
  intro i hlo hhi
  have h : i = 131 := by omega
  subst i
  exact disposition_at_131


theorem disposition_interval_132 : Interval dispositionTest 132 133 := by
  intro i hlo hhi
  have h : i = 132 := by omega
  subst i
  exact disposition_at_132

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
