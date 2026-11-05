module
prelude
public import RootedSubsumedForest0695DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_128 : dispositionTest 128 = true := by decide +kernel

theorem disposition_at_129 : dispositionTest 129 = true := by decide +kernel

theorem disposition_at_130 : dispositionTest 130 = true := by decide +kernel

theorem disposition_at_131 : dispositionTest 131 = true := by decide +kernel

theorem disposition_at_132 : dispositionTest 132 = true := by decide +kernel

theorem disposition_at_133 : dispositionTest 133 = true := by decide +kernel


theorem disposition_at_134 : dispositionTest 134 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 134).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M019.r1224.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1224) = true
  rw [Nonrational.OldTerminalMatches.M019.r1224_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_135 : dispositionTest 135 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 135).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M019.r1225.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1225) = true
  rw [Nonrational.OldTerminalMatches.M019.r1225_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_136 : dispositionTest 136 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 136).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M019.r1226.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1226) = true
  rw [Nonrational.OldTerminalMatches.M019.r1226_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_137 : dispositionTest 137 = true := by decide +kernel

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


theorem disposition_interval_133 : Interval dispositionTest 133 134 := by
  intro i hlo hhi
  have h : i = 133 := by omega
  subst i
  exact disposition_at_133


theorem disposition_interval_134 : Interval dispositionTest 134 135 := by
  intro i hlo hhi
  have h : i = 134 := by omega
  subst i
  exact disposition_at_134


theorem disposition_interval_135 : Interval dispositionTest 135 136 := by
  intro i hlo hhi
  have h : i = 135 := by omega
  subst i
  exact disposition_at_135


theorem disposition_interval_136 : Interval dispositionTest 136 137 := by
  intro i hlo hhi
  have h : i = 136 := by omega
  subst i
  exact disposition_at_136


theorem disposition_interval_137 : Interval dispositionTest 137 138 := by
  intro i hlo hhi
  have h : i = 137 := by omega
  subst i
  exact disposition_at_137

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
