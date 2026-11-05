module
prelude
public import RootedSubsumedForest0337DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem disposition_at_128 : dispositionTest 128 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 128).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0533.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0533) = true
  rw [Nonrational.OldTerminalMatches.M008.r0533_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_129 : dispositionTest 129 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 129).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0534.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0534) = true
  rw [Nonrational.OldTerminalMatches.M008.r0534_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_130 : dispositionTest 130 = true := by decide +kernel

theorem disposition_at_131 : dispositionTest 131 = true := by decide +kernel

theorem disposition_at_132 : dispositionTest 132 = true := by decide +kernel

theorem disposition_at_133 : dispositionTest 133 = true := by decide +kernel

theorem disposition_at_134 : dispositionTest 134 = true := by decide +kernel

theorem disposition_at_135 : dispositionTest 135 = true := by decide +kernel

theorem disposition_at_136 : dispositionTest 136 = true := by decide +kernel

theorem disposition_at_137 : dispositionTest 137 = true := by decide +kernel

theorem disposition_at_138 : dispositionTest 138 = true := by decide +kernel


theorem disposition_at_139 : dispositionTest 139 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 139).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0535.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0535) = true
  rw [Nonrational.OldTerminalMatches.M008.r0535_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_140 : dispositionTest 140 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 140).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0536.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0536) = true
  rw [Nonrational.OldTerminalMatches.M008.r0536_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_141 : dispositionTest 141 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 141).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0537.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0537) = true
  rw [Nonrational.OldTerminalMatches.M008.r0537_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_142 : dispositionTest 142 = true := by decide +kernel


theorem disposition_at_143 : dispositionTest 143 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 143).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) Nonrational.OldTerminalMatches.M008.r0538.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M008.r0538) = true
  rw [Nonrational.OldTerminalMatches.M008.r0538_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_144 : dispositionTest 144 = true := by decide +kernel

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


theorem disposition_interval_138 : Interval dispositionTest 138 139 := by
  intro i hlo hhi
  have h : i = 138 := by omega
  subst i
  exact disposition_at_138


theorem disposition_interval_139 : Interval dispositionTest 139 140 := by
  intro i hlo hhi
  have h : i = 139 := by omega
  subst i
  exact disposition_at_139


theorem disposition_interval_140 : Interval dispositionTest 140 141 := by
  intro i hlo hhi
  have h : i = 140 := by omega
  subst i
  exact disposition_at_140


theorem disposition_interval_141 : Interval dispositionTest 141 142 := by
  intro i hlo hhi
  have h : i = 141 := by omega
  subst i
  exact disposition_at_141


theorem disposition_interval_142 : Interval dispositionTest 142 143 := by
  intro i hlo hhi
  have h : i = 142 := by omega
  subst i
  exact disposition_at_142


theorem disposition_interval_143 : Interval dispositionTest 143 144 := by
  intro i hlo hhi
  have h : i = 143 := by omega
  subst i
  exact disposition_at_143


theorem disposition_interval_144 : Interval dispositionTest 144 145 := by
  intro i hlo hhi
  have h : i = 144 := by omega
  subst i
  exact disposition_at_144

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
