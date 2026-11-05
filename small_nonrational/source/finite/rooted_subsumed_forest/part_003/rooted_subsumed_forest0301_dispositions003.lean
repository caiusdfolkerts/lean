module
prelude
public import RootedSubsumedForest0301DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_96 : dispositionTest 96 = true := by decide +kernel

theorem disposition_at_97 : dispositionTest 97 = true := by decide +kernel

theorem disposition_at_98 : dispositionTest 98 = true := by decide +kernel


theorem disposition_at_99 : dispositionTest 99 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 99).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0404.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0404) = true
  rw [Nonrational.OldTerminalMatches.M006.r0404_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_100 : dispositionTest 100 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 100).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0405.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0405) = true
  rw [Nonrational.OldTerminalMatches.M006.r0405_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_101 : dispositionTest 101 = true := by decide +kernel

theorem disposition_at_102 : dispositionTest 102 = true := by decide +kernel

theorem disposition_at_103 : dispositionTest 103 = true := by decide +kernel


theorem disposition_at_104 : dispositionTest 104 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 104).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0406.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0406) = true
  rw [Nonrational.OldTerminalMatches.M006.r0406_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_105 : dispositionTest 105 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 105).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0407.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0407) = true
  rw [Nonrational.OldTerminalMatches.M006.r0407_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_106 : dispositionTest 106 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 106).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0408.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0408) = true
  rw [Nonrational.OldTerminalMatches.M006.r0408_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_107 : dispositionTest 107 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 107).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M006.r0409.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M006.r0409) = true
  rw [Nonrational.OldTerminalMatches.M006.r0409_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_108 : dispositionTest 108 = true := by decide +kernel

theorem disposition_at_109 : dispositionTest 109 = true := by decide +kernel

theorem disposition_at_110 : dispositionTest 110 = true := by decide +kernel

theorem disposition_at_111 : dispositionTest 111 = true := by decide +kernel

theorem disposition_at_112 : dispositionTest 112 = true := by decide +kernel

theorem disposition_at_113 : dispositionTest 113 = true := by decide +kernel

theorem disposition_at_114 : dispositionTest 114 = true := by decide +kernel

theorem disposition_at_115 : dispositionTest 115 = true := by decide +kernel

theorem disposition_at_116 : dispositionTest 116 = true := by decide +kernel

theorem disposition_at_117 : dispositionTest 117 = true := by decide +kernel

theorem disposition_at_118 : dispositionTest 118 = true := by decide +kernel

theorem disposition_at_119 : dispositionTest 119 = true := by decide +kernel

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


theorem disposition_interval_105 : Interval dispositionTest 105 106 := by
  intro i hlo hhi
  have h : i = 105 := by omega
  subst i
  exact disposition_at_105


theorem disposition_interval_106 : Interval dispositionTest 106 107 := by
  intro i hlo hhi
  have h : i = 106 := by omega
  subst i
  exact disposition_at_106


theorem disposition_interval_107 : Interval dispositionTest 107 108 := by
  intro i hlo hhi
  have h : i = 107 := by omega
  subst i
  exact disposition_at_107


theorem disposition_interval_108 : Interval dispositionTest 108 109 := by
  intro i hlo hhi
  have h : i = 108 := by omega
  subst i
  exact disposition_at_108


theorem disposition_interval_109 : Interval dispositionTest 109 110 := by
  intro i hlo hhi
  have h : i = 109 := by omega
  subst i
  exact disposition_at_109


theorem disposition_interval_110 : Interval dispositionTest 110 111 := by
  intro i hlo hhi
  have h : i = 110 := by omega
  subst i
  exact disposition_at_110


theorem disposition_interval_111 : Interval dispositionTest 111 112 := by
  intro i hlo hhi
  have h : i = 111 := by omega
  subst i
  exact disposition_at_111


theorem disposition_interval_112 : Interval dispositionTest 112 113 := by
  intro i hlo hhi
  have h : i = 112 := by omega
  subst i
  exact disposition_at_112


theorem disposition_interval_113 : Interval dispositionTest 113 114 := by
  intro i hlo hhi
  have h : i = 113 := by omega
  subst i
  exact disposition_at_113


theorem disposition_interval_114 : Interval dispositionTest 114 115 := by
  intro i hlo hhi
  have h : i = 114 := by omega
  subst i
  exact disposition_at_114


theorem disposition_interval_115 : Interval dispositionTest 115 116 := by
  intro i hlo hhi
  have h : i = 115 := by omega
  subst i
  exact disposition_at_115


theorem disposition_interval_116 : Interval dispositionTest 116 117 := by
  intro i hlo hhi
  have h : i = 116 := by omega
  subst i
  exact disposition_at_116


theorem disposition_interval_117 : Interval dispositionTest 117 118 := by
  intro i hlo hhi
  have h : i = 117 := by omega
  subst i
  exact disposition_at_117


theorem disposition_interval_118 : Interval dispositionTest 118 119 := by
  intro i hlo hhi
  have h : i = 118 := by omega
  subst i
  exact disposition_at_118


theorem disposition_interval_119 : Interval dispositionTest 119 120 := by
  intro i hlo hhi
  have h : i = 119 := by omega
  subst i
  exact disposition_at_119

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
