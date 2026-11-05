module
prelude
public import RootedSubsumedForest0355DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_96 : dispositionTest 96 = true := by decide +kernel

theorem disposition_at_97 : dispositionTest 97 = true := by decide +kernel

theorem disposition_at_98 : dispositionTest 98 = true := by decide +kernel

theorem disposition_at_99 : dispositionTest 99 = true := by decide +kernel

theorem disposition_at_100 : dispositionTest 100 = true := by decide +kernel

theorem disposition_at_101 : dispositionTest 101 = true := by decide +kernel

theorem disposition_at_102 : dispositionTest 102 = true := by decide +kernel

theorem disposition_at_103 : dispositionTest 103 = true := by decide +kernel

theorem disposition_at_104 : dispositionTest 104 = true := by decide +kernel

theorem disposition_at_105 : dispositionTest 105 = true := by decide +kernel

theorem disposition_at_106 : dispositionTest 106 = true := by decide +kernel

theorem disposition_at_107 : dispositionTest 107 = true := by decide +kernel

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


theorem disposition_at_119 : dispositionTest 119 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 119).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0957.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0957) = true
  rw [Nonrational.OldTerminalMatches.M014.r0957_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_120 : dispositionTest 120 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 120).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M014.r0958.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M014.r0958) = true
  rw [Nonrational.OldTerminalMatches.M014.r0958_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_121 : dispositionTest 121 = true := by decide +kernel

theorem disposition_at_122 : dispositionTest 122 = true := by decide +kernel

theorem disposition_at_123 : dispositionTest 123 = true := by decide +kernel

theorem disposition_at_124 : dispositionTest 124 = true := by decide +kernel

theorem disposition_at_125 : dispositionTest 125 = true := by decide +kernel

theorem disposition_at_126 : dispositionTest 126 = true := by decide +kernel

theorem disposition_at_127 : dispositionTest 127 = true := by decide +kernel

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


theorem disposition_interval_120 : Interval dispositionTest 120 121 := by
  intro i hlo hhi
  have h : i = 120 := by omega
  subst i
  exact disposition_at_120


theorem disposition_interval_121 : Interval dispositionTest 121 122 := by
  intro i hlo hhi
  have h : i = 121 := by omega
  subst i
  exact disposition_at_121


theorem disposition_interval_122 : Interval dispositionTest 122 123 := by
  intro i hlo hhi
  have h : i = 122 := by omega
  subst i
  exact disposition_at_122


theorem disposition_interval_123 : Interval dispositionTest 123 124 := by
  intro i hlo hhi
  have h : i = 123 := by omega
  subst i
  exact disposition_at_123


theorem disposition_interval_124 : Interval dispositionTest 124 125 := by
  intro i hlo hhi
  have h : i = 124 := by omega
  subst i
  exact disposition_at_124


theorem disposition_interval_125 : Interval dispositionTest 125 126 := by
  intro i hlo hhi
  have h : i = 125 := by omega
  subst i
  exact disposition_at_125


theorem disposition_interval_126 : Interval dispositionTest 126 127 := by
  intro i hlo hhi
  have h : i = 126 := by omega
  subst i
  exact disposition_at_126


theorem disposition_interval_127 : Interval dispositionTest 127 128 := by
  intro i hlo hhi
  have h : i = 127 := by omega
  subst i
  exact disposition_at_127

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
