module
prelude
public import SmallSubsumedForest15DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_128 : dispositionTest 128 = true := by decide +kernel

theorem disposition_at_129 : dispositionTest 129 = true := by decide +kernel

theorem disposition_at_130 : dispositionTest 130 = true := by decide +kernel

theorem disposition_at_131 : dispositionTest 131 = true := by decide +kernel


theorem disposition_at_132 : dispositionTest 132 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 132).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0062.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0062) = true
  rw [Nonrational.OldTerminalMatches.M000.r0062_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_133 : dispositionTest 133 = true := by decide +kernel

theorem disposition_at_134 : dispositionTest 134 = true := by decide +kernel

theorem disposition_at_135 : dispositionTest 135 = true := by decide +kernel

theorem disposition_at_136 : dispositionTest 136 = true := by decide +kernel

theorem disposition_at_137 : dispositionTest 137 = true := by decide +kernel

theorem disposition_at_138 : dispositionTest 138 = true := by decide +kernel

theorem disposition_at_139 : dispositionTest 139 = true := by decide +kernel

theorem disposition_at_140 : dispositionTest 140 = true := by decide +kernel

theorem disposition_at_141 : dispositionTest 141 = true := by decide +kernel

theorem disposition_at_142 : dispositionTest 142 = true := by decide +kernel

theorem disposition_at_143 : dispositionTest 143 = true := by decide +kernel

theorem disposition_at_144 : dispositionTest 144 = true := by decide +kernel

theorem disposition_at_145 : dispositionTest 145 = true := by decide +kernel

theorem disposition_at_146 : dispositionTest 146 = true := by decide +kernel

theorem disposition_at_147 : dispositionTest 147 = true := by decide +kernel

theorem disposition_at_148 : dispositionTest 148 = true := by decide +kernel

theorem disposition_at_149 : dispositionTest 149 = true := by decide +kernel

theorem disposition_at_150 : dispositionTest 150 = true := by decide +kernel

theorem disposition_at_151 : dispositionTest 151 = true := by decide +kernel

theorem disposition_at_152 : dispositionTest 152 = true := by decide +kernel


theorem disposition_at_153 : dispositionTest 153 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 153).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0063.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0063) = true
  rw [Nonrational.OldTerminalMatches.M000.r0063_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_154 : dispositionTest 154 = true := by decide +kernel


theorem disposition_at_155 : dispositionTest 155 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 155).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0064.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0064) = true
  rw [Nonrational.OldTerminalMatches.M001.r0064_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_156 : dispositionTest 156 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 156).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0065.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0065) = true
  rw [Nonrational.OldTerminalMatches.M001.r0065_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_157 : dispositionTest 157 = true := by decide +kernel

theorem disposition_at_158 : dispositionTest 158 = true := by decide +kernel

theorem disposition_at_159 : dispositionTest 159 = true := by decide +kernel

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


theorem disposition_interval_145 : Interval dispositionTest 145 146 := by
  intro i hlo hhi
  have h : i = 145 := by omega
  subst i
  exact disposition_at_145


theorem disposition_interval_146 : Interval dispositionTest 146 147 := by
  intro i hlo hhi
  have h : i = 146 := by omega
  subst i
  exact disposition_at_146


theorem disposition_interval_147 : Interval dispositionTest 147 148 := by
  intro i hlo hhi
  have h : i = 147 := by omega
  subst i
  exact disposition_at_147


theorem disposition_interval_148 : Interval dispositionTest 148 149 := by
  intro i hlo hhi
  have h : i = 148 := by omega
  subst i
  exact disposition_at_148


theorem disposition_interval_149 : Interval dispositionTest 149 150 := by
  intro i hlo hhi
  have h : i = 149 := by omega
  subst i
  exact disposition_at_149


theorem disposition_interval_150 : Interval dispositionTest 150 151 := by
  intro i hlo hhi
  have h : i = 150 := by omega
  subst i
  exact disposition_at_150


theorem disposition_interval_151 : Interval dispositionTest 151 152 := by
  intro i hlo hhi
  have h : i = 151 := by omega
  subst i
  exact disposition_at_151


theorem disposition_interval_152 : Interval dispositionTest 152 153 := by
  intro i hlo hhi
  have h : i = 152 := by omega
  subst i
  exact disposition_at_152


theorem disposition_interval_153 : Interval dispositionTest 153 154 := by
  intro i hlo hhi
  have h : i = 153 := by omega
  subst i
  exact disposition_at_153


theorem disposition_interval_154 : Interval dispositionTest 154 155 := by
  intro i hlo hhi
  have h : i = 154 := by omega
  subst i
  exact disposition_at_154


theorem disposition_interval_155 : Interval dispositionTest 155 156 := by
  intro i hlo hhi
  have h : i = 155 := by omega
  subst i
  exact disposition_at_155


theorem disposition_interval_156 : Interval dispositionTest 156 157 := by
  intro i hlo hhi
  have h : i = 156 := by omega
  subst i
  exact disposition_at_156


theorem disposition_interval_157 : Interval dispositionTest 157 158 := by
  intro i hlo hhi
  have h : i = 157 := by omega
  subst i
  exact disposition_at_157


theorem disposition_interval_158 : Interval dispositionTest 158 159 := by
  intro i hlo hhi
  have h : i = 158 := by omega
  subst i
  exact disposition_at_158


theorem disposition_interval_159 : Interval dispositionTest 159 160 := by
  intro i hlo hhi
  have h : i = 159 := by omega
  subst i
  exact disposition_at_159

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
