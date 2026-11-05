module
prelude
public import RootedSubsumedForest0869DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_160 : dispositionTest 160 = true := by decide +kernel


theorem disposition_at_161 : dispositionTest 161 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 161).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1660.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1660) = true
  rw [Nonrational.OldTerminalMatches.M025.r1660_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_162 : dispositionTest 162 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 162).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1661.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1661) = true
  rw [Nonrational.OldTerminalMatches.M025.r1661_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_163 : dispositionTest 163 = true := by decide +kernel

theorem disposition_at_164 : dispositionTest 164 = true := by decide +kernel

theorem disposition_at_165 : dispositionTest 165 = true := by decide +kernel

theorem disposition_at_166 : dispositionTest 166 = true := by decide +kernel


theorem disposition_at_167 : dispositionTest 167 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 167).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) Nonrational.OldTerminalMatches.M025.r1662.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M025.r1662) = true
  rw [Nonrational.OldTerminalMatches.M025.r1662_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_168 : dispositionTest 168 = true := by decide +kernel

theorem disposition_at_169 : dispositionTest 169 = true := by decide +kernel

theorem disposition_at_170 : dispositionTest 170 = true := by decide +kernel

theorem disposition_at_171 : dispositionTest 171 = true := by decide +kernel

theorem disposition_at_172 : dispositionTest 172 = true := by decide +kernel

theorem disposition_at_173 : dispositionTest 173 = true := by decide +kernel

theorem disposition_at_174 : dispositionTest 174 = true := by decide +kernel

theorem disposition_at_175 : dispositionTest 175 = true := by decide +kernel

theorem disposition_at_176 : dispositionTest 176 = true := by decide +kernel

theorem disposition_at_177 : dispositionTest 177 = true := by decide +kernel

theorem disposition_at_178 : dispositionTest 178 = true := by decide +kernel

theorem disposition_at_179 : dispositionTest 179 = true := by decide +kernel

theorem disposition_at_180 : dispositionTest 180 = true := by decide +kernel

theorem disposition_interval_160 : Interval dispositionTest 160 161 := by
  intro i hlo hhi
  have h : i = 160 := by omega
  subst i
  exact disposition_at_160


theorem disposition_interval_161 : Interval dispositionTest 161 162 := by
  intro i hlo hhi
  have h : i = 161 := by omega
  subst i
  exact disposition_at_161


theorem disposition_interval_162 : Interval dispositionTest 162 163 := by
  intro i hlo hhi
  have h : i = 162 := by omega
  subst i
  exact disposition_at_162


theorem disposition_interval_163 : Interval dispositionTest 163 164 := by
  intro i hlo hhi
  have h : i = 163 := by omega
  subst i
  exact disposition_at_163


theorem disposition_interval_164 : Interval dispositionTest 164 165 := by
  intro i hlo hhi
  have h : i = 164 := by omega
  subst i
  exact disposition_at_164


theorem disposition_interval_165 : Interval dispositionTest 165 166 := by
  intro i hlo hhi
  have h : i = 165 := by omega
  subst i
  exact disposition_at_165


theorem disposition_interval_166 : Interval dispositionTest 166 167 := by
  intro i hlo hhi
  have h : i = 166 := by omega
  subst i
  exact disposition_at_166


theorem disposition_interval_167 : Interval dispositionTest 167 168 := by
  intro i hlo hhi
  have h : i = 167 := by omega
  subst i
  exact disposition_at_167


theorem disposition_interval_168 : Interval dispositionTest 168 169 := by
  intro i hlo hhi
  have h : i = 168 := by omega
  subst i
  exact disposition_at_168


theorem disposition_interval_169 : Interval dispositionTest 169 170 := by
  intro i hlo hhi
  have h : i = 169 := by omega
  subst i
  exact disposition_at_169


theorem disposition_interval_170 : Interval dispositionTest 170 171 := by
  intro i hlo hhi
  have h : i = 170 := by omega
  subst i
  exact disposition_at_170


theorem disposition_interval_171 : Interval dispositionTest 171 172 := by
  intro i hlo hhi
  have h : i = 171 := by omega
  subst i
  exact disposition_at_171


theorem disposition_interval_172 : Interval dispositionTest 172 173 := by
  intro i hlo hhi
  have h : i = 172 := by omega
  subst i
  exact disposition_at_172


theorem disposition_interval_173 : Interval dispositionTest 173 174 := by
  intro i hlo hhi
  have h : i = 173 := by omega
  subst i
  exact disposition_at_173


theorem disposition_interval_174 : Interval dispositionTest 174 175 := by
  intro i hlo hhi
  have h : i = 174 := by omega
  subst i
  exact disposition_at_174


theorem disposition_interval_175 : Interval dispositionTest 175 176 := by
  intro i hlo hhi
  have h : i = 175 := by omega
  subst i
  exact disposition_at_175


theorem disposition_interval_176 : Interval dispositionTest 176 177 := by
  intro i hlo hhi
  have h : i = 176 := by omega
  subst i
  exact disposition_at_176


theorem disposition_interval_177 : Interval dispositionTest 177 178 := by
  intro i hlo hhi
  have h : i = 177 := by omega
  subst i
  exact disposition_at_177


theorem disposition_interval_178 : Interval dispositionTest 178 179 := by
  intro i hlo hhi
  have h : i = 178 := by omega
  subst i
  exact disposition_at_178


theorem disposition_interval_179 : Interval dispositionTest 179 180 := by
  intro i hlo hhi
  have h : i = 179 := by omega
  subst i
  exact disposition_at_179


theorem disposition_interval_180 : Interval dispositionTest 180 181 := by
  intro i hlo hhi
  have h : i = 180 := by omega
  subst i
  exact disposition_at_180

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
