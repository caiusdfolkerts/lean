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
theorem disposition_at_160 : dispositionTest 160 = true := by decide +kernel

theorem disposition_at_161 : dispositionTest 161 = true := by decide +kernel

theorem disposition_at_162 : dispositionTest 162 = true := by decide +kernel

theorem disposition_at_163 : dispositionTest 163 = true := by decide +kernel

theorem disposition_at_164 : dispositionTest 164 = true := by decide +kernel

theorem disposition_at_165 : dispositionTest 165 = true := by decide +kernel


theorem disposition_at_166 : dispositionTest 166 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 166).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0066.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0066) = true
  rw [Nonrational.OldTerminalMatches.M001.r0066_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_167 : dispositionTest 167 = true := by decide +kernel


theorem disposition_at_168 : dispositionTest 168 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 168).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0067.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0067) = true
  rw [Nonrational.OldTerminalMatches.M001.r0067_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_169 : dispositionTest 169 = true := by decide +kernel


theorem disposition_at_170 : dispositionTest 170 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 170).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0068.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0068) = true
  rw [Nonrational.OldTerminalMatches.M001.r0068_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_171 : dispositionTest 171 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 171).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0069.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0069) = true
  rw [Nonrational.OldTerminalMatches.M001.r0069_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_172 : dispositionTest 172 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 172).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0070.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0070) = true
  rw [Nonrational.OldTerminalMatches.M001.r0070_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_173 : dispositionTest 173 = true := by decide +kernel


theorem disposition_at_174 : dispositionTest 174 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 174).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0071.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0071) = true
  rw [Nonrational.OldTerminalMatches.M001.r0071_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_175 : dispositionTest 175 = true := by decide +kernel


theorem disposition_at_176 : dispositionTest 176 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 176).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0072.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0072) = true
  rw [Nonrational.OldTerminalMatches.M001.r0072_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_177 : dispositionTest 177 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 177).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0073.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0073) = true
  rw [Nonrational.OldTerminalMatches.M001.r0073_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_178 : dispositionTest 178 = true := by decide +kernel

theorem disposition_at_179 : dispositionTest 179 = true := by decide +kernel


theorem disposition_at_180 : dispositionTest 180 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 180).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0074.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0074) = true
  rw [Nonrational.OldTerminalMatches.M001.r0074_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_181 : dispositionTest 181 = true := by decide +kernel

theorem disposition_at_182 : dispositionTest 182 = true := by decide +kernel


theorem disposition_at_183 : dispositionTest 183 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 183).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0075.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0075) = true
  rw [Nonrational.OldTerminalMatches.M001.r0075_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_184 : dispositionTest 184 = true := by decide +kernel

theorem disposition_at_185 : dispositionTest 185 = true := by decide +kernel

theorem disposition_at_186 : dispositionTest 186 = true := by decide +kernel

theorem disposition_at_187 : dispositionTest 187 = true := by decide +kernel

theorem disposition_at_188 : dispositionTest 188 = true := by decide +kernel

theorem disposition_at_189 : dispositionTest 189 = true := by decide +kernel

theorem disposition_at_190 : dispositionTest 190 = true := by decide +kernel


theorem disposition_at_191 : dispositionTest 191 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 191).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M001.r0076.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M001.r0076) = true
  rw [Nonrational.OldTerminalMatches.M001.r0076_checked, Bool.and_true]
  decide +kernel

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


theorem disposition_interval_181 : Interval dispositionTest 181 182 := by
  intro i hlo hhi
  have h : i = 181 := by omega
  subst i
  exact disposition_at_181


theorem disposition_interval_182 : Interval dispositionTest 182 183 := by
  intro i hlo hhi
  have h : i = 182 := by omega
  subst i
  exact disposition_at_182


theorem disposition_interval_183 : Interval dispositionTest 183 184 := by
  intro i hlo hhi
  have h : i = 183 := by omega
  subst i
  exact disposition_at_183


theorem disposition_interval_184 : Interval dispositionTest 184 185 := by
  intro i hlo hhi
  have h : i = 184 := by omega
  subst i
  exact disposition_at_184


theorem disposition_interval_185 : Interval dispositionTest 185 186 := by
  intro i hlo hhi
  have h : i = 185 := by omega
  subst i
  exact disposition_at_185


theorem disposition_interval_186 : Interval dispositionTest 186 187 := by
  intro i hlo hhi
  have h : i = 186 := by omega
  subst i
  exact disposition_at_186


theorem disposition_interval_187 : Interval dispositionTest 187 188 := by
  intro i hlo hhi
  have h : i = 187 := by omega
  subst i
  exact disposition_at_187


theorem disposition_interval_188 : Interval dispositionTest 188 189 := by
  intro i hlo hhi
  have h : i = 188 := by omega
  subst i
  exact disposition_at_188


theorem disposition_interval_189 : Interval dispositionTest 189 190 := by
  intro i hlo hhi
  have h : i = 189 := by omega
  subst i
  exact disposition_at_189


theorem disposition_interval_190 : Interval dispositionTest 190 191 := by
  intro i hlo hhi
  have h : i = 190 := by omega
  subst i
  exact disposition_at_190


theorem disposition_interval_191 : Interval dispositionTest 191 192 := by
  intro i hlo hhi
  have h : i = 191 := by omega
  subst i
  exact disposition_at_191

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
