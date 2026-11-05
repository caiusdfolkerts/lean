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
theorem disposition_at_4064 : dispositionTest 4064 = true := by decide +kernel

theorem disposition_at_4065 : dispositionTest 4065 = true := by decide +kernel

theorem disposition_at_4066 : dispositionTest 4066 = true := by decide +kernel

theorem disposition_at_4067 : dispositionTest 4067 = true := by decide +kernel

theorem disposition_at_4068 : dispositionTest 4068 = true := by decide +kernel


theorem disposition_at_4069 : dispositionTest 4069 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4069).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1100.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1100) = true
  rw [Nonrational.OldTerminalMatches.M017.r1100_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4070 : dispositionTest 4070 = true := by decide +kernel


theorem disposition_at_4071 : dispositionTest 4071 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4071).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1101.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1101) = true
  rw [Nonrational.OldTerminalMatches.M017.r1101_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4072 : dispositionTest 4072 = true := by decide +kernel

theorem disposition_at_4073 : dispositionTest 4073 = true := by decide +kernel

theorem disposition_at_4074 : dispositionTest 4074 = true := by decide +kernel

theorem disposition_at_4075 : dispositionTest 4075 = true := by decide +kernel

theorem disposition_at_4076 : dispositionTest 4076 = true := by decide +kernel

theorem disposition_at_4077 : dispositionTest 4077 = true := by decide +kernel

theorem disposition_at_4078 : dispositionTest 4078 = true := by decide +kernel


theorem disposition_at_4079 : dispositionTest 4079 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4079).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1102.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1102) = true
  rw [Nonrational.OldTerminalMatches.M017.r1102_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4080 : dispositionTest 4080 = true := by decide +kernel

theorem disposition_at_4081 : dispositionTest 4081 = true := by decide +kernel

theorem disposition_at_4082 : dispositionTest 4082 = true := by decide +kernel

theorem disposition_at_4083 : dispositionTest 4083 = true := by decide +kernel

theorem disposition_interval_4064 : Interval dispositionTest 4064 4065 := by
  intro i hlo hhi
  have h : i = 4064 := by omega
  subst i
  exact disposition_at_4064


theorem disposition_interval_4065 : Interval dispositionTest 4065 4066 := by
  intro i hlo hhi
  have h : i = 4065 := by omega
  subst i
  exact disposition_at_4065


theorem disposition_interval_4066 : Interval dispositionTest 4066 4067 := by
  intro i hlo hhi
  have h : i = 4066 := by omega
  subst i
  exact disposition_at_4066


theorem disposition_interval_4067 : Interval dispositionTest 4067 4068 := by
  intro i hlo hhi
  have h : i = 4067 := by omega
  subst i
  exact disposition_at_4067


theorem disposition_interval_4068 : Interval dispositionTest 4068 4069 := by
  intro i hlo hhi
  have h : i = 4068 := by omega
  subst i
  exact disposition_at_4068


theorem disposition_interval_4069 : Interval dispositionTest 4069 4070 := by
  intro i hlo hhi
  have h : i = 4069 := by omega
  subst i
  exact disposition_at_4069


theorem disposition_interval_4070 : Interval dispositionTest 4070 4071 := by
  intro i hlo hhi
  have h : i = 4070 := by omega
  subst i
  exact disposition_at_4070


theorem disposition_interval_4071 : Interval dispositionTest 4071 4072 := by
  intro i hlo hhi
  have h : i = 4071 := by omega
  subst i
  exact disposition_at_4071


theorem disposition_interval_4072 : Interval dispositionTest 4072 4073 := by
  intro i hlo hhi
  have h : i = 4072 := by omega
  subst i
  exact disposition_at_4072


theorem disposition_interval_4073 : Interval dispositionTest 4073 4074 := by
  intro i hlo hhi
  have h : i = 4073 := by omega
  subst i
  exact disposition_at_4073


theorem disposition_interval_4074 : Interval dispositionTest 4074 4075 := by
  intro i hlo hhi
  have h : i = 4074 := by omega
  subst i
  exact disposition_at_4074


theorem disposition_interval_4075 : Interval dispositionTest 4075 4076 := by
  intro i hlo hhi
  have h : i = 4075 := by omega
  subst i
  exact disposition_at_4075


theorem disposition_interval_4076 : Interval dispositionTest 4076 4077 := by
  intro i hlo hhi
  have h : i = 4076 := by omega
  subst i
  exact disposition_at_4076


theorem disposition_interval_4077 : Interval dispositionTest 4077 4078 := by
  intro i hlo hhi
  have h : i = 4077 := by omega
  subst i
  exact disposition_at_4077


theorem disposition_interval_4078 : Interval dispositionTest 4078 4079 := by
  intro i hlo hhi
  have h : i = 4078 := by omega
  subst i
  exact disposition_at_4078


theorem disposition_interval_4079 : Interval dispositionTest 4079 4080 := by
  intro i hlo hhi
  have h : i = 4079 := by omega
  subst i
  exact disposition_at_4079


theorem disposition_interval_4080 : Interval dispositionTest 4080 4081 := by
  intro i hlo hhi
  have h : i = 4080 := by omega
  subst i
  exact disposition_at_4080


theorem disposition_interval_4081 : Interval dispositionTest 4081 4082 := by
  intro i hlo hhi
  have h : i = 4081 := by omega
  subst i
  exact disposition_at_4081


theorem disposition_interval_4082 : Interval dispositionTest 4082 4083 := by
  intro i hlo hhi
  have h : i = 4082 := by omega
  subst i
  exact disposition_at_4082


theorem disposition_interval_4083 : Interval dispositionTest 4083 4084 := by
  intro i hlo hhi
  have h : i = 4083 := by omega
  subst i
  exact disposition_at_4083

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
