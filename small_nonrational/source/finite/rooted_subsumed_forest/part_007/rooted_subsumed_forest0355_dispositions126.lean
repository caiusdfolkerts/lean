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
theorem disposition_at_4032 : dispositionTest 4032 = true := by decide +kernel

theorem disposition_at_4033 : dispositionTest 4033 = true := by decide +kernel

theorem disposition_at_4034 : dispositionTest 4034 = true := by decide +kernel


theorem disposition_at_4035 : dispositionTest 4035 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4035).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1097.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1097) = true
  rw [Nonrational.OldTerminalMatches.M017.r1097_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4036 : dispositionTest 4036 = true := by decide +kernel

theorem disposition_at_4037 : dispositionTest 4037 = true := by decide +kernel


theorem disposition_at_4038 : dispositionTest 4038 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4038).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1098.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1098) = true
  rw [Nonrational.OldTerminalMatches.M017.r1098_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4039 : dispositionTest 4039 = true := by decide +kernel

theorem disposition_at_4040 : dispositionTest 4040 = true := by decide +kernel

theorem disposition_at_4041 : dispositionTest 4041 = true := by decide +kernel

theorem disposition_at_4042 : dispositionTest 4042 = true := by decide +kernel

theorem disposition_at_4043 : dispositionTest 4043 = true := by decide +kernel

theorem disposition_at_4044 : dispositionTest 4044 = true := by decide +kernel

theorem disposition_at_4045 : dispositionTest 4045 = true := by decide +kernel

theorem disposition_at_4046 : dispositionTest 4046 = true := by decide +kernel

theorem disposition_at_4047 : dispositionTest 4047 = true := by decide +kernel

theorem disposition_at_4048 : dispositionTest 4048 = true := by decide +kernel

theorem disposition_at_4049 : dispositionTest 4049 = true := by decide +kernel

theorem disposition_at_4050 : dispositionTest 4050 = true := by decide +kernel

theorem disposition_at_4051 : dispositionTest 4051 = true := by decide +kernel

theorem disposition_at_4052 : dispositionTest 4052 = true := by decide +kernel

theorem disposition_at_4053 : dispositionTest 4053 = true := by decide +kernel

theorem disposition_at_4054 : dispositionTest 4054 = true := by decide +kernel

theorem disposition_at_4055 : dispositionTest 4055 = true := by decide +kernel

theorem disposition_at_4056 : dispositionTest 4056 = true := by decide +kernel

theorem disposition_at_4057 : dispositionTest 4057 = true := by decide +kernel

theorem disposition_at_4058 : dispositionTest 4058 = true := by decide +kernel


theorem disposition_at_4059 : dispositionTest 4059 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4059).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M017.r1099.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M017.r1099) = true
  rw [Nonrational.OldTerminalMatches.M017.r1099_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_4060 : dispositionTest 4060 = true := by decide +kernel

theorem disposition_at_4061 : dispositionTest 4061 = true := by decide +kernel

theorem disposition_at_4062 : dispositionTest 4062 = true := by decide +kernel

theorem disposition_at_4063 : dispositionTest 4063 = true := by decide +kernel

theorem disposition_interval_4032 : Interval dispositionTest 4032 4033 := by
  intro i hlo hhi
  have h : i = 4032 := by omega
  subst i
  exact disposition_at_4032


theorem disposition_interval_4033 : Interval dispositionTest 4033 4034 := by
  intro i hlo hhi
  have h : i = 4033 := by omega
  subst i
  exact disposition_at_4033


theorem disposition_interval_4034 : Interval dispositionTest 4034 4035 := by
  intro i hlo hhi
  have h : i = 4034 := by omega
  subst i
  exact disposition_at_4034


theorem disposition_interval_4035 : Interval dispositionTest 4035 4036 := by
  intro i hlo hhi
  have h : i = 4035 := by omega
  subst i
  exact disposition_at_4035


theorem disposition_interval_4036 : Interval dispositionTest 4036 4037 := by
  intro i hlo hhi
  have h : i = 4036 := by omega
  subst i
  exact disposition_at_4036


theorem disposition_interval_4037 : Interval dispositionTest 4037 4038 := by
  intro i hlo hhi
  have h : i = 4037 := by omega
  subst i
  exact disposition_at_4037


theorem disposition_interval_4038 : Interval dispositionTest 4038 4039 := by
  intro i hlo hhi
  have h : i = 4038 := by omega
  subst i
  exact disposition_at_4038


theorem disposition_interval_4039 : Interval dispositionTest 4039 4040 := by
  intro i hlo hhi
  have h : i = 4039 := by omega
  subst i
  exact disposition_at_4039


theorem disposition_interval_4040 : Interval dispositionTest 4040 4041 := by
  intro i hlo hhi
  have h : i = 4040 := by omega
  subst i
  exact disposition_at_4040


theorem disposition_interval_4041 : Interval dispositionTest 4041 4042 := by
  intro i hlo hhi
  have h : i = 4041 := by omega
  subst i
  exact disposition_at_4041


theorem disposition_interval_4042 : Interval dispositionTest 4042 4043 := by
  intro i hlo hhi
  have h : i = 4042 := by omega
  subst i
  exact disposition_at_4042


theorem disposition_interval_4043 : Interval dispositionTest 4043 4044 := by
  intro i hlo hhi
  have h : i = 4043 := by omega
  subst i
  exact disposition_at_4043


theorem disposition_interval_4044 : Interval dispositionTest 4044 4045 := by
  intro i hlo hhi
  have h : i = 4044 := by omega
  subst i
  exact disposition_at_4044


theorem disposition_interval_4045 : Interval dispositionTest 4045 4046 := by
  intro i hlo hhi
  have h : i = 4045 := by omega
  subst i
  exact disposition_at_4045


theorem disposition_interval_4046 : Interval dispositionTest 4046 4047 := by
  intro i hlo hhi
  have h : i = 4046 := by omega
  subst i
  exact disposition_at_4046


theorem disposition_interval_4047 : Interval dispositionTest 4047 4048 := by
  intro i hlo hhi
  have h : i = 4047 := by omega
  subst i
  exact disposition_at_4047


theorem disposition_interval_4048 : Interval dispositionTest 4048 4049 := by
  intro i hlo hhi
  have h : i = 4048 := by omega
  subst i
  exact disposition_at_4048


theorem disposition_interval_4049 : Interval dispositionTest 4049 4050 := by
  intro i hlo hhi
  have h : i = 4049 := by omega
  subst i
  exact disposition_at_4049


theorem disposition_interval_4050 : Interval dispositionTest 4050 4051 := by
  intro i hlo hhi
  have h : i = 4050 := by omega
  subst i
  exact disposition_at_4050


theorem disposition_interval_4051 : Interval dispositionTest 4051 4052 := by
  intro i hlo hhi
  have h : i = 4051 := by omega
  subst i
  exact disposition_at_4051


theorem disposition_interval_4052 : Interval dispositionTest 4052 4053 := by
  intro i hlo hhi
  have h : i = 4052 := by omega
  subst i
  exact disposition_at_4052


theorem disposition_interval_4053 : Interval dispositionTest 4053 4054 := by
  intro i hlo hhi
  have h : i = 4053 := by omega
  subst i
  exact disposition_at_4053


theorem disposition_interval_4054 : Interval dispositionTest 4054 4055 := by
  intro i hlo hhi
  have h : i = 4054 := by omega
  subst i
  exact disposition_at_4054


theorem disposition_interval_4055 : Interval dispositionTest 4055 4056 := by
  intro i hlo hhi
  have h : i = 4055 := by omega
  subst i
  exact disposition_at_4055


theorem disposition_interval_4056 : Interval dispositionTest 4056 4057 := by
  intro i hlo hhi
  have h : i = 4056 := by omega
  subst i
  exact disposition_at_4056


theorem disposition_interval_4057 : Interval dispositionTest 4057 4058 := by
  intro i hlo hhi
  have h : i = 4057 := by omega
  subst i
  exact disposition_at_4057


theorem disposition_interval_4058 : Interval dispositionTest 4058 4059 := by
  intro i hlo hhi
  have h : i = 4058 := by omega
  subst i
  exact disposition_at_4058


theorem disposition_interval_4059 : Interval dispositionTest 4059 4060 := by
  intro i hlo hhi
  have h : i = 4059 := by omega
  subst i
  exact disposition_at_4059


theorem disposition_interval_4060 : Interval dispositionTest 4060 4061 := by
  intro i hlo hhi
  have h : i = 4060 := by omega
  subst i
  exact disposition_at_4060


theorem disposition_interval_4061 : Interval dispositionTest 4061 4062 := by
  intro i hlo hhi
  have h : i = 4061 := by omega
  subst i
  exact disposition_at_4061


theorem disposition_interval_4062 : Interval dispositionTest 4062 4063 := by
  intro i hlo hhi
  have h : i = 4062 := by omega
  subst i
  exact disposition_at_4062


theorem disposition_interval_4063 : Interval dispositionTest 4063 4064 := by
  intro i hlo hhi
  have h : i = 4063 := by omega
  subst i
  exact disposition_at_4063

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
