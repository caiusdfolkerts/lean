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
theorem disposition_at_4000 : dispositionTest 4000 = true := by decide +kernel

theorem disposition_at_4001 : dispositionTest 4001 = true := by decide +kernel

theorem disposition_at_4002 : dispositionTest 4002 = true := by decide +kernel

theorem disposition_at_4003 : dispositionTest 4003 = true := by decide +kernel

theorem disposition_at_4004 : dispositionTest 4004 = true := by decide +kernel

theorem disposition_at_4005 : dispositionTest 4005 = true := by decide +kernel

theorem disposition_at_4006 : dispositionTest 4006 = true := by decide +kernel

theorem disposition_at_4007 : dispositionTest 4007 = true := by decide +kernel

theorem disposition_at_4008 : dispositionTest 4008 = true := by decide +kernel

theorem disposition_at_4009 : dispositionTest 4009 = true := by decide +kernel

theorem disposition_at_4010 : dispositionTest 4010 = true := by decide +kernel

theorem disposition_at_4011 : dispositionTest 4011 = true := by decide +kernel

theorem disposition_at_4012 : dispositionTest 4012 = true := by decide +kernel

theorem disposition_at_4013 : dispositionTest 4013 = true := by decide +kernel

theorem disposition_at_4014 : dispositionTest 4014 = true := by decide +kernel

theorem disposition_at_4015 : dispositionTest 4015 = true := by decide +kernel

theorem disposition_at_4016 : dispositionTest 4016 = true := by decide +kernel

theorem disposition_at_4017 : dispositionTest 4017 = true := by decide +kernel

theorem disposition_at_4018 : dispositionTest 4018 = true := by decide +kernel

theorem disposition_at_4019 : dispositionTest 4019 = true := by decide +kernel

theorem disposition_at_4020 : dispositionTest 4020 = true := by decide +kernel

theorem disposition_at_4021 : dispositionTest 4021 = true := by decide +kernel

theorem disposition_at_4022 : dispositionTest 4022 = true := by decide +kernel

theorem disposition_at_4023 : dispositionTest 4023 = true := by decide +kernel

theorem disposition_at_4024 : dispositionTest 4024 = true := by decide +kernel

theorem disposition_at_4025 : dispositionTest 4025 = true := by decide +kernel

theorem disposition_at_4026 : dispositionTest 4026 = true := by decide +kernel

theorem disposition_at_4027 : dispositionTest 4027 = true := by decide +kernel

theorem disposition_at_4028 : dispositionTest 4028 = true := by decide +kernel

theorem disposition_at_4029 : dispositionTest 4029 = true := by decide +kernel

theorem disposition_at_4030 : dispositionTest 4030 = true := by decide +kernel

theorem disposition_at_4031 : dispositionTest 4031 = true := by decide +kernel

theorem disposition_interval_4000 : Interval dispositionTest 4000 4001 := by
  intro i hlo hhi
  have h : i = 4000 := by omega
  subst i
  exact disposition_at_4000


theorem disposition_interval_4001 : Interval dispositionTest 4001 4002 := by
  intro i hlo hhi
  have h : i = 4001 := by omega
  subst i
  exact disposition_at_4001


theorem disposition_interval_4002 : Interval dispositionTest 4002 4003 := by
  intro i hlo hhi
  have h : i = 4002 := by omega
  subst i
  exact disposition_at_4002


theorem disposition_interval_4003 : Interval dispositionTest 4003 4004 := by
  intro i hlo hhi
  have h : i = 4003 := by omega
  subst i
  exact disposition_at_4003


theorem disposition_interval_4004 : Interval dispositionTest 4004 4005 := by
  intro i hlo hhi
  have h : i = 4004 := by omega
  subst i
  exact disposition_at_4004


theorem disposition_interval_4005 : Interval dispositionTest 4005 4006 := by
  intro i hlo hhi
  have h : i = 4005 := by omega
  subst i
  exact disposition_at_4005


theorem disposition_interval_4006 : Interval dispositionTest 4006 4007 := by
  intro i hlo hhi
  have h : i = 4006 := by omega
  subst i
  exact disposition_at_4006


theorem disposition_interval_4007 : Interval dispositionTest 4007 4008 := by
  intro i hlo hhi
  have h : i = 4007 := by omega
  subst i
  exact disposition_at_4007


theorem disposition_interval_4008 : Interval dispositionTest 4008 4009 := by
  intro i hlo hhi
  have h : i = 4008 := by omega
  subst i
  exact disposition_at_4008


theorem disposition_interval_4009 : Interval dispositionTest 4009 4010 := by
  intro i hlo hhi
  have h : i = 4009 := by omega
  subst i
  exact disposition_at_4009


theorem disposition_interval_4010 : Interval dispositionTest 4010 4011 := by
  intro i hlo hhi
  have h : i = 4010 := by omega
  subst i
  exact disposition_at_4010


theorem disposition_interval_4011 : Interval dispositionTest 4011 4012 := by
  intro i hlo hhi
  have h : i = 4011 := by omega
  subst i
  exact disposition_at_4011


theorem disposition_interval_4012 : Interval dispositionTest 4012 4013 := by
  intro i hlo hhi
  have h : i = 4012 := by omega
  subst i
  exact disposition_at_4012


theorem disposition_interval_4013 : Interval dispositionTest 4013 4014 := by
  intro i hlo hhi
  have h : i = 4013 := by omega
  subst i
  exact disposition_at_4013


theorem disposition_interval_4014 : Interval dispositionTest 4014 4015 := by
  intro i hlo hhi
  have h : i = 4014 := by omega
  subst i
  exact disposition_at_4014


theorem disposition_interval_4015 : Interval dispositionTest 4015 4016 := by
  intro i hlo hhi
  have h : i = 4015 := by omega
  subst i
  exact disposition_at_4015


theorem disposition_interval_4016 : Interval dispositionTest 4016 4017 := by
  intro i hlo hhi
  have h : i = 4016 := by omega
  subst i
  exact disposition_at_4016


theorem disposition_interval_4017 : Interval dispositionTest 4017 4018 := by
  intro i hlo hhi
  have h : i = 4017 := by omega
  subst i
  exact disposition_at_4017


theorem disposition_interval_4018 : Interval dispositionTest 4018 4019 := by
  intro i hlo hhi
  have h : i = 4018 := by omega
  subst i
  exact disposition_at_4018


theorem disposition_interval_4019 : Interval dispositionTest 4019 4020 := by
  intro i hlo hhi
  have h : i = 4019 := by omega
  subst i
  exact disposition_at_4019


theorem disposition_interval_4020 : Interval dispositionTest 4020 4021 := by
  intro i hlo hhi
  have h : i = 4020 := by omega
  subst i
  exact disposition_at_4020


theorem disposition_interval_4021 : Interval dispositionTest 4021 4022 := by
  intro i hlo hhi
  have h : i = 4021 := by omega
  subst i
  exact disposition_at_4021


theorem disposition_interval_4022 : Interval dispositionTest 4022 4023 := by
  intro i hlo hhi
  have h : i = 4022 := by omega
  subst i
  exact disposition_at_4022


theorem disposition_interval_4023 : Interval dispositionTest 4023 4024 := by
  intro i hlo hhi
  have h : i = 4023 := by omega
  subst i
  exact disposition_at_4023


theorem disposition_interval_4024 : Interval dispositionTest 4024 4025 := by
  intro i hlo hhi
  have h : i = 4024 := by omega
  subst i
  exact disposition_at_4024


theorem disposition_interval_4025 : Interval dispositionTest 4025 4026 := by
  intro i hlo hhi
  have h : i = 4025 := by omega
  subst i
  exact disposition_at_4025


theorem disposition_interval_4026 : Interval dispositionTest 4026 4027 := by
  intro i hlo hhi
  have h : i = 4026 := by omega
  subst i
  exact disposition_at_4026


theorem disposition_interval_4027 : Interval dispositionTest 4027 4028 := by
  intro i hlo hhi
  have h : i = 4027 := by omega
  subst i
  exact disposition_at_4027


theorem disposition_interval_4028 : Interval dispositionTest 4028 4029 := by
  intro i hlo hhi
  have h : i = 4028 := by omega
  subst i
  exact disposition_at_4028


theorem disposition_interval_4029 : Interval dispositionTest 4029 4030 := by
  intro i hlo hhi
  have h : i = 4029 := by omega
  subst i
  exact disposition_at_4029


theorem disposition_interval_4030 : Interval dispositionTest 4030 4031 := by
  intro i hlo hhi
  have h : i = 4030 := by omega
  subst i
  exact disposition_at_4030


theorem disposition_interval_4031 : Interval dispositionTest 4031 4032 := by
  intro i hlo hhi
  have h : i = 4031 := by omega
  subst i
  exact disposition_at_4031

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
