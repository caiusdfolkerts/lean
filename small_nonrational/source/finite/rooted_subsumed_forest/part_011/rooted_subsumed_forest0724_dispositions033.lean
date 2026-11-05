module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_1056 : dispositionTest 1056 = true := by decide +kernel

theorem disposition_at_1057 : dispositionTest 1057 = true := by decide +kernel

theorem disposition_at_1058 : dispositionTest 1058 = true := by decide +kernel

theorem disposition_at_1059 : dispositionTest 1059 = true := by decide +kernel

theorem disposition_at_1060 : dispositionTest 1060 = true := by decide +kernel

theorem disposition_at_1061 : dispositionTest 1061 = true := by decide +kernel

theorem disposition_at_1062 : dispositionTest 1062 = true := by decide +kernel

theorem disposition_at_1063 : dispositionTest 1063 = true := by decide +kernel

theorem disposition_at_1064 : dispositionTest 1064 = true := by decide +kernel

theorem disposition_at_1065 : dispositionTest 1065 = true := by decide +kernel

theorem disposition_at_1066 : dispositionTest 1066 = true := by decide +kernel

theorem disposition_at_1067 : dispositionTest 1067 = true := by decide +kernel

theorem disposition_at_1068 : dispositionTest 1068 = true := by decide +kernel

theorem disposition_at_1069 : dispositionTest 1069 = true := by decide +kernel

theorem disposition_at_1070 : dispositionTest 1070 = true := by decide +kernel

theorem disposition_at_1071 : dispositionTest 1071 = true := by decide +kernel

theorem disposition_at_1072 : dispositionTest 1072 = true := by decide +kernel

theorem disposition_at_1073 : dispositionTest 1073 = true := by decide +kernel

theorem disposition_at_1074 : dispositionTest 1074 = true := by decide +kernel

theorem disposition_at_1075 : dispositionTest 1075 = true := by decide +kernel

theorem disposition_at_1076 : dispositionTest 1076 = true := by decide +kernel

theorem disposition_at_1077 : dispositionTest 1077 = true := by decide +kernel

theorem disposition_at_1078 : dispositionTest 1078 = true := by decide +kernel

theorem disposition_at_1079 : dispositionTest 1079 = true := by decide +kernel

theorem disposition_at_1080 : dispositionTest 1080 = true := by decide +kernel

theorem disposition_at_1081 : dispositionTest 1081 = true := by decide +kernel

theorem disposition_at_1082 : dispositionTest 1082 = true := by decide +kernel

theorem disposition_at_1083 : dispositionTest 1083 = true := by decide +kernel

theorem disposition_at_1084 : dispositionTest 1084 = true := by decide +kernel

theorem disposition_at_1085 : dispositionTest 1085 = true := by decide +kernel

theorem disposition_at_1086 : dispositionTest 1086 = true := by decide +kernel

theorem disposition_at_1087 : dispositionTest 1087 = true := by decide +kernel

theorem disposition_interval_1056 : Interval dispositionTest 1056 1057 := by
  intro i hlo hhi
  have h : i = 1056 := by omega
  subst i
  exact disposition_at_1056


theorem disposition_interval_1057 : Interval dispositionTest 1057 1058 := by
  intro i hlo hhi
  have h : i = 1057 := by omega
  subst i
  exact disposition_at_1057


theorem disposition_interval_1058 : Interval dispositionTest 1058 1059 := by
  intro i hlo hhi
  have h : i = 1058 := by omega
  subst i
  exact disposition_at_1058


theorem disposition_interval_1059 : Interval dispositionTest 1059 1060 := by
  intro i hlo hhi
  have h : i = 1059 := by omega
  subst i
  exact disposition_at_1059


theorem disposition_interval_1060 : Interval dispositionTest 1060 1061 := by
  intro i hlo hhi
  have h : i = 1060 := by omega
  subst i
  exact disposition_at_1060


theorem disposition_interval_1061 : Interval dispositionTest 1061 1062 := by
  intro i hlo hhi
  have h : i = 1061 := by omega
  subst i
  exact disposition_at_1061


theorem disposition_interval_1062 : Interval dispositionTest 1062 1063 := by
  intro i hlo hhi
  have h : i = 1062 := by omega
  subst i
  exact disposition_at_1062


theorem disposition_interval_1063 : Interval dispositionTest 1063 1064 := by
  intro i hlo hhi
  have h : i = 1063 := by omega
  subst i
  exact disposition_at_1063


theorem disposition_interval_1064 : Interval dispositionTest 1064 1065 := by
  intro i hlo hhi
  have h : i = 1064 := by omega
  subst i
  exact disposition_at_1064


theorem disposition_interval_1065 : Interval dispositionTest 1065 1066 := by
  intro i hlo hhi
  have h : i = 1065 := by omega
  subst i
  exact disposition_at_1065


theorem disposition_interval_1066 : Interval dispositionTest 1066 1067 := by
  intro i hlo hhi
  have h : i = 1066 := by omega
  subst i
  exact disposition_at_1066


theorem disposition_interval_1067 : Interval dispositionTest 1067 1068 := by
  intro i hlo hhi
  have h : i = 1067 := by omega
  subst i
  exact disposition_at_1067


theorem disposition_interval_1068 : Interval dispositionTest 1068 1069 := by
  intro i hlo hhi
  have h : i = 1068 := by omega
  subst i
  exact disposition_at_1068


theorem disposition_interval_1069 : Interval dispositionTest 1069 1070 := by
  intro i hlo hhi
  have h : i = 1069 := by omega
  subst i
  exact disposition_at_1069


theorem disposition_interval_1070 : Interval dispositionTest 1070 1071 := by
  intro i hlo hhi
  have h : i = 1070 := by omega
  subst i
  exact disposition_at_1070


theorem disposition_interval_1071 : Interval dispositionTest 1071 1072 := by
  intro i hlo hhi
  have h : i = 1071 := by omega
  subst i
  exact disposition_at_1071


theorem disposition_interval_1072 : Interval dispositionTest 1072 1073 := by
  intro i hlo hhi
  have h : i = 1072 := by omega
  subst i
  exact disposition_at_1072


theorem disposition_interval_1073 : Interval dispositionTest 1073 1074 := by
  intro i hlo hhi
  have h : i = 1073 := by omega
  subst i
  exact disposition_at_1073


theorem disposition_interval_1074 : Interval dispositionTest 1074 1075 := by
  intro i hlo hhi
  have h : i = 1074 := by omega
  subst i
  exact disposition_at_1074


theorem disposition_interval_1075 : Interval dispositionTest 1075 1076 := by
  intro i hlo hhi
  have h : i = 1075 := by omega
  subst i
  exact disposition_at_1075


theorem disposition_interval_1076 : Interval dispositionTest 1076 1077 := by
  intro i hlo hhi
  have h : i = 1076 := by omega
  subst i
  exact disposition_at_1076


theorem disposition_interval_1077 : Interval dispositionTest 1077 1078 := by
  intro i hlo hhi
  have h : i = 1077 := by omega
  subst i
  exact disposition_at_1077


theorem disposition_interval_1078 : Interval dispositionTest 1078 1079 := by
  intro i hlo hhi
  have h : i = 1078 := by omega
  subst i
  exact disposition_at_1078


theorem disposition_interval_1079 : Interval dispositionTest 1079 1080 := by
  intro i hlo hhi
  have h : i = 1079 := by omega
  subst i
  exact disposition_at_1079


theorem disposition_interval_1080 : Interval dispositionTest 1080 1081 := by
  intro i hlo hhi
  have h : i = 1080 := by omega
  subst i
  exact disposition_at_1080


theorem disposition_interval_1081 : Interval dispositionTest 1081 1082 := by
  intro i hlo hhi
  have h : i = 1081 := by omega
  subst i
  exact disposition_at_1081


theorem disposition_interval_1082 : Interval dispositionTest 1082 1083 := by
  intro i hlo hhi
  have h : i = 1082 := by omega
  subst i
  exact disposition_at_1082


theorem disposition_interval_1083 : Interval dispositionTest 1083 1084 := by
  intro i hlo hhi
  have h : i = 1083 := by omega
  subst i
  exact disposition_at_1083


theorem disposition_interval_1084 : Interval dispositionTest 1084 1085 := by
  intro i hlo hhi
  have h : i = 1084 := by omega
  subst i
  exact disposition_at_1084


theorem disposition_interval_1085 : Interval dispositionTest 1085 1086 := by
  intro i hlo hhi
  have h : i = 1085 := by omega
  subst i
  exact disposition_at_1085


theorem disposition_interval_1086 : Interval dispositionTest 1086 1087 := by
  intro i hlo hhi
  have h : i = 1086 := by omega
  subst i
  exact disposition_at_1086


theorem disposition_interval_1087 : Interval dispositionTest 1087 1088 := by
  intro i hlo hhi
  have h : i = 1087 := by omega
  subst i
  exact disposition_at_1087

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
