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
theorem disposition_at_1088 : dispositionTest 1088 = true := by decide +kernel

theorem disposition_at_1089 : dispositionTest 1089 = true := by decide +kernel

theorem disposition_at_1090 : dispositionTest 1090 = true := by decide +kernel

theorem disposition_at_1091 : dispositionTest 1091 = true := by decide +kernel

theorem disposition_at_1092 : dispositionTest 1092 = true := by decide +kernel

theorem disposition_at_1093 : dispositionTest 1093 = true := by decide +kernel

theorem disposition_at_1094 : dispositionTest 1094 = true := by decide +kernel

theorem disposition_at_1095 : dispositionTest 1095 = true := by decide +kernel

theorem disposition_at_1096 : dispositionTest 1096 = true := by decide +kernel

theorem disposition_at_1097 : dispositionTest 1097 = true := by decide +kernel

theorem disposition_at_1098 : dispositionTest 1098 = true := by decide +kernel

theorem disposition_at_1099 : dispositionTest 1099 = true := by decide +kernel

theorem disposition_at_1100 : dispositionTest 1100 = true := by decide +kernel

theorem disposition_at_1101 : dispositionTest 1101 = true := by decide +kernel

theorem disposition_at_1102 : dispositionTest 1102 = true := by decide +kernel

theorem disposition_at_1103 : dispositionTest 1103 = true := by decide +kernel

theorem disposition_at_1104 : dispositionTest 1104 = true := by decide +kernel

theorem disposition_at_1105 : dispositionTest 1105 = true := by decide +kernel

theorem disposition_at_1106 : dispositionTest 1106 = true := by decide +kernel

theorem disposition_at_1107 : dispositionTest 1107 = true := by decide +kernel

theorem disposition_at_1108 : dispositionTest 1108 = true := by decide +kernel

theorem disposition_at_1109 : dispositionTest 1109 = true := by decide +kernel

theorem disposition_at_1110 : dispositionTest 1110 = true := by decide +kernel

theorem disposition_at_1111 : dispositionTest 1111 = true := by decide +kernel

theorem disposition_at_1112 : dispositionTest 1112 = true := by decide +kernel

theorem disposition_at_1113 : dispositionTest 1113 = true := by decide +kernel

theorem disposition_at_1114 : dispositionTest 1114 = true := by decide +kernel

theorem disposition_at_1115 : dispositionTest 1115 = true := by decide +kernel

theorem disposition_at_1116 : dispositionTest 1116 = true := by decide +kernel

theorem disposition_at_1117 : dispositionTest 1117 = true := by decide +kernel

theorem disposition_at_1118 : dispositionTest 1118 = true := by decide +kernel

theorem disposition_at_1119 : dispositionTest 1119 = true := by decide +kernel

theorem disposition_interval_1088 : Interval dispositionTest 1088 1089 := by
  intro i hlo hhi
  have h : i = 1088 := by omega
  subst i
  exact disposition_at_1088


theorem disposition_interval_1089 : Interval dispositionTest 1089 1090 := by
  intro i hlo hhi
  have h : i = 1089 := by omega
  subst i
  exact disposition_at_1089


theorem disposition_interval_1090 : Interval dispositionTest 1090 1091 := by
  intro i hlo hhi
  have h : i = 1090 := by omega
  subst i
  exact disposition_at_1090


theorem disposition_interval_1091 : Interval dispositionTest 1091 1092 := by
  intro i hlo hhi
  have h : i = 1091 := by omega
  subst i
  exact disposition_at_1091


theorem disposition_interval_1092 : Interval dispositionTest 1092 1093 := by
  intro i hlo hhi
  have h : i = 1092 := by omega
  subst i
  exact disposition_at_1092


theorem disposition_interval_1093 : Interval dispositionTest 1093 1094 := by
  intro i hlo hhi
  have h : i = 1093 := by omega
  subst i
  exact disposition_at_1093


theorem disposition_interval_1094 : Interval dispositionTest 1094 1095 := by
  intro i hlo hhi
  have h : i = 1094 := by omega
  subst i
  exact disposition_at_1094


theorem disposition_interval_1095 : Interval dispositionTest 1095 1096 := by
  intro i hlo hhi
  have h : i = 1095 := by omega
  subst i
  exact disposition_at_1095


theorem disposition_interval_1096 : Interval dispositionTest 1096 1097 := by
  intro i hlo hhi
  have h : i = 1096 := by omega
  subst i
  exact disposition_at_1096


theorem disposition_interval_1097 : Interval dispositionTest 1097 1098 := by
  intro i hlo hhi
  have h : i = 1097 := by omega
  subst i
  exact disposition_at_1097


theorem disposition_interval_1098 : Interval dispositionTest 1098 1099 := by
  intro i hlo hhi
  have h : i = 1098 := by omega
  subst i
  exact disposition_at_1098


theorem disposition_interval_1099 : Interval dispositionTest 1099 1100 := by
  intro i hlo hhi
  have h : i = 1099 := by omega
  subst i
  exact disposition_at_1099


theorem disposition_interval_1100 : Interval dispositionTest 1100 1101 := by
  intro i hlo hhi
  have h : i = 1100 := by omega
  subst i
  exact disposition_at_1100


theorem disposition_interval_1101 : Interval dispositionTest 1101 1102 := by
  intro i hlo hhi
  have h : i = 1101 := by omega
  subst i
  exact disposition_at_1101


theorem disposition_interval_1102 : Interval dispositionTest 1102 1103 := by
  intro i hlo hhi
  have h : i = 1102 := by omega
  subst i
  exact disposition_at_1102


theorem disposition_interval_1103 : Interval dispositionTest 1103 1104 := by
  intro i hlo hhi
  have h : i = 1103 := by omega
  subst i
  exact disposition_at_1103


theorem disposition_interval_1104 : Interval dispositionTest 1104 1105 := by
  intro i hlo hhi
  have h : i = 1104 := by omega
  subst i
  exact disposition_at_1104


theorem disposition_interval_1105 : Interval dispositionTest 1105 1106 := by
  intro i hlo hhi
  have h : i = 1105 := by omega
  subst i
  exact disposition_at_1105


theorem disposition_interval_1106 : Interval dispositionTest 1106 1107 := by
  intro i hlo hhi
  have h : i = 1106 := by omega
  subst i
  exact disposition_at_1106


theorem disposition_interval_1107 : Interval dispositionTest 1107 1108 := by
  intro i hlo hhi
  have h : i = 1107 := by omega
  subst i
  exact disposition_at_1107


theorem disposition_interval_1108 : Interval dispositionTest 1108 1109 := by
  intro i hlo hhi
  have h : i = 1108 := by omega
  subst i
  exact disposition_at_1108


theorem disposition_interval_1109 : Interval dispositionTest 1109 1110 := by
  intro i hlo hhi
  have h : i = 1109 := by omega
  subst i
  exact disposition_at_1109


theorem disposition_interval_1110 : Interval dispositionTest 1110 1111 := by
  intro i hlo hhi
  have h : i = 1110 := by omega
  subst i
  exact disposition_at_1110


theorem disposition_interval_1111 : Interval dispositionTest 1111 1112 := by
  intro i hlo hhi
  have h : i = 1111 := by omega
  subst i
  exact disposition_at_1111


theorem disposition_interval_1112 : Interval dispositionTest 1112 1113 := by
  intro i hlo hhi
  have h : i = 1112 := by omega
  subst i
  exact disposition_at_1112


theorem disposition_interval_1113 : Interval dispositionTest 1113 1114 := by
  intro i hlo hhi
  have h : i = 1113 := by omega
  subst i
  exact disposition_at_1113


theorem disposition_interval_1114 : Interval dispositionTest 1114 1115 := by
  intro i hlo hhi
  have h : i = 1114 := by omega
  subst i
  exact disposition_at_1114


theorem disposition_interval_1115 : Interval dispositionTest 1115 1116 := by
  intro i hlo hhi
  have h : i = 1115 := by omega
  subst i
  exact disposition_at_1115


theorem disposition_interval_1116 : Interval dispositionTest 1116 1117 := by
  intro i hlo hhi
  have h : i = 1116 := by omega
  subst i
  exact disposition_at_1116


theorem disposition_interval_1117 : Interval dispositionTest 1117 1118 := by
  intro i hlo hhi
  have h : i = 1117 := by omega
  subst i
  exact disposition_at_1117


theorem disposition_interval_1118 : Interval dispositionTest 1118 1119 := by
  intro i hlo hhi
  have h : i = 1118 := by omega
  subst i
  exact disposition_at_1118


theorem disposition_interval_1119 : Interval dispositionTest 1119 1120 := by
  intro i hlo hhi
  have h : i = 1119 := by omega
  subst i
  exact disposition_at_1119

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
