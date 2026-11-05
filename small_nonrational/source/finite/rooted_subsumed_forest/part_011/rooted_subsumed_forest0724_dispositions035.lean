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
theorem disposition_at_1120 : dispositionTest 1120 = true := by decide +kernel

theorem disposition_at_1121 : dispositionTest 1121 = true := by decide +kernel

theorem disposition_at_1122 : dispositionTest 1122 = true := by decide +kernel

theorem disposition_at_1123 : dispositionTest 1123 = true := by decide +kernel

theorem disposition_at_1124 : dispositionTest 1124 = true := by decide +kernel

theorem disposition_at_1125 : dispositionTest 1125 = true := by decide +kernel

theorem disposition_at_1126 : dispositionTest 1126 = true := by decide +kernel

theorem disposition_at_1127 : dispositionTest 1127 = true := by decide +kernel

theorem disposition_at_1128 : dispositionTest 1128 = true := by decide +kernel

theorem disposition_at_1129 : dispositionTest 1129 = true := by decide +kernel

theorem disposition_at_1130 : dispositionTest 1130 = true := by decide +kernel

theorem disposition_at_1131 : dispositionTest 1131 = true := by decide +kernel

theorem disposition_at_1132 : dispositionTest 1132 = true := by decide +kernel

theorem disposition_at_1133 : dispositionTest 1133 = true := by decide +kernel

theorem disposition_at_1134 : dispositionTest 1134 = true := by decide +kernel

theorem disposition_at_1135 : dispositionTest 1135 = true := by decide +kernel

theorem disposition_at_1136 : dispositionTest 1136 = true := by decide +kernel

theorem disposition_at_1137 : dispositionTest 1137 = true := by decide +kernel

theorem disposition_at_1138 : dispositionTest 1138 = true := by decide +kernel

theorem disposition_at_1139 : dispositionTest 1139 = true := by decide +kernel

theorem disposition_at_1140 : dispositionTest 1140 = true := by decide +kernel

theorem disposition_at_1141 : dispositionTest 1141 = true := by decide +kernel

theorem disposition_at_1142 : dispositionTest 1142 = true := by decide +kernel

theorem disposition_at_1143 : dispositionTest 1143 = true := by decide +kernel

theorem disposition_at_1144 : dispositionTest 1144 = true := by decide +kernel

theorem disposition_at_1145 : dispositionTest 1145 = true := by decide +kernel

theorem disposition_at_1146 : dispositionTest 1146 = true := by decide +kernel

theorem disposition_at_1147 : dispositionTest 1147 = true := by decide +kernel

theorem disposition_at_1148 : dispositionTest 1148 = true := by decide +kernel

theorem disposition_at_1149 : dispositionTest 1149 = true := by decide +kernel

theorem disposition_at_1150 : dispositionTest 1150 = true := by decide +kernel

theorem disposition_at_1151 : dispositionTest 1151 = true := by decide +kernel

theorem disposition_interval_1120 : Interval dispositionTest 1120 1121 := by
  intro i hlo hhi
  have h : i = 1120 := by omega
  subst i
  exact disposition_at_1120


theorem disposition_interval_1121 : Interval dispositionTest 1121 1122 := by
  intro i hlo hhi
  have h : i = 1121 := by omega
  subst i
  exact disposition_at_1121


theorem disposition_interval_1122 : Interval dispositionTest 1122 1123 := by
  intro i hlo hhi
  have h : i = 1122 := by omega
  subst i
  exact disposition_at_1122


theorem disposition_interval_1123 : Interval dispositionTest 1123 1124 := by
  intro i hlo hhi
  have h : i = 1123 := by omega
  subst i
  exact disposition_at_1123


theorem disposition_interval_1124 : Interval dispositionTest 1124 1125 := by
  intro i hlo hhi
  have h : i = 1124 := by omega
  subst i
  exact disposition_at_1124


theorem disposition_interval_1125 : Interval dispositionTest 1125 1126 := by
  intro i hlo hhi
  have h : i = 1125 := by omega
  subst i
  exact disposition_at_1125


theorem disposition_interval_1126 : Interval dispositionTest 1126 1127 := by
  intro i hlo hhi
  have h : i = 1126 := by omega
  subst i
  exact disposition_at_1126


theorem disposition_interval_1127 : Interval dispositionTest 1127 1128 := by
  intro i hlo hhi
  have h : i = 1127 := by omega
  subst i
  exact disposition_at_1127


theorem disposition_interval_1128 : Interval dispositionTest 1128 1129 := by
  intro i hlo hhi
  have h : i = 1128 := by omega
  subst i
  exact disposition_at_1128


theorem disposition_interval_1129 : Interval dispositionTest 1129 1130 := by
  intro i hlo hhi
  have h : i = 1129 := by omega
  subst i
  exact disposition_at_1129


theorem disposition_interval_1130 : Interval dispositionTest 1130 1131 := by
  intro i hlo hhi
  have h : i = 1130 := by omega
  subst i
  exact disposition_at_1130


theorem disposition_interval_1131 : Interval dispositionTest 1131 1132 := by
  intro i hlo hhi
  have h : i = 1131 := by omega
  subst i
  exact disposition_at_1131


theorem disposition_interval_1132 : Interval dispositionTest 1132 1133 := by
  intro i hlo hhi
  have h : i = 1132 := by omega
  subst i
  exact disposition_at_1132


theorem disposition_interval_1133 : Interval dispositionTest 1133 1134 := by
  intro i hlo hhi
  have h : i = 1133 := by omega
  subst i
  exact disposition_at_1133


theorem disposition_interval_1134 : Interval dispositionTest 1134 1135 := by
  intro i hlo hhi
  have h : i = 1134 := by omega
  subst i
  exact disposition_at_1134


theorem disposition_interval_1135 : Interval dispositionTest 1135 1136 := by
  intro i hlo hhi
  have h : i = 1135 := by omega
  subst i
  exact disposition_at_1135


theorem disposition_interval_1136 : Interval dispositionTest 1136 1137 := by
  intro i hlo hhi
  have h : i = 1136 := by omega
  subst i
  exact disposition_at_1136


theorem disposition_interval_1137 : Interval dispositionTest 1137 1138 := by
  intro i hlo hhi
  have h : i = 1137 := by omega
  subst i
  exact disposition_at_1137


theorem disposition_interval_1138 : Interval dispositionTest 1138 1139 := by
  intro i hlo hhi
  have h : i = 1138 := by omega
  subst i
  exact disposition_at_1138


theorem disposition_interval_1139 : Interval dispositionTest 1139 1140 := by
  intro i hlo hhi
  have h : i = 1139 := by omega
  subst i
  exact disposition_at_1139


theorem disposition_interval_1140 : Interval dispositionTest 1140 1141 := by
  intro i hlo hhi
  have h : i = 1140 := by omega
  subst i
  exact disposition_at_1140


theorem disposition_interval_1141 : Interval dispositionTest 1141 1142 := by
  intro i hlo hhi
  have h : i = 1141 := by omega
  subst i
  exact disposition_at_1141


theorem disposition_interval_1142 : Interval dispositionTest 1142 1143 := by
  intro i hlo hhi
  have h : i = 1142 := by omega
  subst i
  exact disposition_at_1142


theorem disposition_interval_1143 : Interval dispositionTest 1143 1144 := by
  intro i hlo hhi
  have h : i = 1143 := by omega
  subst i
  exact disposition_at_1143


theorem disposition_interval_1144 : Interval dispositionTest 1144 1145 := by
  intro i hlo hhi
  have h : i = 1144 := by omega
  subst i
  exact disposition_at_1144


theorem disposition_interval_1145 : Interval dispositionTest 1145 1146 := by
  intro i hlo hhi
  have h : i = 1145 := by omega
  subst i
  exact disposition_at_1145


theorem disposition_interval_1146 : Interval dispositionTest 1146 1147 := by
  intro i hlo hhi
  have h : i = 1146 := by omega
  subst i
  exact disposition_at_1146


theorem disposition_interval_1147 : Interval dispositionTest 1147 1148 := by
  intro i hlo hhi
  have h : i = 1147 := by omega
  subst i
  exact disposition_at_1147


theorem disposition_interval_1148 : Interval dispositionTest 1148 1149 := by
  intro i hlo hhi
  have h : i = 1148 := by omega
  subst i
  exact disposition_at_1148


theorem disposition_interval_1149 : Interval dispositionTest 1149 1150 := by
  intro i hlo hhi
  have h : i = 1149 := by omega
  subst i
  exact disposition_at_1149


theorem disposition_interval_1150 : Interval dispositionTest 1150 1151 := by
  intro i hlo hhi
  have h : i = 1150 := by omega
  subst i
  exact disposition_at_1150


theorem disposition_interval_1151 : Interval dispositionTest 1151 1152 := by
  intro i hlo hhi
  have h : i = 1151 := by omega
  subst i
  exact disposition_at_1151

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
