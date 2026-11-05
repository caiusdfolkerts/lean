module
prelude
public import RootedSubsumedForest0708DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_1152 : dispositionTest 1152 = true := by decide +kernel

theorem disposition_at_1153 : dispositionTest 1153 = true := by decide +kernel

theorem disposition_at_1154 : dispositionTest 1154 = true := by decide +kernel

theorem disposition_at_1155 : dispositionTest 1155 = true := by decide +kernel

theorem disposition_at_1156 : dispositionTest 1156 = true := by decide +kernel

theorem disposition_at_1157 : dispositionTest 1157 = true := by decide +kernel

theorem disposition_at_1158 : dispositionTest 1158 = true := by decide +kernel

theorem disposition_at_1159 : dispositionTest 1159 = true := by decide +kernel

theorem disposition_at_1160 : dispositionTest 1160 = true := by decide +kernel

theorem disposition_at_1161 : dispositionTest 1161 = true := by decide +kernel

theorem disposition_at_1162 : dispositionTest 1162 = true := by decide +kernel

theorem disposition_at_1163 : dispositionTest 1163 = true := by decide +kernel

theorem disposition_at_1164 : dispositionTest 1164 = true := by decide +kernel

theorem disposition_at_1165 : dispositionTest 1165 = true := by decide +kernel

theorem disposition_at_1166 : dispositionTest 1166 = true := by decide +kernel

theorem disposition_at_1167 : dispositionTest 1167 = true := by decide +kernel

theorem disposition_at_1168 : dispositionTest 1168 = true := by decide +kernel

theorem disposition_at_1169 : dispositionTest 1169 = true := by decide +kernel

theorem disposition_at_1170 : dispositionTest 1170 = true := by decide +kernel

theorem disposition_at_1171 : dispositionTest 1171 = true := by decide +kernel

theorem disposition_at_1172 : dispositionTest 1172 = true := by decide +kernel

theorem disposition_at_1173 : dispositionTest 1173 = true := by decide +kernel

theorem disposition_at_1174 : dispositionTest 1174 = true := by decide +kernel

theorem disposition_at_1175 : dispositionTest 1175 = true := by decide +kernel

theorem disposition_at_1176 : dispositionTest 1176 = true := by decide +kernel

theorem disposition_at_1177 : dispositionTest 1177 = true := by decide +kernel

theorem disposition_at_1178 : dispositionTest 1178 = true := by decide +kernel

theorem disposition_at_1179 : dispositionTest 1179 = true := by decide +kernel

theorem disposition_at_1180 : dispositionTest 1180 = true := by decide +kernel

theorem disposition_at_1181 : dispositionTest 1181 = true := by decide +kernel

theorem disposition_at_1182 : dispositionTest 1182 = true := by decide +kernel

theorem disposition_at_1183 : dispositionTest 1183 = true := by decide +kernel

theorem disposition_interval_1152 : Interval dispositionTest 1152 1153 := by
  intro i hlo hhi
  have h : i = 1152 := by omega
  subst i
  exact disposition_at_1152


theorem disposition_interval_1153 : Interval dispositionTest 1153 1154 := by
  intro i hlo hhi
  have h : i = 1153 := by omega
  subst i
  exact disposition_at_1153


theorem disposition_interval_1154 : Interval dispositionTest 1154 1155 := by
  intro i hlo hhi
  have h : i = 1154 := by omega
  subst i
  exact disposition_at_1154


theorem disposition_interval_1155 : Interval dispositionTest 1155 1156 := by
  intro i hlo hhi
  have h : i = 1155 := by omega
  subst i
  exact disposition_at_1155


theorem disposition_interval_1156 : Interval dispositionTest 1156 1157 := by
  intro i hlo hhi
  have h : i = 1156 := by omega
  subst i
  exact disposition_at_1156


theorem disposition_interval_1157 : Interval dispositionTest 1157 1158 := by
  intro i hlo hhi
  have h : i = 1157 := by omega
  subst i
  exact disposition_at_1157


theorem disposition_interval_1158 : Interval dispositionTest 1158 1159 := by
  intro i hlo hhi
  have h : i = 1158 := by omega
  subst i
  exact disposition_at_1158


theorem disposition_interval_1159 : Interval dispositionTest 1159 1160 := by
  intro i hlo hhi
  have h : i = 1159 := by omega
  subst i
  exact disposition_at_1159


theorem disposition_interval_1160 : Interval dispositionTest 1160 1161 := by
  intro i hlo hhi
  have h : i = 1160 := by omega
  subst i
  exact disposition_at_1160


theorem disposition_interval_1161 : Interval dispositionTest 1161 1162 := by
  intro i hlo hhi
  have h : i = 1161 := by omega
  subst i
  exact disposition_at_1161


theorem disposition_interval_1162 : Interval dispositionTest 1162 1163 := by
  intro i hlo hhi
  have h : i = 1162 := by omega
  subst i
  exact disposition_at_1162


theorem disposition_interval_1163 : Interval dispositionTest 1163 1164 := by
  intro i hlo hhi
  have h : i = 1163 := by omega
  subst i
  exact disposition_at_1163


theorem disposition_interval_1164 : Interval dispositionTest 1164 1165 := by
  intro i hlo hhi
  have h : i = 1164 := by omega
  subst i
  exact disposition_at_1164


theorem disposition_interval_1165 : Interval dispositionTest 1165 1166 := by
  intro i hlo hhi
  have h : i = 1165 := by omega
  subst i
  exact disposition_at_1165


theorem disposition_interval_1166 : Interval dispositionTest 1166 1167 := by
  intro i hlo hhi
  have h : i = 1166 := by omega
  subst i
  exact disposition_at_1166


theorem disposition_interval_1167 : Interval dispositionTest 1167 1168 := by
  intro i hlo hhi
  have h : i = 1167 := by omega
  subst i
  exact disposition_at_1167


theorem disposition_interval_1168 : Interval dispositionTest 1168 1169 := by
  intro i hlo hhi
  have h : i = 1168 := by omega
  subst i
  exact disposition_at_1168


theorem disposition_interval_1169 : Interval dispositionTest 1169 1170 := by
  intro i hlo hhi
  have h : i = 1169 := by omega
  subst i
  exact disposition_at_1169


theorem disposition_interval_1170 : Interval dispositionTest 1170 1171 := by
  intro i hlo hhi
  have h : i = 1170 := by omega
  subst i
  exact disposition_at_1170


theorem disposition_interval_1171 : Interval dispositionTest 1171 1172 := by
  intro i hlo hhi
  have h : i = 1171 := by omega
  subst i
  exact disposition_at_1171


theorem disposition_interval_1172 : Interval dispositionTest 1172 1173 := by
  intro i hlo hhi
  have h : i = 1172 := by omega
  subst i
  exact disposition_at_1172


theorem disposition_interval_1173 : Interval dispositionTest 1173 1174 := by
  intro i hlo hhi
  have h : i = 1173 := by omega
  subst i
  exact disposition_at_1173


theorem disposition_interval_1174 : Interval dispositionTest 1174 1175 := by
  intro i hlo hhi
  have h : i = 1174 := by omega
  subst i
  exact disposition_at_1174


theorem disposition_interval_1175 : Interval dispositionTest 1175 1176 := by
  intro i hlo hhi
  have h : i = 1175 := by omega
  subst i
  exact disposition_at_1175


theorem disposition_interval_1176 : Interval dispositionTest 1176 1177 := by
  intro i hlo hhi
  have h : i = 1176 := by omega
  subst i
  exact disposition_at_1176


theorem disposition_interval_1177 : Interval dispositionTest 1177 1178 := by
  intro i hlo hhi
  have h : i = 1177 := by omega
  subst i
  exact disposition_at_1177


theorem disposition_interval_1178 : Interval dispositionTest 1178 1179 := by
  intro i hlo hhi
  have h : i = 1178 := by omega
  subst i
  exact disposition_at_1178


theorem disposition_interval_1179 : Interval dispositionTest 1179 1180 := by
  intro i hlo hhi
  have h : i = 1179 := by omega
  subst i
  exact disposition_at_1179


theorem disposition_interval_1180 : Interval dispositionTest 1180 1181 := by
  intro i hlo hhi
  have h : i = 1180 := by omega
  subst i
  exact disposition_at_1180


theorem disposition_interval_1181 : Interval dispositionTest 1181 1182 := by
  intro i hlo hhi
  have h : i = 1181 := by omega
  subst i
  exact disposition_at_1181


theorem disposition_interval_1182 : Interval dispositionTest 1182 1183 := by
  intro i hlo hhi
  have h : i = 1182 := by omega
  subst i
  exact disposition_at_1182


theorem disposition_interval_1183 : Interval dispositionTest 1183 1184 := by
  intro i hlo hhi
  have h : i = 1183 := by omega
  subst i
  exact disposition_at_1183

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
