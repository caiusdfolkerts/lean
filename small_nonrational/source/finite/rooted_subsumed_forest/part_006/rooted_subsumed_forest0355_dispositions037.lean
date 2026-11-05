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
theorem disposition_at_1184 : dispositionTest 1184 = true := by decide +kernel

theorem disposition_at_1185 : dispositionTest 1185 = true := by decide +kernel

theorem disposition_at_1186 : dispositionTest 1186 = true := by decide +kernel

theorem disposition_at_1187 : dispositionTest 1187 = true := by decide +kernel

theorem disposition_at_1188 : dispositionTest 1188 = true := by decide +kernel

theorem disposition_at_1189 : dispositionTest 1189 = true := by decide +kernel

theorem disposition_at_1190 : dispositionTest 1190 = true := by decide +kernel

theorem disposition_at_1191 : dispositionTest 1191 = true := by decide +kernel

theorem disposition_at_1192 : dispositionTest 1192 = true := by decide +kernel

theorem disposition_at_1193 : dispositionTest 1193 = true := by decide +kernel

theorem disposition_at_1194 : dispositionTest 1194 = true := by decide +kernel

theorem disposition_at_1195 : dispositionTest 1195 = true := by decide +kernel

theorem disposition_at_1196 : dispositionTest 1196 = true := by decide +kernel

theorem disposition_at_1197 : dispositionTest 1197 = true := by decide +kernel

theorem disposition_at_1198 : dispositionTest 1198 = true := by decide +kernel

theorem disposition_at_1199 : dispositionTest 1199 = true := by decide +kernel

theorem disposition_at_1200 : dispositionTest 1200 = true := by decide +kernel

theorem disposition_at_1201 : dispositionTest 1201 = true := by decide +kernel

theorem disposition_at_1202 : dispositionTest 1202 = true := by decide +kernel

theorem disposition_at_1203 : dispositionTest 1203 = true := by decide +kernel

theorem disposition_at_1204 : dispositionTest 1204 = true := by decide +kernel

theorem disposition_at_1205 : dispositionTest 1205 = true := by decide +kernel

theorem disposition_at_1206 : dispositionTest 1206 = true := by decide +kernel

theorem disposition_at_1207 : dispositionTest 1207 = true := by decide +kernel

theorem disposition_at_1208 : dispositionTest 1208 = true := by decide +kernel

theorem disposition_at_1209 : dispositionTest 1209 = true := by decide +kernel

theorem disposition_at_1210 : dispositionTest 1210 = true := by decide +kernel

theorem disposition_at_1211 : dispositionTest 1211 = true := by decide +kernel

theorem disposition_at_1212 : dispositionTest 1212 = true := by decide +kernel

theorem disposition_at_1213 : dispositionTest 1213 = true := by decide +kernel

theorem disposition_at_1214 : dispositionTest 1214 = true := by decide +kernel

theorem disposition_at_1215 : dispositionTest 1215 = true := by decide +kernel

theorem disposition_interval_1184 : Interval dispositionTest 1184 1185 := by
  intro i hlo hhi
  have h : i = 1184 := by omega
  subst i
  exact disposition_at_1184


theorem disposition_interval_1185 : Interval dispositionTest 1185 1186 := by
  intro i hlo hhi
  have h : i = 1185 := by omega
  subst i
  exact disposition_at_1185


theorem disposition_interval_1186 : Interval dispositionTest 1186 1187 := by
  intro i hlo hhi
  have h : i = 1186 := by omega
  subst i
  exact disposition_at_1186


theorem disposition_interval_1187 : Interval dispositionTest 1187 1188 := by
  intro i hlo hhi
  have h : i = 1187 := by omega
  subst i
  exact disposition_at_1187


theorem disposition_interval_1188 : Interval dispositionTest 1188 1189 := by
  intro i hlo hhi
  have h : i = 1188 := by omega
  subst i
  exact disposition_at_1188


theorem disposition_interval_1189 : Interval dispositionTest 1189 1190 := by
  intro i hlo hhi
  have h : i = 1189 := by omega
  subst i
  exact disposition_at_1189


theorem disposition_interval_1190 : Interval dispositionTest 1190 1191 := by
  intro i hlo hhi
  have h : i = 1190 := by omega
  subst i
  exact disposition_at_1190


theorem disposition_interval_1191 : Interval dispositionTest 1191 1192 := by
  intro i hlo hhi
  have h : i = 1191 := by omega
  subst i
  exact disposition_at_1191


theorem disposition_interval_1192 : Interval dispositionTest 1192 1193 := by
  intro i hlo hhi
  have h : i = 1192 := by omega
  subst i
  exact disposition_at_1192


theorem disposition_interval_1193 : Interval dispositionTest 1193 1194 := by
  intro i hlo hhi
  have h : i = 1193 := by omega
  subst i
  exact disposition_at_1193


theorem disposition_interval_1194 : Interval dispositionTest 1194 1195 := by
  intro i hlo hhi
  have h : i = 1194 := by omega
  subst i
  exact disposition_at_1194


theorem disposition_interval_1195 : Interval dispositionTest 1195 1196 := by
  intro i hlo hhi
  have h : i = 1195 := by omega
  subst i
  exact disposition_at_1195


theorem disposition_interval_1196 : Interval dispositionTest 1196 1197 := by
  intro i hlo hhi
  have h : i = 1196 := by omega
  subst i
  exact disposition_at_1196


theorem disposition_interval_1197 : Interval dispositionTest 1197 1198 := by
  intro i hlo hhi
  have h : i = 1197 := by omega
  subst i
  exact disposition_at_1197


theorem disposition_interval_1198 : Interval dispositionTest 1198 1199 := by
  intro i hlo hhi
  have h : i = 1198 := by omega
  subst i
  exact disposition_at_1198


theorem disposition_interval_1199 : Interval dispositionTest 1199 1200 := by
  intro i hlo hhi
  have h : i = 1199 := by omega
  subst i
  exact disposition_at_1199


theorem disposition_interval_1200 : Interval dispositionTest 1200 1201 := by
  intro i hlo hhi
  have h : i = 1200 := by omega
  subst i
  exact disposition_at_1200


theorem disposition_interval_1201 : Interval dispositionTest 1201 1202 := by
  intro i hlo hhi
  have h : i = 1201 := by omega
  subst i
  exact disposition_at_1201


theorem disposition_interval_1202 : Interval dispositionTest 1202 1203 := by
  intro i hlo hhi
  have h : i = 1202 := by omega
  subst i
  exact disposition_at_1202


theorem disposition_interval_1203 : Interval dispositionTest 1203 1204 := by
  intro i hlo hhi
  have h : i = 1203 := by omega
  subst i
  exact disposition_at_1203


theorem disposition_interval_1204 : Interval dispositionTest 1204 1205 := by
  intro i hlo hhi
  have h : i = 1204 := by omega
  subst i
  exact disposition_at_1204


theorem disposition_interval_1205 : Interval dispositionTest 1205 1206 := by
  intro i hlo hhi
  have h : i = 1205 := by omega
  subst i
  exact disposition_at_1205


theorem disposition_interval_1206 : Interval dispositionTest 1206 1207 := by
  intro i hlo hhi
  have h : i = 1206 := by omega
  subst i
  exact disposition_at_1206


theorem disposition_interval_1207 : Interval dispositionTest 1207 1208 := by
  intro i hlo hhi
  have h : i = 1207 := by omega
  subst i
  exact disposition_at_1207


theorem disposition_interval_1208 : Interval dispositionTest 1208 1209 := by
  intro i hlo hhi
  have h : i = 1208 := by omega
  subst i
  exact disposition_at_1208


theorem disposition_interval_1209 : Interval dispositionTest 1209 1210 := by
  intro i hlo hhi
  have h : i = 1209 := by omega
  subst i
  exact disposition_at_1209


theorem disposition_interval_1210 : Interval dispositionTest 1210 1211 := by
  intro i hlo hhi
  have h : i = 1210 := by omega
  subst i
  exact disposition_at_1210


theorem disposition_interval_1211 : Interval dispositionTest 1211 1212 := by
  intro i hlo hhi
  have h : i = 1211 := by omega
  subst i
  exact disposition_at_1211


theorem disposition_interval_1212 : Interval dispositionTest 1212 1213 := by
  intro i hlo hhi
  have h : i = 1212 := by omega
  subst i
  exact disposition_at_1212


theorem disposition_interval_1213 : Interval dispositionTest 1213 1214 := by
  intro i hlo hhi
  have h : i = 1213 := by omega
  subst i
  exact disposition_at_1213


theorem disposition_interval_1214 : Interval dispositionTest 1214 1215 := by
  intro i hlo hhi
  have h : i = 1214 := by omega
  subst i
  exact disposition_at_1214


theorem disposition_interval_1215 : Interval dispositionTest 1215 1216 := by
  intro i hlo hhi
  have h : i = 1215 := by omega
  subst i
  exact disposition_at_1215

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
