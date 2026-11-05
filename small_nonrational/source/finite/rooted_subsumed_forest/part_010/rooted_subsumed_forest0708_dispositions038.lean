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
theorem disposition_at_1216 : dispositionTest 1216 = true := by decide +kernel

theorem disposition_at_1217 : dispositionTest 1217 = true := by decide +kernel

theorem disposition_at_1218 : dispositionTest 1218 = true := by decide +kernel

theorem disposition_at_1219 : dispositionTest 1219 = true := by decide +kernel

theorem disposition_at_1220 : dispositionTest 1220 = true := by decide +kernel

theorem disposition_at_1221 : dispositionTest 1221 = true := by decide +kernel

theorem disposition_at_1222 : dispositionTest 1222 = true := by decide +kernel

theorem disposition_at_1223 : dispositionTest 1223 = true := by decide +kernel

theorem disposition_at_1224 : dispositionTest 1224 = true := by decide +kernel

theorem disposition_at_1225 : dispositionTest 1225 = true := by decide +kernel

theorem disposition_at_1226 : dispositionTest 1226 = true := by decide +kernel

theorem disposition_at_1227 : dispositionTest 1227 = true := by decide +kernel

theorem disposition_at_1228 : dispositionTest 1228 = true := by decide +kernel

theorem disposition_at_1229 : dispositionTest 1229 = true := by decide +kernel

theorem disposition_at_1230 : dispositionTest 1230 = true := by decide +kernel

theorem disposition_at_1231 : dispositionTest 1231 = true := by decide +kernel

theorem disposition_at_1232 : dispositionTest 1232 = true := by decide +kernel

theorem disposition_at_1233 : dispositionTest 1233 = true := by decide +kernel

theorem disposition_at_1234 : dispositionTest 1234 = true := by decide +kernel

theorem disposition_at_1235 : dispositionTest 1235 = true := by decide +kernel

theorem disposition_at_1236 : dispositionTest 1236 = true := by decide +kernel

theorem disposition_at_1237 : dispositionTest 1237 = true := by decide +kernel

theorem disposition_at_1238 : dispositionTest 1238 = true := by decide +kernel

theorem disposition_at_1239 : dispositionTest 1239 = true := by decide +kernel

theorem disposition_at_1240 : dispositionTest 1240 = true := by decide +kernel

theorem disposition_at_1241 : dispositionTest 1241 = true := by decide +kernel

theorem disposition_at_1242 : dispositionTest 1242 = true := by decide +kernel

theorem disposition_at_1243 : dispositionTest 1243 = true := by decide +kernel

theorem disposition_at_1244 : dispositionTest 1244 = true := by decide +kernel


theorem disposition_at_1245 : dispositionTest 1245 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1245).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1257.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1257) = true
  rw [Nonrational.OldTerminalMatches.M019.r1257_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1246 : dispositionTest 1246 = true := by decide +kernel

theorem disposition_at_1247 : dispositionTest 1247 = true := by decide +kernel

theorem disposition_interval_1216 : Interval dispositionTest 1216 1217 := by
  intro i hlo hhi
  have h : i = 1216 := by omega
  subst i
  exact disposition_at_1216


theorem disposition_interval_1217 : Interval dispositionTest 1217 1218 := by
  intro i hlo hhi
  have h : i = 1217 := by omega
  subst i
  exact disposition_at_1217


theorem disposition_interval_1218 : Interval dispositionTest 1218 1219 := by
  intro i hlo hhi
  have h : i = 1218 := by omega
  subst i
  exact disposition_at_1218


theorem disposition_interval_1219 : Interval dispositionTest 1219 1220 := by
  intro i hlo hhi
  have h : i = 1219 := by omega
  subst i
  exact disposition_at_1219


theorem disposition_interval_1220 : Interval dispositionTest 1220 1221 := by
  intro i hlo hhi
  have h : i = 1220 := by omega
  subst i
  exact disposition_at_1220


theorem disposition_interval_1221 : Interval dispositionTest 1221 1222 := by
  intro i hlo hhi
  have h : i = 1221 := by omega
  subst i
  exact disposition_at_1221


theorem disposition_interval_1222 : Interval dispositionTest 1222 1223 := by
  intro i hlo hhi
  have h : i = 1222 := by omega
  subst i
  exact disposition_at_1222


theorem disposition_interval_1223 : Interval dispositionTest 1223 1224 := by
  intro i hlo hhi
  have h : i = 1223 := by omega
  subst i
  exact disposition_at_1223


theorem disposition_interval_1224 : Interval dispositionTest 1224 1225 := by
  intro i hlo hhi
  have h : i = 1224 := by omega
  subst i
  exact disposition_at_1224


theorem disposition_interval_1225 : Interval dispositionTest 1225 1226 := by
  intro i hlo hhi
  have h : i = 1225 := by omega
  subst i
  exact disposition_at_1225


theorem disposition_interval_1226 : Interval dispositionTest 1226 1227 := by
  intro i hlo hhi
  have h : i = 1226 := by omega
  subst i
  exact disposition_at_1226


theorem disposition_interval_1227 : Interval dispositionTest 1227 1228 := by
  intro i hlo hhi
  have h : i = 1227 := by omega
  subst i
  exact disposition_at_1227


theorem disposition_interval_1228 : Interval dispositionTest 1228 1229 := by
  intro i hlo hhi
  have h : i = 1228 := by omega
  subst i
  exact disposition_at_1228


theorem disposition_interval_1229 : Interval dispositionTest 1229 1230 := by
  intro i hlo hhi
  have h : i = 1229 := by omega
  subst i
  exact disposition_at_1229


theorem disposition_interval_1230 : Interval dispositionTest 1230 1231 := by
  intro i hlo hhi
  have h : i = 1230 := by omega
  subst i
  exact disposition_at_1230


theorem disposition_interval_1231 : Interval dispositionTest 1231 1232 := by
  intro i hlo hhi
  have h : i = 1231 := by omega
  subst i
  exact disposition_at_1231


theorem disposition_interval_1232 : Interval dispositionTest 1232 1233 := by
  intro i hlo hhi
  have h : i = 1232 := by omega
  subst i
  exact disposition_at_1232


theorem disposition_interval_1233 : Interval dispositionTest 1233 1234 := by
  intro i hlo hhi
  have h : i = 1233 := by omega
  subst i
  exact disposition_at_1233


theorem disposition_interval_1234 : Interval dispositionTest 1234 1235 := by
  intro i hlo hhi
  have h : i = 1234 := by omega
  subst i
  exact disposition_at_1234


theorem disposition_interval_1235 : Interval dispositionTest 1235 1236 := by
  intro i hlo hhi
  have h : i = 1235 := by omega
  subst i
  exact disposition_at_1235


theorem disposition_interval_1236 : Interval dispositionTest 1236 1237 := by
  intro i hlo hhi
  have h : i = 1236 := by omega
  subst i
  exact disposition_at_1236


theorem disposition_interval_1237 : Interval dispositionTest 1237 1238 := by
  intro i hlo hhi
  have h : i = 1237 := by omega
  subst i
  exact disposition_at_1237


theorem disposition_interval_1238 : Interval dispositionTest 1238 1239 := by
  intro i hlo hhi
  have h : i = 1238 := by omega
  subst i
  exact disposition_at_1238


theorem disposition_interval_1239 : Interval dispositionTest 1239 1240 := by
  intro i hlo hhi
  have h : i = 1239 := by omega
  subst i
  exact disposition_at_1239


theorem disposition_interval_1240 : Interval dispositionTest 1240 1241 := by
  intro i hlo hhi
  have h : i = 1240 := by omega
  subst i
  exact disposition_at_1240


theorem disposition_interval_1241 : Interval dispositionTest 1241 1242 := by
  intro i hlo hhi
  have h : i = 1241 := by omega
  subst i
  exact disposition_at_1241


theorem disposition_interval_1242 : Interval dispositionTest 1242 1243 := by
  intro i hlo hhi
  have h : i = 1242 := by omega
  subst i
  exact disposition_at_1242


theorem disposition_interval_1243 : Interval dispositionTest 1243 1244 := by
  intro i hlo hhi
  have h : i = 1243 := by omega
  subst i
  exact disposition_at_1243


theorem disposition_interval_1244 : Interval dispositionTest 1244 1245 := by
  intro i hlo hhi
  have h : i = 1244 := by omega
  subst i
  exact disposition_at_1244


theorem disposition_interval_1245 : Interval dispositionTest 1245 1246 := by
  intro i hlo hhi
  have h : i = 1245 := by omega
  subst i
  exact disposition_at_1245


theorem disposition_interval_1246 : Interval dispositionTest 1246 1247 := by
  intro i hlo hhi
  have h : i = 1246 := by omega
  subst i
  exact disposition_at_1246


theorem disposition_interval_1247 : Interval dispositionTest 1247 1248 := by
  intro i hlo hhi
  have h : i = 1247 := by omega
  subst i
  exact disposition_at_1247

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
