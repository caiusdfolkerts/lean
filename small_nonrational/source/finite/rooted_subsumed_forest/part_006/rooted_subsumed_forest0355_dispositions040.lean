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
theorem disposition_at_1280 : dispositionTest 1280 = true := by decide +kernel

theorem disposition_at_1281 : dispositionTest 1281 = true := by decide +kernel

theorem disposition_at_1282 : dispositionTest 1282 = true := by decide +kernel

theorem disposition_at_1283 : dispositionTest 1283 = true := by decide +kernel

theorem disposition_at_1284 : dispositionTest 1284 = true := by decide +kernel

theorem disposition_at_1285 : dispositionTest 1285 = true := by decide +kernel

theorem disposition_at_1286 : dispositionTest 1286 = true := by decide +kernel

theorem disposition_at_1287 : dispositionTest 1287 = true := by decide +kernel

theorem disposition_at_1288 : dispositionTest 1288 = true := by decide +kernel

theorem disposition_at_1289 : dispositionTest 1289 = true := by decide +kernel

theorem disposition_at_1290 : dispositionTest 1290 = true := by decide +kernel

theorem disposition_at_1291 : dispositionTest 1291 = true := by decide +kernel

theorem disposition_at_1292 : dispositionTest 1292 = true := by decide +kernel

theorem disposition_at_1293 : dispositionTest 1293 = true := by decide +kernel

theorem disposition_at_1294 : dispositionTest 1294 = true := by decide +kernel

theorem disposition_at_1295 : dispositionTest 1295 = true := by decide +kernel

theorem disposition_at_1296 : dispositionTest 1296 = true := by decide +kernel


theorem disposition_at_1297 : dispositionTest 1297 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1297).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M015.r1006.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M015.r1006) = true
  rw [Nonrational.OldTerminalMatches.M015.r1006_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1298 : dispositionTest 1298 = true := by decide +kernel

theorem disposition_at_1299 : dispositionTest 1299 = true := by decide +kernel

theorem disposition_at_1300 : dispositionTest 1300 = true := by decide +kernel

theorem disposition_at_1301 : dispositionTest 1301 = true := by decide +kernel

theorem disposition_at_1302 : dispositionTest 1302 = true := by decide +kernel

theorem disposition_at_1303 : dispositionTest 1303 = true := by decide +kernel

theorem disposition_at_1304 : dispositionTest 1304 = true := by decide +kernel

theorem disposition_at_1305 : dispositionTest 1305 = true := by decide +kernel

theorem disposition_at_1306 : dispositionTest 1306 = true := by decide +kernel

theorem disposition_at_1307 : dispositionTest 1307 = true := by decide +kernel

theorem disposition_at_1308 : dispositionTest 1308 = true := by decide +kernel

theorem disposition_at_1309 : dispositionTest 1309 = true := by decide +kernel

theorem disposition_at_1310 : dispositionTest 1310 = true := by decide +kernel

theorem disposition_at_1311 : dispositionTest 1311 = true := by decide +kernel

theorem disposition_interval_1280 : Interval dispositionTest 1280 1281 := by
  intro i hlo hhi
  have h : i = 1280 := by omega
  subst i
  exact disposition_at_1280


theorem disposition_interval_1281 : Interval dispositionTest 1281 1282 := by
  intro i hlo hhi
  have h : i = 1281 := by omega
  subst i
  exact disposition_at_1281


theorem disposition_interval_1282 : Interval dispositionTest 1282 1283 := by
  intro i hlo hhi
  have h : i = 1282 := by omega
  subst i
  exact disposition_at_1282


theorem disposition_interval_1283 : Interval dispositionTest 1283 1284 := by
  intro i hlo hhi
  have h : i = 1283 := by omega
  subst i
  exact disposition_at_1283


theorem disposition_interval_1284 : Interval dispositionTest 1284 1285 := by
  intro i hlo hhi
  have h : i = 1284 := by omega
  subst i
  exact disposition_at_1284


theorem disposition_interval_1285 : Interval dispositionTest 1285 1286 := by
  intro i hlo hhi
  have h : i = 1285 := by omega
  subst i
  exact disposition_at_1285


theorem disposition_interval_1286 : Interval dispositionTest 1286 1287 := by
  intro i hlo hhi
  have h : i = 1286 := by omega
  subst i
  exact disposition_at_1286


theorem disposition_interval_1287 : Interval dispositionTest 1287 1288 := by
  intro i hlo hhi
  have h : i = 1287 := by omega
  subst i
  exact disposition_at_1287


theorem disposition_interval_1288 : Interval dispositionTest 1288 1289 := by
  intro i hlo hhi
  have h : i = 1288 := by omega
  subst i
  exact disposition_at_1288


theorem disposition_interval_1289 : Interval dispositionTest 1289 1290 := by
  intro i hlo hhi
  have h : i = 1289 := by omega
  subst i
  exact disposition_at_1289


theorem disposition_interval_1290 : Interval dispositionTest 1290 1291 := by
  intro i hlo hhi
  have h : i = 1290 := by omega
  subst i
  exact disposition_at_1290


theorem disposition_interval_1291 : Interval dispositionTest 1291 1292 := by
  intro i hlo hhi
  have h : i = 1291 := by omega
  subst i
  exact disposition_at_1291


theorem disposition_interval_1292 : Interval dispositionTest 1292 1293 := by
  intro i hlo hhi
  have h : i = 1292 := by omega
  subst i
  exact disposition_at_1292


theorem disposition_interval_1293 : Interval dispositionTest 1293 1294 := by
  intro i hlo hhi
  have h : i = 1293 := by omega
  subst i
  exact disposition_at_1293


theorem disposition_interval_1294 : Interval dispositionTest 1294 1295 := by
  intro i hlo hhi
  have h : i = 1294 := by omega
  subst i
  exact disposition_at_1294


theorem disposition_interval_1295 : Interval dispositionTest 1295 1296 := by
  intro i hlo hhi
  have h : i = 1295 := by omega
  subst i
  exact disposition_at_1295


theorem disposition_interval_1296 : Interval dispositionTest 1296 1297 := by
  intro i hlo hhi
  have h : i = 1296 := by omega
  subst i
  exact disposition_at_1296


theorem disposition_interval_1297 : Interval dispositionTest 1297 1298 := by
  intro i hlo hhi
  have h : i = 1297 := by omega
  subst i
  exact disposition_at_1297


theorem disposition_interval_1298 : Interval dispositionTest 1298 1299 := by
  intro i hlo hhi
  have h : i = 1298 := by omega
  subst i
  exact disposition_at_1298


theorem disposition_interval_1299 : Interval dispositionTest 1299 1300 := by
  intro i hlo hhi
  have h : i = 1299 := by omega
  subst i
  exact disposition_at_1299


theorem disposition_interval_1300 : Interval dispositionTest 1300 1301 := by
  intro i hlo hhi
  have h : i = 1300 := by omega
  subst i
  exact disposition_at_1300


theorem disposition_interval_1301 : Interval dispositionTest 1301 1302 := by
  intro i hlo hhi
  have h : i = 1301 := by omega
  subst i
  exact disposition_at_1301


theorem disposition_interval_1302 : Interval dispositionTest 1302 1303 := by
  intro i hlo hhi
  have h : i = 1302 := by omega
  subst i
  exact disposition_at_1302


theorem disposition_interval_1303 : Interval dispositionTest 1303 1304 := by
  intro i hlo hhi
  have h : i = 1303 := by omega
  subst i
  exact disposition_at_1303


theorem disposition_interval_1304 : Interval dispositionTest 1304 1305 := by
  intro i hlo hhi
  have h : i = 1304 := by omega
  subst i
  exact disposition_at_1304


theorem disposition_interval_1305 : Interval dispositionTest 1305 1306 := by
  intro i hlo hhi
  have h : i = 1305 := by omega
  subst i
  exact disposition_at_1305


theorem disposition_interval_1306 : Interval dispositionTest 1306 1307 := by
  intro i hlo hhi
  have h : i = 1306 := by omega
  subst i
  exact disposition_at_1306


theorem disposition_interval_1307 : Interval dispositionTest 1307 1308 := by
  intro i hlo hhi
  have h : i = 1307 := by omega
  subst i
  exact disposition_at_1307


theorem disposition_interval_1308 : Interval dispositionTest 1308 1309 := by
  intro i hlo hhi
  have h : i = 1308 := by omega
  subst i
  exact disposition_at_1308


theorem disposition_interval_1309 : Interval dispositionTest 1309 1310 := by
  intro i hlo hhi
  have h : i = 1309 := by omega
  subst i
  exact disposition_at_1309


theorem disposition_interval_1310 : Interval dispositionTest 1310 1311 := by
  intro i hlo hhi
  have h : i = 1310 := by omega
  subst i
  exact disposition_at_1310


theorem disposition_interval_1311 : Interval dispositionTest 1311 1312 := by
  intro i hlo hhi
  have h : i = 1311 := by omega
  subst i
  exact disposition_at_1311

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
