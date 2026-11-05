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
theorem disposition_at_1344 : dispositionTest 1344 = true := by decide +kernel

theorem disposition_at_1345 : dispositionTest 1345 = true := by decide +kernel

theorem disposition_at_1346 : dispositionTest 1346 = true := by decide +kernel

theorem disposition_at_1347 : dispositionTest 1347 = true := by decide +kernel

theorem disposition_at_1348 : dispositionTest 1348 = true := by decide +kernel

theorem disposition_at_1349 : dispositionTest 1349 = true := by decide +kernel

theorem disposition_at_1350 : dispositionTest 1350 = true := by decide +kernel

theorem disposition_at_1351 : dispositionTest 1351 = true := by decide +kernel

theorem disposition_at_1352 : dispositionTest 1352 = true := by decide +kernel

theorem disposition_at_1353 : dispositionTest 1353 = true := by decide +kernel

theorem disposition_at_1354 : dispositionTest 1354 = true := by decide +kernel

theorem disposition_at_1355 : dispositionTest 1355 = true := by decide +kernel

theorem disposition_at_1356 : dispositionTest 1356 = true := by decide +kernel

theorem disposition_at_1357 : dispositionTest 1357 = true := by decide +kernel

theorem disposition_at_1358 : dispositionTest 1358 = true := by decide +kernel

theorem disposition_at_1359 : dispositionTest 1359 = true := by decide +kernel

theorem disposition_at_1360 : dispositionTest 1360 = true := by decide +kernel

theorem disposition_at_1361 : dispositionTest 1361 = true := by decide +kernel

theorem disposition_at_1362 : dispositionTest 1362 = true := by decide +kernel

theorem disposition_at_1363 : dispositionTest 1363 = true := by decide +kernel


theorem disposition_at_1364 : dispositionTest 1364 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1364).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1259.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1259) = true
  rw [Nonrational.OldTerminalMatches.M019.r1259_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_1365 : dispositionTest 1365 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1365).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) Nonrational.OldTerminalMatches.M019.r1260.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M019.r1260) = true
  rw [Nonrational.OldTerminalMatches.M019.r1260_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1366 : dispositionTest 1366 = true := by decide +kernel

theorem disposition_at_1367 : dispositionTest 1367 = true := by decide +kernel

theorem disposition_at_1368 : dispositionTest 1368 = true := by decide +kernel

theorem disposition_at_1369 : dispositionTest 1369 = true := by decide +kernel

theorem disposition_at_1370 : dispositionTest 1370 = true := by decide +kernel

theorem disposition_at_1371 : dispositionTest 1371 = true := by decide +kernel

theorem disposition_at_1372 : dispositionTest 1372 = true := by decide +kernel

theorem disposition_at_1373 : dispositionTest 1373 = true := by decide +kernel

theorem disposition_at_1374 : dispositionTest 1374 = true := by decide +kernel

theorem disposition_at_1375 : dispositionTest 1375 = true := by decide +kernel

theorem disposition_interval_1344 : Interval dispositionTest 1344 1345 := by
  intro i hlo hhi
  have h : i = 1344 := by omega
  subst i
  exact disposition_at_1344


theorem disposition_interval_1345 : Interval dispositionTest 1345 1346 := by
  intro i hlo hhi
  have h : i = 1345 := by omega
  subst i
  exact disposition_at_1345


theorem disposition_interval_1346 : Interval dispositionTest 1346 1347 := by
  intro i hlo hhi
  have h : i = 1346 := by omega
  subst i
  exact disposition_at_1346


theorem disposition_interval_1347 : Interval dispositionTest 1347 1348 := by
  intro i hlo hhi
  have h : i = 1347 := by omega
  subst i
  exact disposition_at_1347


theorem disposition_interval_1348 : Interval dispositionTest 1348 1349 := by
  intro i hlo hhi
  have h : i = 1348 := by omega
  subst i
  exact disposition_at_1348


theorem disposition_interval_1349 : Interval dispositionTest 1349 1350 := by
  intro i hlo hhi
  have h : i = 1349 := by omega
  subst i
  exact disposition_at_1349


theorem disposition_interval_1350 : Interval dispositionTest 1350 1351 := by
  intro i hlo hhi
  have h : i = 1350 := by omega
  subst i
  exact disposition_at_1350


theorem disposition_interval_1351 : Interval dispositionTest 1351 1352 := by
  intro i hlo hhi
  have h : i = 1351 := by omega
  subst i
  exact disposition_at_1351


theorem disposition_interval_1352 : Interval dispositionTest 1352 1353 := by
  intro i hlo hhi
  have h : i = 1352 := by omega
  subst i
  exact disposition_at_1352


theorem disposition_interval_1353 : Interval dispositionTest 1353 1354 := by
  intro i hlo hhi
  have h : i = 1353 := by omega
  subst i
  exact disposition_at_1353


theorem disposition_interval_1354 : Interval dispositionTest 1354 1355 := by
  intro i hlo hhi
  have h : i = 1354 := by omega
  subst i
  exact disposition_at_1354


theorem disposition_interval_1355 : Interval dispositionTest 1355 1356 := by
  intro i hlo hhi
  have h : i = 1355 := by omega
  subst i
  exact disposition_at_1355


theorem disposition_interval_1356 : Interval dispositionTest 1356 1357 := by
  intro i hlo hhi
  have h : i = 1356 := by omega
  subst i
  exact disposition_at_1356


theorem disposition_interval_1357 : Interval dispositionTest 1357 1358 := by
  intro i hlo hhi
  have h : i = 1357 := by omega
  subst i
  exact disposition_at_1357


theorem disposition_interval_1358 : Interval dispositionTest 1358 1359 := by
  intro i hlo hhi
  have h : i = 1358 := by omega
  subst i
  exact disposition_at_1358


theorem disposition_interval_1359 : Interval dispositionTest 1359 1360 := by
  intro i hlo hhi
  have h : i = 1359 := by omega
  subst i
  exact disposition_at_1359


theorem disposition_interval_1360 : Interval dispositionTest 1360 1361 := by
  intro i hlo hhi
  have h : i = 1360 := by omega
  subst i
  exact disposition_at_1360


theorem disposition_interval_1361 : Interval dispositionTest 1361 1362 := by
  intro i hlo hhi
  have h : i = 1361 := by omega
  subst i
  exact disposition_at_1361


theorem disposition_interval_1362 : Interval dispositionTest 1362 1363 := by
  intro i hlo hhi
  have h : i = 1362 := by omega
  subst i
  exact disposition_at_1362


theorem disposition_interval_1363 : Interval dispositionTest 1363 1364 := by
  intro i hlo hhi
  have h : i = 1363 := by omega
  subst i
  exact disposition_at_1363


theorem disposition_interval_1364 : Interval dispositionTest 1364 1365 := by
  intro i hlo hhi
  have h : i = 1364 := by omega
  subst i
  exact disposition_at_1364


theorem disposition_interval_1365 : Interval dispositionTest 1365 1366 := by
  intro i hlo hhi
  have h : i = 1365 := by omega
  subst i
  exact disposition_at_1365


theorem disposition_interval_1366 : Interval dispositionTest 1366 1367 := by
  intro i hlo hhi
  have h : i = 1366 := by omega
  subst i
  exact disposition_at_1366


theorem disposition_interval_1367 : Interval dispositionTest 1367 1368 := by
  intro i hlo hhi
  have h : i = 1367 := by omega
  subst i
  exact disposition_at_1367


theorem disposition_interval_1368 : Interval dispositionTest 1368 1369 := by
  intro i hlo hhi
  have h : i = 1368 := by omega
  subst i
  exact disposition_at_1368


theorem disposition_interval_1369 : Interval dispositionTest 1369 1370 := by
  intro i hlo hhi
  have h : i = 1369 := by omega
  subst i
  exact disposition_at_1369


theorem disposition_interval_1370 : Interval dispositionTest 1370 1371 := by
  intro i hlo hhi
  have h : i = 1370 := by omega
  subst i
  exact disposition_at_1370


theorem disposition_interval_1371 : Interval dispositionTest 1371 1372 := by
  intro i hlo hhi
  have h : i = 1371 := by omega
  subst i
  exact disposition_at_1371


theorem disposition_interval_1372 : Interval dispositionTest 1372 1373 := by
  intro i hlo hhi
  have h : i = 1372 := by omega
  subst i
  exact disposition_at_1372


theorem disposition_interval_1373 : Interval dispositionTest 1373 1374 := by
  intro i hlo hhi
  have h : i = 1373 := by omega
  subst i
  exact disposition_at_1373


theorem disposition_interval_1374 : Interval dispositionTest 1374 1375 := by
  intro i hlo hhi
  have h : i = 1374 := by omega
  subst i
  exact disposition_at_1374


theorem disposition_interval_1375 : Interval dispositionTest 1375 1376 := by
  intro i hlo hhi
  have h : i = 1375 := by omega
  subst i
  exact disposition_at_1375

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
