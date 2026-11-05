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
theorem disposition_at_1440 : dispositionTest 1440 = true := by decide +kernel

theorem disposition_at_1441 : dispositionTest 1441 = true := by decide +kernel

theorem disposition_at_1442 : dispositionTest 1442 = true := by decide +kernel

theorem disposition_at_1443 : dispositionTest 1443 = true := by decide +kernel

theorem disposition_at_1444 : dispositionTest 1444 = true := by decide +kernel

theorem disposition_at_1445 : dispositionTest 1445 = true := by decide +kernel

theorem disposition_at_1446 : dispositionTest 1446 = true := by decide +kernel

theorem disposition_at_1447 : dispositionTest 1447 = true := by decide +kernel

theorem disposition_at_1448 : dispositionTest 1448 = true := by decide +kernel

theorem disposition_at_1449 : dispositionTest 1449 = true := by decide +kernel

theorem disposition_at_1450 : dispositionTest 1450 = true := by decide +kernel

theorem disposition_at_1451 : dispositionTest 1451 = true := by decide +kernel

theorem disposition_at_1452 : dispositionTest 1452 = true := by decide +kernel

theorem disposition_at_1453 : dispositionTest 1453 = true := by decide +kernel

theorem disposition_at_1454 : dispositionTest 1454 = true := by decide +kernel

theorem disposition_at_1455 : dispositionTest 1455 = true := by decide +kernel

theorem disposition_at_1456 : dispositionTest 1456 = true := by decide +kernel

theorem disposition_at_1457 : dispositionTest 1457 = true := by decide +kernel

theorem disposition_at_1458 : dispositionTest 1458 = true := by decide +kernel

theorem disposition_at_1459 : dispositionTest 1459 = true := by decide +kernel

theorem disposition_at_1460 : dispositionTest 1460 = true := by decide +kernel

theorem disposition_at_1461 : dispositionTest 1461 = true := by decide +kernel

theorem disposition_at_1462 : dispositionTest 1462 = true := by decide +kernel

theorem disposition_at_1463 : dispositionTest 1463 = true := by decide +kernel

theorem disposition_at_1464 : dispositionTest 1464 = true := by decide +kernel

theorem disposition_at_1465 : dispositionTest 1465 = true := by decide +kernel

theorem disposition_at_1466 : dispositionTest 1466 = true := by decide +kernel

theorem disposition_at_1467 : dispositionTest 1467 = true := by decide +kernel

theorem disposition_at_1468 : dispositionTest 1468 = true := by decide +kernel

theorem disposition_at_1469 : dispositionTest 1469 = true := by decide +kernel

theorem disposition_at_1470 : dispositionTest 1470 = true := by decide +kernel

theorem disposition_at_1471 : dispositionTest 1471 = true := by decide +kernel

theorem disposition_interval_1440 : Interval dispositionTest 1440 1441 := by
  intro i hlo hhi
  have h : i = 1440 := by omega
  subst i
  exact disposition_at_1440


theorem disposition_interval_1441 : Interval dispositionTest 1441 1442 := by
  intro i hlo hhi
  have h : i = 1441 := by omega
  subst i
  exact disposition_at_1441


theorem disposition_interval_1442 : Interval dispositionTest 1442 1443 := by
  intro i hlo hhi
  have h : i = 1442 := by omega
  subst i
  exact disposition_at_1442


theorem disposition_interval_1443 : Interval dispositionTest 1443 1444 := by
  intro i hlo hhi
  have h : i = 1443 := by omega
  subst i
  exact disposition_at_1443


theorem disposition_interval_1444 : Interval dispositionTest 1444 1445 := by
  intro i hlo hhi
  have h : i = 1444 := by omega
  subst i
  exact disposition_at_1444


theorem disposition_interval_1445 : Interval dispositionTest 1445 1446 := by
  intro i hlo hhi
  have h : i = 1445 := by omega
  subst i
  exact disposition_at_1445


theorem disposition_interval_1446 : Interval dispositionTest 1446 1447 := by
  intro i hlo hhi
  have h : i = 1446 := by omega
  subst i
  exact disposition_at_1446


theorem disposition_interval_1447 : Interval dispositionTest 1447 1448 := by
  intro i hlo hhi
  have h : i = 1447 := by omega
  subst i
  exact disposition_at_1447


theorem disposition_interval_1448 : Interval dispositionTest 1448 1449 := by
  intro i hlo hhi
  have h : i = 1448 := by omega
  subst i
  exact disposition_at_1448


theorem disposition_interval_1449 : Interval dispositionTest 1449 1450 := by
  intro i hlo hhi
  have h : i = 1449 := by omega
  subst i
  exact disposition_at_1449


theorem disposition_interval_1450 : Interval dispositionTest 1450 1451 := by
  intro i hlo hhi
  have h : i = 1450 := by omega
  subst i
  exact disposition_at_1450


theorem disposition_interval_1451 : Interval dispositionTest 1451 1452 := by
  intro i hlo hhi
  have h : i = 1451 := by omega
  subst i
  exact disposition_at_1451


theorem disposition_interval_1452 : Interval dispositionTest 1452 1453 := by
  intro i hlo hhi
  have h : i = 1452 := by omega
  subst i
  exact disposition_at_1452


theorem disposition_interval_1453 : Interval dispositionTest 1453 1454 := by
  intro i hlo hhi
  have h : i = 1453 := by omega
  subst i
  exact disposition_at_1453


theorem disposition_interval_1454 : Interval dispositionTest 1454 1455 := by
  intro i hlo hhi
  have h : i = 1454 := by omega
  subst i
  exact disposition_at_1454


theorem disposition_interval_1455 : Interval dispositionTest 1455 1456 := by
  intro i hlo hhi
  have h : i = 1455 := by omega
  subst i
  exact disposition_at_1455


theorem disposition_interval_1456 : Interval dispositionTest 1456 1457 := by
  intro i hlo hhi
  have h : i = 1456 := by omega
  subst i
  exact disposition_at_1456


theorem disposition_interval_1457 : Interval dispositionTest 1457 1458 := by
  intro i hlo hhi
  have h : i = 1457 := by omega
  subst i
  exact disposition_at_1457


theorem disposition_interval_1458 : Interval dispositionTest 1458 1459 := by
  intro i hlo hhi
  have h : i = 1458 := by omega
  subst i
  exact disposition_at_1458


theorem disposition_interval_1459 : Interval dispositionTest 1459 1460 := by
  intro i hlo hhi
  have h : i = 1459 := by omega
  subst i
  exact disposition_at_1459


theorem disposition_interval_1460 : Interval dispositionTest 1460 1461 := by
  intro i hlo hhi
  have h : i = 1460 := by omega
  subst i
  exact disposition_at_1460


theorem disposition_interval_1461 : Interval dispositionTest 1461 1462 := by
  intro i hlo hhi
  have h : i = 1461 := by omega
  subst i
  exact disposition_at_1461


theorem disposition_interval_1462 : Interval dispositionTest 1462 1463 := by
  intro i hlo hhi
  have h : i = 1462 := by omega
  subst i
  exact disposition_at_1462


theorem disposition_interval_1463 : Interval dispositionTest 1463 1464 := by
  intro i hlo hhi
  have h : i = 1463 := by omega
  subst i
  exact disposition_at_1463


theorem disposition_interval_1464 : Interval dispositionTest 1464 1465 := by
  intro i hlo hhi
  have h : i = 1464 := by omega
  subst i
  exact disposition_at_1464


theorem disposition_interval_1465 : Interval dispositionTest 1465 1466 := by
  intro i hlo hhi
  have h : i = 1465 := by omega
  subst i
  exact disposition_at_1465


theorem disposition_interval_1466 : Interval dispositionTest 1466 1467 := by
  intro i hlo hhi
  have h : i = 1466 := by omega
  subst i
  exact disposition_at_1466


theorem disposition_interval_1467 : Interval dispositionTest 1467 1468 := by
  intro i hlo hhi
  have h : i = 1467 := by omega
  subst i
  exact disposition_at_1467


theorem disposition_interval_1468 : Interval dispositionTest 1468 1469 := by
  intro i hlo hhi
  have h : i = 1468 := by omega
  subst i
  exact disposition_at_1468


theorem disposition_interval_1469 : Interval dispositionTest 1469 1470 := by
  intro i hlo hhi
  have h : i = 1469 := by omega
  subst i
  exact disposition_at_1469


theorem disposition_interval_1470 : Interval dispositionTest 1470 1471 := by
  intro i hlo hhi
  have h : i = 1470 := by omega
  subst i
  exact disposition_at_1470


theorem disposition_interval_1471 : Interval dispositionTest 1471 1472 := by
  intro i hlo hhi
  have h : i = 1471 := by omega
  subst i
  exact disposition_at_1471

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
