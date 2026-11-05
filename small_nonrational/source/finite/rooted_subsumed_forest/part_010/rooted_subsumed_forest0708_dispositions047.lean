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
theorem disposition_at_1504 : dispositionTest 1504 = true := by decide +kernel

theorem disposition_at_1505 : dispositionTest 1505 = true := by decide +kernel

theorem disposition_at_1506 : dispositionTest 1506 = true := by decide +kernel

theorem disposition_at_1507 : dispositionTest 1507 = true := by decide +kernel

theorem disposition_at_1508 : dispositionTest 1508 = true := by decide +kernel

theorem disposition_at_1509 : dispositionTest 1509 = true := by decide +kernel

theorem disposition_at_1510 : dispositionTest 1510 = true := by decide +kernel

theorem disposition_at_1511 : dispositionTest 1511 = true := by decide +kernel

theorem disposition_at_1512 : dispositionTest 1512 = true := by decide +kernel

theorem disposition_at_1513 : dispositionTest 1513 = true := by decide +kernel

theorem disposition_at_1514 : dispositionTest 1514 = true := by decide +kernel

theorem disposition_at_1515 : dispositionTest 1515 = true := by decide +kernel

theorem disposition_at_1516 : dispositionTest 1516 = true := by decide +kernel

theorem disposition_at_1517 : dispositionTest 1517 = true := by decide +kernel

theorem disposition_at_1518 : dispositionTest 1518 = true := by decide +kernel

theorem disposition_at_1519 : dispositionTest 1519 = true := by decide +kernel

theorem disposition_at_1520 : dispositionTest 1520 = true := by decide +kernel

theorem disposition_at_1521 : dispositionTest 1521 = true := by decide +kernel

theorem disposition_at_1522 : dispositionTest 1522 = true := by decide +kernel

theorem disposition_at_1523 : dispositionTest 1523 = true := by decide +kernel

theorem disposition_at_1524 : dispositionTest 1524 = true := by decide +kernel

theorem disposition_at_1525 : dispositionTest 1525 = true := by decide +kernel

theorem disposition_at_1526 : dispositionTest 1526 = true := by decide +kernel

theorem disposition_at_1527 : dispositionTest 1527 = true := by decide +kernel

theorem disposition_at_1528 : dispositionTest 1528 = true := by decide +kernel

theorem disposition_at_1529 : dispositionTest 1529 = true := by decide +kernel

theorem disposition_at_1530 : dispositionTest 1530 = true := by decide +kernel

theorem disposition_at_1531 : dispositionTest 1531 = true := by decide +kernel

theorem disposition_at_1532 : dispositionTest 1532 = true := by decide +kernel

theorem disposition_at_1533 : dispositionTest 1533 = true := by decide +kernel

theorem disposition_at_1534 : dispositionTest 1534 = true := by decide +kernel

theorem disposition_at_1535 : dispositionTest 1535 = true := by decide +kernel

theorem disposition_interval_1504 : Interval dispositionTest 1504 1505 := by
  intro i hlo hhi
  have h : i = 1504 := by omega
  subst i
  exact disposition_at_1504


theorem disposition_interval_1505 : Interval dispositionTest 1505 1506 := by
  intro i hlo hhi
  have h : i = 1505 := by omega
  subst i
  exact disposition_at_1505


theorem disposition_interval_1506 : Interval dispositionTest 1506 1507 := by
  intro i hlo hhi
  have h : i = 1506 := by omega
  subst i
  exact disposition_at_1506


theorem disposition_interval_1507 : Interval dispositionTest 1507 1508 := by
  intro i hlo hhi
  have h : i = 1507 := by omega
  subst i
  exact disposition_at_1507


theorem disposition_interval_1508 : Interval dispositionTest 1508 1509 := by
  intro i hlo hhi
  have h : i = 1508 := by omega
  subst i
  exact disposition_at_1508


theorem disposition_interval_1509 : Interval dispositionTest 1509 1510 := by
  intro i hlo hhi
  have h : i = 1509 := by omega
  subst i
  exact disposition_at_1509


theorem disposition_interval_1510 : Interval dispositionTest 1510 1511 := by
  intro i hlo hhi
  have h : i = 1510 := by omega
  subst i
  exact disposition_at_1510


theorem disposition_interval_1511 : Interval dispositionTest 1511 1512 := by
  intro i hlo hhi
  have h : i = 1511 := by omega
  subst i
  exact disposition_at_1511


theorem disposition_interval_1512 : Interval dispositionTest 1512 1513 := by
  intro i hlo hhi
  have h : i = 1512 := by omega
  subst i
  exact disposition_at_1512


theorem disposition_interval_1513 : Interval dispositionTest 1513 1514 := by
  intro i hlo hhi
  have h : i = 1513 := by omega
  subst i
  exact disposition_at_1513


theorem disposition_interval_1514 : Interval dispositionTest 1514 1515 := by
  intro i hlo hhi
  have h : i = 1514 := by omega
  subst i
  exact disposition_at_1514


theorem disposition_interval_1515 : Interval dispositionTest 1515 1516 := by
  intro i hlo hhi
  have h : i = 1515 := by omega
  subst i
  exact disposition_at_1515


theorem disposition_interval_1516 : Interval dispositionTest 1516 1517 := by
  intro i hlo hhi
  have h : i = 1516 := by omega
  subst i
  exact disposition_at_1516


theorem disposition_interval_1517 : Interval dispositionTest 1517 1518 := by
  intro i hlo hhi
  have h : i = 1517 := by omega
  subst i
  exact disposition_at_1517


theorem disposition_interval_1518 : Interval dispositionTest 1518 1519 := by
  intro i hlo hhi
  have h : i = 1518 := by omega
  subst i
  exact disposition_at_1518


theorem disposition_interval_1519 : Interval dispositionTest 1519 1520 := by
  intro i hlo hhi
  have h : i = 1519 := by omega
  subst i
  exact disposition_at_1519


theorem disposition_interval_1520 : Interval dispositionTest 1520 1521 := by
  intro i hlo hhi
  have h : i = 1520 := by omega
  subst i
  exact disposition_at_1520


theorem disposition_interval_1521 : Interval dispositionTest 1521 1522 := by
  intro i hlo hhi
  have h : i = 1521 := by omega
  subst i
  exact disposition_at_1521


theorem disposition_interval_1522 : Interval dispositionTest 1522 1523 := by
  intro i hlo hhi
  have h : i = 1522 := by omega
  subst i
  exact disposition_at_1522


theorem disposition_interval_1523 : Interval dispositionTest 1523 1524 := by
  intro i hlo hhi
  have h : i = 1523 := by omega
  subst i
  exact disposition_at_1523


theorem disposition_interval_1524 : Interval dispositionTest 1524 1525 := by
  intro i hlo hhi
  have h : i = 1524 := by omega
  subst i
  exact disposition_at_1524


theorem disposition_interval_1525 : Interval dispositionTest 1525 1526 := by
  intro i hlo hhi
  have h : i = 1525 := by omega
  subst i
  exact disposition_at_1525


theorem disposition_interval_1526 : Interval dispositionTest 1526 1527 := by
  intro i hlo hhi
  have h : i = 1526 := by omega
  subst i
  exact disposition_at_1526


theorem disposition_interval_1527 : Interval dispositionTest 1527 1528 := by
  intro i hlo hhi
  have h : i = 1527 := by omega
  subst i
  exact disposition_at_1527


theorem disposition_interval_1528 : Interval dispositionTest 1528 1529 := by
  intro i hlo hhi
  have h : i = 1528 := by omega
  subst i
  exact disposition_at_1528


theorem disposition_interval_1529 : Interval dispositionTest 1529 1530 := by
  intro i hlo hhi
  have h : i = 1529 := by omega
  subst i
  exact disposition_at_1529


theorem disposition_interval_1530 : Interval dispositionTest 1530 1531 := by
  intro i hlo hhi
  have h : i = 1530 := by omega
  subst i
  exact disposition_at_1530


theorem disposition_interval_1531 : Interval dispositionTest 1531 1532 := by
  intro i hlo hhi
  have h : i = 1531 := by omega
  subst i
  exact disposition_at_1531


theorem disposition_interval_1532 : Interval dispositionTest 1532 1533 := by
  intro i hlo hhi
  have h : i = 1532 := by omega
  subst i
  exact disposition_at_1532


theorem disposition_interval_1533 : Interval dispositionTest 1533 1534 := by
  intro i hlo hhi
  have h : i = 1533 := by omega
  subst i
  exact disposition_at_1533


theorem disposition_interval_1534 : Interval dispositionTest 1534 1535 := by
  intro i hlo hhi
  have h : i = 1534 := by omega
  subst i
  exact disposition_at_1534


theorem disposition_interval_1535 : Interval dispositionTest 1535 1536 := by
  intro i hlo hhi
  have h : i = 1535 := by omega
  subst i
  exact disposition_at_1535

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
