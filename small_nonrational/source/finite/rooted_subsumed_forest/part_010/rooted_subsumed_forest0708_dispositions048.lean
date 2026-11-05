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
theorem disposition_at_1536 : dispositionTest 1536 = true := by decide +kernel

theorem disposition_at_1537 : dispositionTest 1537 = true := by decide +kernel

theorem disposition_at_1538 : dispositionTest 1538 = true := by decide +kernel

theorem disposition_at_1539 : dispositionTest 1539 = true := by decide +kernel

theorem disposition_at_1540 : dispositionTest 1540 = true := by decide +kernel

theorem disposition_at_1541 : dispositionTest 1541 = true := by decide +kernel

theorem disposition_at_1542 : dispositionTest 1542 = true := by decide +kernel

theorem disposition_at_1543 : dispositionTest 1543 = true := by decide +kernel

theorem disposition_at_1544 : dispositionTest 1544 = true := by decide +kernel

theorem disposition_at_1545 : dispositionTest 1545 = true := by decide +kernel

theorem disposition_at_1546 : dispositionTest 1546 = true := by decide +kernel

theorem disposition_at_1547 : dispositionTest 1547 = true := by decide +kernel

theorem disposition_at_1548 : dispositionTest 1548 = true := by decide +kernel

theorem disposition_at_1549 : dispositionTest 1549 = true := by decide +kernel

theorem disposition_at_1550 : dispositionTest 1550 = true := by decide +kernel

theorem disposition_at_1551 : dispositionTest 1551 = true := by decide +kernel

theorem disposition_at_1552 : dispositionTest 1552 = true := by decide +kernel

theorem disposition_at_1553 : dispositionTest 1553 = true := by decide +kernel

theorem disposition_at_1554 : dispositionTest 1554 = true := by decide +kernel

theorem disposition_at_1555 : dispositionTest 1555 = true := by decide +kernel

theorem disposition_at_1556 : dispositionTest 1556 = true := by decide +kernel

theorem disposition_at_1557 : dispositionTest 1557 = true := by decide +kernel

theorem disposition_at_1558 : dispositionTest 1558 = true := by decide +kernel

theorem disposition_at_1559 : dispositionTest 1559 = true := by decide +kernel

theorem disposition_at_1560 : dispositionTest 1560 = true := by decide +kernel

theorem disposition_at_1561 : dispositionTest 1561 = true := by decide +kernel

theorem disposition_at_1562 : dispositionTest 1562 = true := by decide +kernel

theorem disposition_at_1563 : dispositionTest 1563 = true := by decide +kernel

theorem disposition_at_1564 : dispositionTest 1564 = true := by decide +kernel

theorem disposition_at_1565 : dispositionTest 1565 = true := by decide +kernel

theorem disposition_at_1566 : dispositionTest 1566 = true := by decide +kernel

theorem disposition_at_1567 : dispositionTest 1567 = true := by decide +kernel

theorem disposition_interval_1536 : Interval dispositionTest 1536 1537 := by
  intro i hlo hhi
  have h : i = 1536 := by omega
  subst i
  exact disposition_at_1536


theorem disposition_interval_1537 : Interval dispositionTest 1537 1538 := by
  intro i hlo hhi
  have h : i = 1537 := by omega
  subst i
  exact disposition_at_1537


theorem disposition_interval_1538 : Interval dispositionTest 1538 1539 := by
  intro i hlo hhi
  have h : i = 1538 := by omega
  subst i
  exact disposition_at_1538


theorem disposition_interval_1539 : Interval dispositionTest 1539 1540 := by
  intro i hlo hhi
  have h : i = 1539 := by omega
  subst i
  exact disposition_at_1539


theorem disposition_interval_1540 : Interval dispositionTest 1540 1541 := by
  intro i hlo hhi
  have h : i = 1540 := by omega
  subst i
  exact disposition_at_1540


theorem disposition_interval_1541 : Interval dispositionTest 1541 1542 := by
  intro i hlo hhi
  have h : i = 1541 := by omega
  subst i
  exact disposition_at_1541


theorem disposition_interval_1542 : Interval dispositionTest 1542 1543 := by
  intro i hlo hhi
  have h : i = 1542 := by omega
  subst i
  exact disposition_at_1542


theorem disposition_interval_1543 : Interval dispositionTest 1543 1544 := by
  intro i hlo hhi
  have h : i = 1543 := by omega
  subst i
  exact disposition_at_1543


theorem disposition_interval_1544 : Interval dispositionTest 1544 1545 := by
  intro i hlo hhi
  have h : i = 1544 := by omega
  subst i
  exact disposition_at_1544


theorem disposition_interval_1545 : Interval dispositionTest 1545 1546 := by
  intro i hlo hhi
  have h : i = 1545 := by omega
  subst i
  exact disposition_at_1545


theorem disposition_interval_1546 : Interval dispositionTest 1546 1547 := by
  intro i hlo hhi
  have h : i = 1546 := by omega
  subst i
  exact disposition_at_1546


theorem disposition_interval_1547 : Interval dispositionTest 1547 1548 := by
  intro i hlo hhi
  have h : i = 1547 := by omega
  subst i
  exact disposition_at_1547


theorem disposition_interval_1548 : Interval dispositionTest 1548 1549 := by
  intro i hlo hhi
  have h : i = 1548 := by omega
  subst i
  exact disposition_at_1548


theorem disposition_interval_1549 : Interval dispositionTest 1549 1550 := by
  intro i hlo hhi
  have h : i = 1549 := by omega
  subst i
  exact disposition_at_1549


theorem disposition_interval_1550 : Interval dispositionTest 1550 1551 := by
  intro i hlo hhi
  have h : i = 1550 := by omega
  subst i
  exact disposition_at_1550


theorem disposition_interval_1551 : Interval dispositionTest 1551 1552 := by
  intro i hlo hhi
  have h : i = 1551 := by omega
  subst i
  exact disposition_at_1551


theorem disposition_interval_1552 : Interval dispositionTest 1552 1553 := by
  intro i hlo hhi
  have h : i = 1552 := by omega
  subst i
  exact disposition_at_1552


theorem disposition_interval_1553 : Interval dispositionTest 1553 1554 := by
  intro i hlo hhi
  have h : i = 1553 := by omega
  subst i
  exact disposition_at_1553


theorem disposition_interval_1554 : Interval dispositionTest 1554 1555 := by
  intro i hlo hhi
  have h : i = 1554 := by omega
  subst i
  exact disposition_at_1554


theorem disposition_interval_1555 : Interval dispositionTest 1555 1556 := by
  intro i hlo hhi
  have h : i = 1555 := by omega
  subst i
  exact disposition_at_1555


theorem disposition_interval_1556 : Interval dispositionTest 1556 1557 := by
  intro i hlo hhi
  have h : i = 1556 := by omega
  subst i
  exact disposition_at_1556


theorem disposition_interval_1557 : Interval dispositionTest 1557 1558 := by
  intro i hlo hhi
  have h : i = 1557 := by omega
  subst i
  exact disposition_at_1557


theorem disposition_interval_1558 : Interval dispositionTest 1558 1559 := by
  intro i hlo hhi
  have h : i = 1558 := by omega
  subst i
  exact disposition_at_1558


theorem disposition_interval_1559 : Interval dispositionTest 1559 1560 := by
  intro i hlo hhi
  have h : i = 1559 := by omega
  subst i
  exact disposition_at_1559


theorem disposition_interval_1560 : Interval dispositionTest 1560 1561 := by
  intro i hlo hhi
  have h : i = 1560 := by omega
  subst i
  exact disposition_at_1560


theorem disposition_interval_1561 : Interval dispositionTest 1561 1562 := by
  intro i hlo hhi
  have h : i = 1561 := by omega
  subst i
  exact disposition_at_1561


theorem disposition_interval_1562 : Interval dispositionTest 1562 1563 := by
  intro i hlo hhi
  have h : i = 1562 := by omega
  subst i
  exact disposition_at_1562


theorem disposition_interval_1563 : Interval dispositionTest 1563 1564 := by
  intro i hlo hhi
  have h : i = 1563 := by omega
  subst i
  exact disposition_at_1563


theorem disposition_interval_1564 : Interval dispositionTest 1564 1565 := by
  intro i hlo hhi
  have h : i = 1564 := by omega
  subst i
  exact disposition_at_1564


theorem disposition_interval_1565 : Interval dispositionTest 1565 1566 := by
  intro i hlo hhi
  have h : i = 1565 := by omega
  subst i
  exact disposition_at_1565


theorem disposition_interval_1566 : Interval dispositionTest 1566 1567 := by
  intro i hlo hhi
  have h : i = 1566 := by omega
  subst i
  exact disposition_at_1566


theorem disposition_interval_1567 : Interval dispositionTest 1567 1568 := by
  intro i hlo hhi
  have h : i = 1567 := by omega
  subst i
  exact disposition_at_1567

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
