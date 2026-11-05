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
theorem disposition_at_1568 : dispositionTest 1568 = true := by decide +kernel

theorem disposition_at_1569 : dispositionTest 1569 = true := by decide +kernel

theorem disposition_at_1570 : dispositionTest 1570 = true := by decide +kernel

theorem disposition_at_1571 : dispositionTest 1571 = true := by decide +kernel

theorem disposition_at_1572 : dispositionTest 1572 = true := by decide +kernel

theorem disposition_at_1573 : dispositionTest 1573 = true := by decide +kernel

theorem disposition_at_1574 : dispositionTest 1574 = true := by decide +kernel

theorem disposition_at_1575 : dispositionTest 1575 = true := by decide +kernel

theorem disposition_at_1576 : dispositionTest 1576 = true := by decide +kernel

theorem disposition_at_1577 : dispositionTest 1577 = true := by decide +kernel

theorem disposition_at_1578 : dispositionTest 1578 = true := by decide +kernel

theorem disposition_at_1579 : dispositionTest 1579 = true := by decide +kernel

theorem disposition_at_1580 : dispositionTest 1580 = true := by decide +kernel

theorem disposition_at_1581 : dispositionTest 1581 = true := by decide +kernel

theorem disposition_at_1582 : dispositionTest 1582 = true := by decide +kernel

theorem disposition_at_1583 : dispositionTest 1583 = true := by decide +kernel

theorem disposition_at_1584 : dispositionTest 1584 = true := by decide +kernel

theorem disposition_at_1585 : dispositionTest 1585 = true := by decide +kernel

theorem disposition_at_1586 : dispositionTest 1586 = true := by decide +kernel

theorem disposition_at_1587 : dispositionTest 1587 = true := by decide +kernel

theorem disposition_at_1588 : dispositionTest 1588 = true := by decide +kernel

theorem disposition_at_1589 : dispositionTest 1589 = true := by decide +kernel

theorem disposition_at_1590 : dispositionTest 1590 = true := by decide +kernel

theorem disposition_at_1591 : dispositionTest 1591 = true := by decide +kernel

theorem disposition_at_1592 : dispositionTest 1592 = true := by decide +kernel

theorem disposition_at_1593 : dispositionTest 1593 = true := by decide +kernel

theorem disposition_at_1594 : dispositionTest 1594 = true := by decide +kernel

theorem disposition_at_1595 : dispositionTest 1595 = true := by decide +kernel

theorem disposition_at_1596 : dispositionTest 1596 = true := by decide +kernel

theorem disposition_at_1597 : dispositionTest 1597 = true := by decide +kernel

theorem disposition_at_1598 : dispositionTest 1598 = true := by decide +kernel

theorem disposition_at_1599 : dispositionTest 1599 = true := by decide +kernel

theorem disposition_interval_1568 : Interval dispositionTest 1568 1569 := by
  intro i hlo hhi
  have h : i = 1568 := by omega
  subst i
  exact disposition_at_1568


theorem disposition_interval_1569 : Interval dispositionTest 1569 1570 := by
  intro i hlo hhi
  have h : i = 1569 := by omega
  subst i
  exact disposition_at_1569


theorem disposition_interval_1570 : Interval dispositionTest 1570 1571 := by
  intro i hlo hhi
  have h : i = 1570 := by omega
  subst i
  exact disposition_at_1570


theorem disposition_interval_1571 : Interval dispositionTest 1571 1572 := by
  intro i hlo hhi
  have h : i = 1571 := by omega
  subst i
  exact disposition_at_1571


theorem disposition_interval_1572 : Interval dispositionTest 1572 1573 := by
  intro i hlo hhi
  have h : i = 1572 := by omega
  subst i
  exact disposition_at_1572


theorem disposition_interval_1573 : Interval dispositionTest 1573 1574 := by
  intro i hlo hhi
  have h : i = 1573 := by omega
  subst i
  exact disposition_at_1573


theorem disposition_interval_1574 : Interval dispositionTest 1574 1575 := by
  intro i hlo hhi
  have h : i = 1574 := by omega
  subst i
  exact disposition_at_1574


theorem disposition_interval_1575 : Interval dispositionTest 1575 1576 := by
  intro i hlo hhi
  have h : i = 1575 := by omega
  subst i
  exact disposition_at_1575


theorem disposition_interval_1576 : Interval dispositionTest 1576 1577 := by
  intro i hlo hhi
  have h : i = 1576 := by omega
  subst i
  exact disposition_at_1576


theorem disposition_interval_1577 : Interval dispositionTest 1577 1578 := by
  intro i hlo hhi
  have h : i = 1577 := by omega
  subst i
  exact disposition_at_1577


theorem disposition_interval_1578 : Interval dispositionTest 1578 1579 := by
  intro i hlo hhi
  have h : i = 1578 := by omega
  subst i
  exact disposition_at_1578


theorem disposition_interval_1579 : Interval dispositionTest 1579 1580 := by
  intro i hlo hhi
  have h : i = 1579 := by omega
  subst i
  exact disposition_at_1579


theorem disposition_interval_1580 : Interval dispositionTest 1580 1581 := by
  intro i hlo hhi
  have h : i = 1580 := by omega
  subst i
  exact disposition_at_1580


theorem disposition_interval_1581 : Interval dispositionTest 1581 1582 := by
  intro i hlo hhi
  have h : i = 1581 := by omega
  subst i
  exact disposition_at_1581


theorem disposition_interval_1582 : Interval dispositionTest 1582 1583 := by
  intro i hlo hhi
  have h : i = 1582 := by omega
  subst i
  exact disposition_at_1582


theorem disposition_interval_1583 : Interval dispositionTest 1583 1584 := by
  intro i hlo hhi
  have h : i = 1583 := by omega
  subst i
  exact disposition_at_1583


theorem disposition_interval_1584 : Interval dispositionTest 1584 1585 := by
  intro i hlo hhi
  have h : i = 1584 := by omega
  subst i
  exact disposition_at_1584


theorem disposition_interval_1585 : Interval dispositionTest 1585 1586 := by
  intro i hlo hhi
  have h : i = 1585 := by omega
  subst i
  exact disposition_at_1585


theorem disposition_interval_1586 : Interval dispositionTest 1586 1587 := by
  intro i hlo hhi
  have h : i = 1586 := by omega
  subst i
  exact disposition_at_1586


theorem disposition_interval_1587 : Interval dispositionTest 1587 1588 := by
  intro i hlo hhi
  have h : i = 1587 := by omega
  subst i
  exact disposition_at_1587


theorem disposition_interval_1588 : Interval dispositionTest 1588 1589 := by
  intro i hlo hhi
  have h : i = 1588 := by omega
  subst i
  exact disposition_at_1588


theorem disposition_interval_1589 : Interval dispositionTest 1589 1590 := by
  intro i hlo hhi
  have h : i = 1589 := by omega
  subst i
  exact disposition_at_1589


theorem disposition_interval_1590 : Interval dispositionTest 1590 1591 := by
  intro i hlo hhi
  have h : i = 1590 := by omega
  subst i
  exact disposition_at_1590


theorem disposition_interval_1591 : Interval dispositionTest 1591 1592 := by
  intro i hlo hhi
  have h : i = 1591 := by omega
  subst i
  exact disposition_at_1591


theorem disposition_interval_1592 : Interval dispositionTest 1592 1593 := by
  intro i hlo hhi
  have h : i = 1592 := by omega
  subst i
  exact disposition_at_1592


theorem disposition_interval_1593 : Interval dispositionTest 1593 1594 := by
  intro i hlo hhi
  have h : i = 1593 := by omega
  subst i
  exact disposition_at_1593


theorem disposition_interval_1594 : Interval dispositionTest 1594 1595 := by
  intro i hlo hhi
  have h : i = 1594 := by omega
  subst i
  exact disposition_at_1594


theorem disposition_interval_1595 : Interval dispositionTest 1595 1596 := by
  intro i hlo hhi
  have h : i = 1595 := by omega
  subst i
  exact disposition_at_1595


theorem disposition_interval_1596 : Interval dispositionTest 1596 1597 := by
  intro i hlo hhi
  have h : i = 1596 := by omega
  subst i
  exact disposition_at_1596


theorem disposition_interval_1597 : Interval dispositionTest 1597 1598 := by
  intro i hlo hhi
  have h : i = 1597 := by omega
  subst i
  exact disposition_at_1597


theorem disposition_interval_1598 : Interval dispositionTest 1598 1599 := by
  intro i hlo hhi
  have h : i = 1598 := by omega
  subst i
  exact disposition_at_1598


theorem disposition_interval_1599 : Interval dispositionTest 1599 1600 := by
  intro i hlo hhi
  have h : i = 1599 := by omega
  subst i
  exact disposition_at_1599

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
