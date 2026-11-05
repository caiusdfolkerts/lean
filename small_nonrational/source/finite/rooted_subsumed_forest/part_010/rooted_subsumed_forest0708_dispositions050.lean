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
theorem disposition_at_1600 : dispositionTest 1600 = true := by decide +kernel

theorem disposition_at_1601 : dispositionTest 1601 = true := by decide +kernel

theorem disposition_at_1602 : dispositionTest 1602 = true := by decide +kernel

theorem disposition_at_1603 : dispositionTest 1603 = true := by decide +kernel

theorem disposition_at_1604 : dispositionTest 1604 = true := by decide +kernel

theorem disposition_at_1605 : dispositionTest 1605 = true := by decide +kernel

theorem disposition_at_1606 : dispositionTest 1606 = true := by decide +kernel

theorem disposition_at_1607 : dispositionTest 1607 = true := by decide +kernel

theorem disposition_at_1608 : dispositionTest 1608 = true := by decide +kernel

theorem disposition_at_1609 : dispositionTest 1609 = true := by decide +kernel

theorem disposition_at_1610 : dispositionTest 1610 = true := by decide +kernel

theorem disposition_at_1611 : dispositionTest 1611 = true := by decide +kernel

theorem disposition_at_1612 : dispositionTest 1612 = true := by decide +kernel

theorem disposition_at_1613 : dispositionTest 1613 = true := by decide +kernel

theorem disposition_at_1614 : dispositionTest 1614 = true := by decide +kernel

theorem disposition_at_1615 : dispositionTest 1615 = true := by decide +kernel

theorem disposition_at_1616 : dispositionTest 1616 = true := by decide +kernel

theorem disposition_at_1617 : dispositionTest 1617 = true := by decide +kernel

theorem disposition_at_1618 : dispositionTest 1618 = true := by decide +kernel

theorem disposition_at_1619 : dispositionTest 1619 = true := by decide +kernel

theorem disposition_at_1620 : dispositionTest 1620 = true := by decide +kernel

theorem disposition_at_1621 : dispositionTest 1621 = true := by decide +kernel

theorem disposition_at_1622 : dispositionTest 1622 = true := by decide +kernel

theorem disposition_at_1623 : dispositionTest 1623 = true := by decide +kernel

theorem disposition_at_1624 : dispositionTest 1624 = true := by decide +kernel

theorem disposition_at_1625 : dispositionTest 1625 = true := by decide +kernel

theorem disposition_at_1626 : dispositionTest 1626 = true := by decide +kernel

theorem disposition_at_1627 : dispositionTest 1627 = true := by decide +kernel

theorem disposition_at_1628 : dispositionTest 1628 = true := by decide +kernel

theorem disposition_at_1629 : dispositionTest 1629 = true := by decide +kernel

theorem disposition_at_1630 : dispositionTest 1630 = true := by decide +kernel

theorem disposition_interval_1600 : Interval dispositionTest 1600 1601 := by
  intro i hlo hhi
  have h : i = 1600 := by omega
  subst i
  exact disposition_at_1600


theorem disposition_interval_1601 : Interval dispositionTest 1601 1602 := by
  intro i hlo hhi
  have h : i = 1601 := by omega
  subst i
  exact disposition_at_1601


theorem disposition_interval_1602 : Interval dispositionTest 1602 1603 := by
  intro i hlo hhi
  have h : i = 1602 := by omega
  subst i
  exact disposition_at_1602


theorem disposition_interval_1603 : Interval dispositionTest 1603 1604 := by
  intro i hlo hhi
  have h : i = 1603 := by omega
  subst i
  exact disposition_at_1603


theorem disposition_interval_1604 : Interval dispositionTest 1604 1605 := by
  intro i hlo hhi
  have h : i = 1604 := by omega
  subst i
  exact disposition_at_1604


theorem disposition_interval_1605 : Interval dispositionTest 1605 1606 := by
  intro i hlo hhi
  have h : i = 1605 := by omega
  subst i
  exact disposition_at_1605


theorem disposition_interval_1606 : Interval dispositionTest 1606 1607 := by
  intro i hlo hhi
  have h : i = 1606 := by omega
  subst i
  exact disposition_at_1606


theorem disposition_interval_1607 : Interval dispositionTest 1607 1608 := by
  intro i hlo hhi
  have h : i = 1607 := by omega
  subst i
  exact disposition_at_1607


theorem disposition_interval_1608 : Interval dispositionTest 1608 1609 := by
  intro i hlo hhi
  have h : i = 1608 := by omega
  subst i
  exact disposition_at_1608


theorem disposition_interval_1609 : Interval dispositionTest 1609 1610 := by
  intro i hlo hhi
  have h : i = 1609 := by omega
  subst i
  exact disposition_at_1609


theorem disposition_interval_1610 : Interval dispositionTest 1610 1611 := by
  intro i hlo hhi
  have h : i = 1610 := by omega
  subst i
  exact disposition_at_1610


theorem disposition_interval_1611 : Interval dispositionTest 1611 1612 := by
  intro i hlo hhi
  have h : i = 1611 := by omega
  subst i
  exact disposition_at_1611


theorem disposition_interval_1612 : Interval dispositionTest 1612 1613 := by
  intro i hlo hhi
  have h : i = 1612 := by omega
  subst i
  exact disposition_at_1612


theorem disposition_interval_1613 : Interval dispositionTest 1613 1614 := by
  intro i hlo hhi
  have h : i = 1613 := by omega
  subst i
  exact disposition_at_1613


theorem disposition_interval_1614 : Interval dispositionTest 1614 1615 := by
  intro i hlo hhi
  have h : i = 1614 := by omega
  subst i
  exact disposition_at_1614


theorem disposition_interval_1615 : Interval dispositionTest 1615 1616 := by
  intro i hlo hhi
  have h : i = 1615 := by omega
  subst i
  exact disposition_at_1615


theorem disposition_interval_1616 : Interval dispositionTest 1616 1617 := by
  intro i hlo hhi
  have h : i = 1616 := by omega
  subst i
  exact disposition_at_1616


theorem disposition_interval_1617 : Interval dispositionTest 1617 1618 := by
  intro i hlo hhi
  have h : i = 1617 := by omega
  subst i
  exact disposition_at_1617


theorem disposition_interval_1618 : Interval dispositionTest 1618 1619 := by
  intro i hlo hhi
  have h : i = 1618 := by omega
  subst i
  exact disposition_at_1618


theorem disposition_interval_1619 : Interval dispositionTest 1619 1620 := by
  intro i hlo hhi
  have h : i = 1619 := by omega
  subst i
  exact disposition_at_1619


theorem disposition_interval_1620 : Interval dispositionTest 1620 1621 := by
  intro i hlo hhi
  have h : i = 1620 := by omega
  subst i
  exact disposition_at_1620


theorem disposition_interval_1621 : Interval dispositionTest 1621 1622 := by
  intro i hlo hhi
  have h : i = 1621 := by omega
  subst i
  exact disposition_at_1621


theorem disposition_interval_1622 : Interval dispositionTest 1622 1623 := by
  intro i hlo hhi
  have h : i = 1622 := by omega
  subst i
  exact disposition_at_1622


theorem disposition_interval_1623 : Interval dispositionTest 1623 1624 := by
  intro i hlo hhi
  have h : i = 1623 := by omega
  subst i
  exact disposition_at_1623


theorem disposition_interval_1624 : Interval dispositionTest 1624 1625 := by
  intro i hlo hhi
  have h : i = 1624 := by omega
  subst i
  exact disposition_at_1624


theorem disposition_interval_1625 : Interval dispositionTest 1625 1626 := by
  intro i hlo hhi
  have h : i = 1625 := by omega
  subst i
  exact disposition_at_1625


theorem disposition_interval_1626 : Interval dispositionTest 1626 1627 := by
  intro i hlo hhi
  have h : i = 1626 := by omega
  subst i
  exact disposition_at_1626


theorem disposition_interval_1627 : Interval dispositionTest 1627 1628 := by
  intro i hlo hhi
  have h : i = 1627 := by omega
  subst i
  exact disposition_at_1627


theorem disposition_interval_1628 : Interval dispositionTest 1628 1629 := by
  intro i hlo hhi
  have h : i = 1628 := by omega
  subst i
  exact disposition_at_1628


theorem disposition_interval_1629 : Interval dispositionTest 1629 1630 := by
  intro i hlo hhi
  have h : i = 1629 := by omega
  subst i
  exact disposition_at_1629


theorem disposition_interval_1630 : Interval dispositionTest 1630 1631 := by
  intro i hlo hhi
  have h : i = 1630 := by omega
  subst i
  exact disposition_at_1630

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
