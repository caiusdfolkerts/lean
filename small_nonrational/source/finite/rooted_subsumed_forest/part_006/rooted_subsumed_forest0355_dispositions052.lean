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
theorem disposition_at_1664 : dispositionTest 1664 = true := by decide +kernel

theorem disposition_at_1665 : dispositionTest 1665 = true := by decide +kernel

theorem disposition_at_1666 : dispositionTest 1666 = true := by decide +kernel

theorem disposition_at_1667 : dispositionTest 1667 = true := by decide +kernel

theorem disposition_at_1668 : dispositionTest 1668 = true := by decide +kernel


theorem disposition_at_1669 : dispositionTest 1669 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1669).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1032.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1032) = true
  rw [Nonrational.OldTerminalMatches.M016.r1032_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1670 : dispositionTest 1670 = true := by decide +kernel

theorem disposition_at_1671 : dispositionTest 1671 = true := by decide +kernel

theorem disposition_at_1672 : dispositionTest 1672 = true := by decide +kernel

theorem disposition_at_1673 : dispositionTest 1673 = true := by decide +kernel

theorem disposition_at_1674 : dispositionTest 1674 = true := by decide +kernel

theorem disposition_at_1675 : dispositionTest 1675 = true := by decide +kernel

theorem disposition_at_1676 : dispositionTest 1676 = true := by decide +kernel

theorem disposition_at_1677 : dispositionTest 1677 = true := by decide +kernel

theorem disposition_at_1678 : dispositionTest 1678 = true := by decide +kernel

theorem disposition_at_1679 : dispositionTest 1679 = true := by decide +kernel

theorem disposition_at_1680 : dispositionTest 1680 = true := by decide +kernel

theorem disposition_at_1681 : dispositionTest 1681 = true := by decide +kernel

theorem disposition_at_1682 : dispositionTest 1682 = true := by decide +kernel

theorem disposition_at_1683 : dispositionTest 1683 = true := by decide +kernel

theorem disposition_at_1684 : dispositionTest 1684 = true := by decide +kernel

theorem disposition_at_1685 : dispositionTest 1685 = true := by decide +kernel

theorem disposition_at_1686 : dispositionTest 1686 = true := by decide +kernel

theorem disposition_at_1687 : dispositionTest 1687 = true := by decide +kernel

theorem disposition_at_1688 : dispositionTest 1688 = true := by decide +kernel

theorem disposition_at_1689 : dispositionTest 1689 = true := by decide +kernel

theorem disposition_at_1690 : dispositionTest 1690 = true := by decide +kernel

theorem disposition_at_1691 : dispositionTest 1691 = true := by decide +kernel

theorem disposition_at_1692 : dispositionTest 1692 = true := by decide +kernel

theorem disposition_at_1693 : dispositionTest 1693 = true := by decide +kernel

theorem disposition_at_1694 : dispositionTest 1694 = true := by decide +kernel

theorem disposition_at_1695 : dispositionTest 1695 = true := by decide +kernel

theorem disposition_interval_1664 : Interval dispositionTest 1664 1665 := by
  intro i hlo hhi
  have h : i = 1664 := by omega
  subst i
  exact disposition_at_1664


theorem disposition_interval_1665 : Interval dispositionTest 1665 1666 := by
  intro i hlo hhi
  have h : i = 1665 := by omega
  subst i
  exact disposition_at_1665


theorem disposition_interval_1666 : Interval dispositionTest 1666 1667 := by
  intro i hlo hhi
  have h : i = 1666 := by omega
  subst i
  exact disposition_at_1666


theorem disposition_interval_1667 : Interval dispositionTest 1667 1668 := by
  intro i hlo hhi
  have h : i = 1667 := by omega
  subst i
  exact disposition_at_1667


theorem disposition_interval_1668 : Interval dispositionTest 1668 1669 := by
  intro i hlo hhi
  have h : i = 1668 := by omega
  subst i
  exact disposition_at_1668


theorem disposition_interval_1669 : Interval dispositionTest 1669 1670 := by
  intro i hlo hhi
  have h : i = 1669 := by omega
  subst i
  exact disposition_at_1669


theorem disposition_interval_1670 : Interval dispositionTest 1670 1671 := by
  intro i hlo hhi
  have h : i = 1670 := by omega
  subst i
  exact disposition_at_1670


theorem disposition_interval_1671 : Interval dispositionTest 1671 1672 := by
  intro i hlo hhi
  have h : i = 1671 := by omega
  subst i
  exact disposition_at_1671


theorem disposition_interval_1672 : Interval dispositionTest 1672 1673 := by
  intro i hlo hhi
  have h : i = 1672 := by omega
  subst i
  exact disposition_at_1672


theorem disposition_interval_1673 : Interval dispositionTest 1673 1674 := by
  intro i hlo hhi
  have h : i = 1673 := by omega
  subst i
  exact disposition_at_1673


theorem disposition_interval_1674 : Interval dispositionTest 1674 1675 := by
  intro i hlo hhi
  have h : i = 1674 := by omega
  subst i
  exact disposition_at_1674


theorem disposition_interval_1675 : Interval dispositionTest 1675 1676 := by
  intro i hlo hhi
  have h : i = 1675 := by omega
  subst i
  exact disposition_at_1675


theorem disposition_interval_1676 : Interval dispositionTest 1676 1677 := by
  intro i hlo hhi
  have h : i = 1676 := by omega
  subst i
  exact disposition_at_1676


theorem disposition_interval_1677 : Interval dispositionTest 1677 1678 := by
  intro i hlo hhi
  have h : i = 1677 := by omega
  subst i
  exact disposition_at_1677


theorem disposition_interval_1678 : Interval dispositionTest 1678 1679 := by
  intro i hlo hhi
  have h : i = 1678 := by omega
  subst i
  exact disposition_at_1678


theorem disposition_interval_1679 : Interval dispositionTest 1679 1680 := by
  intro i hlo hhi
  have h : i = 1679 := by omega
  subst i
  exact disposition_at_1679


theorem disposition_interval_1680 : Interval dispositionTest 1680 1681 := by
  intro i hlo hhi
  have h : i = 1680 := by omega
  subst i
  exact disposition_at_1680


theorem disposition_interval_1681 : Interval dispositionTest 1681 1682 := by
  intro i hlo hhi
  have h : i = 1681 := by omega
  subst i
  exact disposition_at_1681


theorem disposition_interval_1682 : Interval dispositionTest 1682 1683 := by
  intro i hlo hhi
  have h : i = 1682 := by omega
  subst i
  exact disposition_at_1682


theorem disposition_interval_1683 : Interval dispositionTest 1683 1684 := by
  intro i hlo hhi
  have h : i = 1683 := by omega
  subst i
  exact disposition_at_1683


theorem disposition_interval_1684 : Interval dispositionTest 1684 1685 := by
  intro i hlo hhi
  have h : i = 1684 := by omega
  subst i
  exact disposition_at_1684


theorem disposition_interval_1685 : Interval dispositionTest 1685 1686 := by
  intro i hlo hhi
  have h : i = 1685 := by omega
  subst i
  exact disposition_at_1685


theorem disposition_interval_1686 : Interval dispositionTest 1686 1687 := by
  intro i hlo hhi
  have h : i = 1686 := by omega
  subst i
  exact disposition_at_1686


theorem disposition_interval_1687 : Interval dispositionTest 1687 1688 := by
  intro i hlo hhi
  have h : i = 1687 := by omega
  subst i
  exact disposition_at_1687


theorem disposition_interval_1688 : Interval dispositionTest 1688 1689 := by
  intro i hlo hhi
  have h : i = 1688 := by omega
  subst i
  exact disposition_at_1688


theorem disposition_interval_1689 : Interval dispositionTest 1689 1690 := by
  intro i hlo hhi
  have h : i = 1689 := by omega
  subst i
  exact disposition_at_1689


theorem disposition_interval_1690 : Interval dispositionTest 1690 1691 := by
  intro i hlo hhi
  have h : i = 1690 := by omega
  subst i
  exact disposition_at_1690


theorem disposition_interval_1691 : Interval dispositionTest 1691 1692 := by
  intro i hlo hhi
  have h : i = 1691 := by omega
  subst i
  exact disposition_at_1691


theorem disposition_interval_1692 : Interval dispositionTest 1692 1693 := by
  intro i hlo hhi
  have h : i = 1692 := by omega
  subst i
  exact disposition_at_1692


theorem disposition_interval_1693 : Interval dispositionTest 1693 1694 := by
  intro i hlo hhi
  have h : i = 1693 := by omega
  subst i
  exact disposition_at_1693


theorem disposition_interval_1694 : Interval dispositionTest 1694 1695 := by
  intro i hlo hhi
  have h : i = 1694 := by omega
  subst i
  exact disposition_at_1694


theorem disposition_interval_1695 : Interval dispositionTest 1695 1696 := by
  intro i hlo hhi
  have h : i = 1695 := by omega
  subst i
  exact disposition_at_1695

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
