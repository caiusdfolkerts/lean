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

theorem disposition_at_1632 : dispositionTest 1632 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1632).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1026.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1026) = true
  rw [Nonrational.OldTerminalMatches.M016.r1026_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1633 : dispositionTest 1633 = true := by decide +kernel

theorem disposition_at_1634 : dispositionTest 1634 = true := by decide +kernel


theorem disposition_at_1635 : dispositionTest 1635 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1635).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1027.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1027) = true
  rw [Nonrational.OldTerminalMatches.M016.r1027_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_1636 : dispositionTest 1636 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1636).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1028.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1028) = true
  rw [Nonrational.OldTerminalMatches.M016.r1028_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_1637 : dispositionTest 1637 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1637).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1029.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1029) = true
  rw [Nonrational.OldTerminalMatches.M016.r1029_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_1638 : dispositionTest 1638 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1638).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1030.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1030) = true
  rw [Nonrational.OldTerminalMatches.M016.r1030_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1639 : dispositionTest 1639 = true := by decide +kernel


theorem disposition_at_1640 : dispositionTest 1640 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1640).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1031.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1031) = true
  rw [Nonrational.OldTerminalMatches.M016.r1031_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1641 : dispositionTest 1641 = true := by decide +kernel

theorem disposition_at_1642 : dispositionTest 1642 = true := by decide +kernel

theorem disposition_at_1643 : dispositionTest 1643 = true := by decide +kernel

theorem disposition_at_1644 : dispositionTest 1644 = true := by decide +kernel

theorem disposition_at_1645 : dispositionTest 1645 = true := by decide +kernel

theorem disposition_at_1646 : dispositionTest 1646 = true := by decide +kernel

theorem disposition_at_1647 : dispositionTest 1647 = true := by decide +kernel

theorem disposition_at_1648 : dispositionTest 1648 = true := by decide +kernel

theorem disposition_at_1649 : dispositionTest 1649 = true := by decide +kernel

theorem disposition_at_1650 : dispositionTest 1650 = true := by decide +kernel

theorem disposition_at_1651 : dispositionTest 1651 = true := by decide +kernel

theorem disposition_at_1652 : dispositionTest 1652 = true := by decide +kernel

theorem disposition_at_1653 : dispositionTest 1653 = true := by decide +kernel

theorem disposition_at_1654 : dispositionTest 1654 = true := by decide +kernel

theorem disposition_at_1655 : dispositionTest 1655 = true := by decide +kernel

theorem disposition_at_1656 : dispositionTest 1656 = true := by decide +kernel

theorem disposition_at_1657 : dispositionTest 1657 = true := by decide +kernel

theorem disposition_at_1658 : dispositionTest 1658 = true := by decide +kernel

theorem disposition_at_1659 : dispositionTest 1659 = true := by decide +kernel

theorem disposition_at_1660 : dispositionTest 1660 = true := by decide +kernel

theorem disposition_at_1661 : dispositionTest 1661 = true := by decide +kernel

theorem disposition_at_1662 : dispositionTest 1662 = true := by decide +kernel

theorem disposition_at_1663 : dispositionTest 1663 = true := by decide +kernel

theorem disposition_interval_1632 : Interval dispositionTest 1632 1633 := by
  intro i hlo hhi
  have h : i = 1632 := by omega
  subst i
  exact disposition_at_1632


theorem disposition_interval_1633 : Interval dispositionTest 1633 1634 := by
  intro i hlo hhi
  have h : i = 1633 := by omega
  subst i
  exact disposition_at_1633


theorem disposition_interval_1634 : Interval dispositionTest 1634 1635 := by
  intro i hlo hhi
  have h : i = 1634 := by omega
  subst i
  exact disposition_at_1634


theorem disposition_interval_1635 : Interval dispositionTest 1635 1636 := by
  intro i hlo hhi
  have h : i = 1635 := by omega
  subst i
  exact disposition_at_1635


theorem disposition_interval_1636 : Interval dispositionTest 1636 1637 := by
  intro i hlo hhi
  have h : i = 1636 := by omega
  subst i
  exact disposition_at_1636


theorem disposition_interval_1637 : Interval dispositionTest 1637 1638 := by
  intro i hlo hhi
  have h : i = 1637 := by omega
  subst i
  exact disposition_at_1637


theorem disposition_interval_1638 : Interval dispositionTest 1638 1639 := by
  intro i hlo hhi
  have h : i = 1638 := by omega
  subst i
  exact disposition_at_1638


theorem disposition_interval_1639 : Interval dispositionTest 1639 1640 := by
  intro i hlo hhi
  have h : i = 1639 := by omega
  subst i
  exact disposition_at_1639


theorem disposition_interval_1640 : Interval dispositionTest 1640 1641 := by
  intro i hlo hhi
  have h : i = 1640 := by omega
  subst i
  exact disposition_at_1640


theorem disposition_interval_1641 : Interval dispositionTest 1641 1642 := by
  intro i hlo hhi
  have h : i = 1641 := by omega
  subst i
  exact disposition_at_1641


theorem disposition_interval_1642 : Interval dispositionTest 1642 1643 := by
  intro i hlo hhi
  have h : i = 1642 := by omega
  subst i
  exact disposition_at_1642


theorem disposition_interval_1643 : Interval dispositionTest 1643 1644 := by
  intro i hlo hhi
  have h : i = 1643 := by omega
  subst i
  exact disposition_at_1643


theorem disposition_interval_1644 : Interval dispositionTest 1644 1645 := by
  intro i hlo hhi
  have h : i = 1644 := by omega
  subst i
  exact disposition_at_1644


theorem disposition_interval_1645 : Interval dispositionTest 1645 1646 := by
  intro i hlo hhi
  have h : i = 1645 := by omega
  subst i
  exact disposition_at_1645


theorem disposition_interval_1646 : Interval dispositionTest 1646 1647 := by
  intro i hlo hhi
  have h : i = 1646 := by omega
  subst i
  exact disposition_at_1646


theorem disposition_interval_1647 : Interval dispositionTest 1647 1648 := by
  intro i hlo hhi
  have h : i = 1647 := by omega
  subst i
  exact disposition_at_1647


theorem disposition_interval_1648 : Interval dispositionTest 1648 1649 := by
  intro i hlo hhi
  have h : i = 1648 := by omega
  subst i
  exact disposition_at_1648


theorem disposition_interval_1649 : Interval dispositionTest 1649 1650 := by
  intro i hlo hhi
  have h : i = 1649 := by omega
  subst i
  exact disposition_at_1649


theorem disposition_interval_1650 : Interval dispositionTest 1650 1651 := by
  intro i hlo hhi
  have h : i = 1650 := by omega
  subst i
  exact disposition_at_1650


theorem disposition_interval_1651 : Interval dispositionTest 1651 1652 := by
  intro i hlo hhi
  have h : i = 1651 := by omega
  subst i
  exact disposition_at_1651


theorem disposition_interval_1652 : Interval dispositionTest 1652 1653 := by
  intro i hlo hhi
  have h : i = 1652 := by omega
  subst i
  exact disposition_at_1652


theorem disposition_interval_1653 : Interval dispositionTest 1653 1654 := by
  intro i hlo hhi
  have h : i = 1653 := by omega
  subst i
  exact disposition_at_1653


theorem disposition_interval_1654 : Interval dispositionTest 1654 1655 := by
  intro i hlo hhi
  have h : i = 1654 := by omega
  subst i
  exact disposition_at_1654


theorem disposition_interval_1655 : Interval dispositionTest 1655 1656 := by
  intro i hlo hhi
  have h : i = 1655 := by omega
  subst i
  exact disposition_at_1655


theorem disposition_interval_1656 : Interval dispositionTest 1656 1657 := by
  intro i hlo hhi
  have h : i = 1656 := by omega
  subst i
  exact disposition_at_1656


theorem disposition_interval_1657 : Interval dispositionTest 1657 1658 := by
  intro i hlo hhi
  have h : i = 1657 := by omega
  subst i
  exact disposition_at_1657


theorem disposition_interval_1658 : Interval dispositionTest 1658 1659 := by
  intro i hlo hhi
  have h : i = 1658 := by omega
  subst i
  exact disposition_at_1658


theorem disposition_interval_1659 : Interval dispositionTest 1659 1660 := by
  intro i hlo hhi
  have h : i = 1659 := by omega
  subst i
  exact disposition_at_1659


theorem disposition_interval_1660 : Interval dispositionTest 1660 1661 := by
  intro i hlo hhi
  have h : i = 1660 := by omega
  subst i
  exact disposition_at_1660


theorem disposition_interval_1661 : Interval dispositionTest 1661 1662 := by
  intro i hlo hhi
  have h : i = 1661 := by omega
  subst i
  exact disposition_at_1661


theorem disposition_interval_1662 : Interval dispositionTest 1662 1663 := by
  intro i hlo hhi
  have h : i = 1662 := by omega
  subst i
  exact disposition_at_1662


theorem disposition_interval_1663 : Interval dispositionTest 1663 1664 := by
  intro i hlo hhi
  have h : i = 1663 := by omega
  subst i
  exact disposition_at_1663

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
