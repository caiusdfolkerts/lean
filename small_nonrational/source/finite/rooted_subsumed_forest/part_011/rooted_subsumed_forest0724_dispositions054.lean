module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_1728 : dispositionTest 1728 = true := by decide +kernel

theorem disposition_at_1729 : dispositionTest 1729 = true := by decide +kernel

theorem disposition_at_1730 : dispositionTest 1730 = true := by decide +kernel

theorem disposition_at_1731 : dispositionTest 1731 = true := by decide +kernel

theorem disposition_at_1732 : dispositionTest 1732 = true := by decide +kernel

theorem disposition_at_1733 : dispositionTest 1733 = true := by decide +kernel

theorem disposition_at_1734 : dispositionTest 1734 = true := by decide +kernel

theorem disposition_at_1735 : dispositionTest 1735 = true := by decide +kernel

theorem disposition_at_1736 : dispositionTest 1736 = true := by decide +kernel

theorem disposition_at_1737 : dispositionTest 1737 = true := by decide +kernel

theorem disposition_at_1738 : dispositionTest 1738 = true := by decide +kernel

theorem disposition_at_1739 : dispositionTest 1739 = true := by decide +kernel

theorem disposition_at_1740 : dispositionTest 1740 = true := by decide +kernel

theorem disposition_at_1741 : dispositionTest 1741 = true := by decide +kernel

theorem disposition_at_1742 : dispositionTest 1742 = true := by decide +kernel

theorem disposition_at_1743 : dispositionTest 1743 = true := by decide +kernel

theorem disposition_at_1744 : dispositionTest 1744 = true := by decide +kernel

theorem disposition_at_1745 : dispositionTest 1745 = true := by decide +kernel

theorem disposition_at_1746 : dispositionTest 1746 = true := by decide +kernel

theorem disposition_at_1747 : dispositionTest 1747 = true := by decide +kernel

theorem disposition_at_1748 : dispositionTest 1748 = true := by decide +kernel


theorem disposition_at_1749 : dispositionTest 1749 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1749).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1525.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1525) = true
  rw [Nonrational.OldTerminalMatches.M023.r1525_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1750 : dispositionTest 1750 = true := by decide +kernel


theorem disposition_at_1751 : dispositionTest 1751 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1751).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1526.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1526) = true
  rw [Nonrational.OldTerminalMatches.M023.r1526_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1752 : dispositionTest 1752 = true := by decide +kernel

theorem disposition_at_1753 : dispositionTest 1753 = true := by decide +kernel

theorem disposition_at_1754 : dispositionTest 1754 = true := by decide +kernel

theorem disposition_at_1755 : dispositionTest 1755 = true := by decide +kernel

theorem disposition_at_1756 : dispositionTest 1756 = true := by decide +kernel

theorem disposition_at_1757 : dispositionTest 1757 = true := by decide +kernel

theorem disposition_at_1758 : dispositionTest 1758 = true := by decide +kernel

theorem disposition_at_1759 : dispositionTest 1759 = true := by decide +kernel

theorem disposition_interval_1728 : Interval dispositionTest 1728 1729 := by
  intro i hlo hhi
  have h : i = 1728 := by omega
  subst i
  exact disposition_at_1728


theorem disposition_interval_1729 : Interval dispositionTest 1729 1730 := by
  intro i hlo hhi
  have h : i = 1729 := by omega
  subst i
  exact disposition_at_1729


theorem disposition_interval_1730 : Interval dispositionTest 1730 1731 := by
  intro i hlo hhi
  have h : i = 1730 := by omega
  subst i
  exact disposition_at_1730


theorem disposition_interval_1731 : Interval dispositionTest 1731 1732 := by
  intro i hlo hhi
  have h : i = 1731 := by omega
  subst i
  exact disposition_at_1731


theorem disposition_interval_1732 : Interval dispositionTest 1732 1733 := by
  intro i hlo hhi
  have h : i = 1732 := by omega
  subst i
  exact disposition_at_1732


theorem disposition_interval_1733 : Interval dispositionTest 1733 1734 := by
  intro i hlo hhi
  have h : i = 1733 := by omega
  subst i
  exact disposition_at_1733


theorem disposition_interval_1734 : Interval dispositionTest 1734 1735 := by
  intro i hlo hhi
  have h : i = 1734 := by omega
  subst i
  exact disposition_at_1734


theorem disposition_interval_1735 : Interval dispositionTest 1735 1736 := by
  intro i hlo hhi
  have h : i = 1735 := by omega
  subst i
  exact disposition_at_1735


theorem disposition_interval_1736 : Interval dispositionTest 1736 1737 := by
  intro i hlo hhi
  have h : i = 1736 := by omega
  subst i
  exact disposition_at_1736


theorem disposition_interval_1737 : Interval dispositionTest 1737 1738 := by
  intro i hlo hhi
  have h : i = 1737 := by omega
  subst i
  exact disposition_at_1737


theorem disposition_interval_1738 : Interval dispositionTest 1738 1739 := by
  intro i hlo hhi
  have h : i = 1738 := by omega
  subst i
  exact disposition_at_1738


theorem disposition_interval_1739 : Interval dispositionTest 1739 1740 := by
  intro i hlo hhi
  have h : i = 1739 := by omega
  subst i
  exact disposition_at_1739


theorem disposition_interval_1740 : Interval dispositionTest 1740 1741 := by
  intro i hlo hhi
  have h : i = 1740 := by omega
  subst i
  exact disposition_at_1740


theorem disposition_interval_1741 : Interval dispositionTest 1741 1742 := by
  intro i hlo hhi
  have h : i = 1741 := by omega
  subst i
  exact disposition_at_1741


theorem disposition_interval_1742 : Interval dispositionTest 1742 1743 := by
  intro i hlo hhi
  have h : i = 1742 := by omega
  subst i
  exact disposition_at_1742


theorem disposition_interval_1743 : Interval dispositionTest 1743 1744 := by
  intro i hlo hhi
  have h : i = 1743 := by omega
  subst i
  exact disposition_at_1743


theorem disposition_interval_1744 : Interval dispositionTest 1744 1745 := by
  intro i hlo hhi
  have h : i = 1744 := by omega
  subst i
  exact disposition_at_1744


theorem disposition_interval_1745 : Interval dispositionTest 1745 1746 := by
  intro i hlo hhi
  have h : i = 1745 := by omega
  subst i
  exact disposition_at_1745


theorem disposition_interval_1746 : Interval dispositionTest 1746 1747 := by
  intro i hlo hhi
  have h : i = 1746 := by omega
  subst i
  exact disposition_at_1746


theorem disposition_interval_1747 : Interval dispositionTest 1747 1748 := by
  intro i hlo hhi
  have h : i = 1747 := by omega
  subst i
  exact disposition_at_1747


theorem disposition_interval_1748 : Interval dispositionTest 1748 1749 := by
  intro i hlo hhi
  have h : i = 1748 := by omega
  subst i
  exact disposition_at_1748


theorem disposition_interval_1749 : Interval dispositionTest 1749 1750 := by
  intro i hlo hhi
  have h : i = 1749 := by omega
  subst i
  exact disposition_at_1749


theorem disposition_interval_1750 : Interval dispositionTest 1750 1751 := by
  intro i hlo hhi
  have h : i = 1750 := by omega
  subst i
  exact disposition_at_1750


theorem disposition_interval_1751 : Interval dispositionTest 1751 1752 := by
  intro i hlo hhi
  have h : i = 1751 := by omega
  subst i
  exact disposition_at_1751


theorem disposition_interval_1752 : Interval dispositionTest 1752 1753 := by
  intro i hlo hhi
  have h : i = 1752 := by omega
  subst i
  exact disposition_at_1752


theorem disposition_interval_1753 : Interval dispositionTest 1753 1754 := by
  intro i hlo hhi
  have h : i = 1753 := by omega
  subst i
  exact disposition_at_1753


theorem disposition_interval_1754 : Interval dispositionTest 1754 1755 := by
  intro i hlo hhi
  have h : i = 1754 := by omega
  subst i
  exact disposition_at_1754


theorem disposition_interval_1755 : Interval dispositionTest 1755 1756 := by
  intro i hlo hhi
  have h : i = 1755 := by omega
  subst i
  exact disposition_at_1755


theorem disposition_interval_1756 : Interval dispositionTest 1756 1757 := by
  intro i hlo hhi
  have h : i = 1756 := by omega
  subst i
  exact disposition_at_1756


theorem disposition_interval_1757 : Interval dispositionTest 1757 1758 := by
  intro i hlo hhi
  have h : i = 1757 := by omega
  subst i
  exact disposition_at_1757


theorem disposition_interval_1758 : Interval dispositionTest 1758 1759 := by
  intro i hlo hhi
  have h : i = 1758 := by omega
  subst i
  exact disposition_at_1758


theorem disposition_interval_1759 : Interval dispositionTest 1759 1760 := by
  intro i hlo hhi
  have h : i = 1759 := by omega
  subst i
  exact disposition_at_1759

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
