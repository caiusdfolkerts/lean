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
theorem disposition_at_1760 : dispositionTest 1760 = true := by decide +kernel

theorem disposition_at_1761 : dispositionTest 1761 = true := by decide +kernel

theorem disposition_at_1762 : dispositionTest 1762 = true := by decide +kernel

theorem disposition_at_1763 : dispositionTest 1763 = true := by decide +kernel

theorem disposition_at_1764 : dispositionTest 1764 = true := by decide +kernel

theorem disposition_at_1765 : dispositionTest 1765 = true := by decide +kernel

theorem disposition_at_1766 : dispositionTest 1766 = true := by decide +kernel

theorem disposition_at_1767 : dispositionTest 1767 = true := by decide +kernel

theorem disposition_at_1768 : dispositionTest 1768 = true := by decide +kernel

theorem disposition_at_1769 : dispositionTest 1769 = true := by decide +kernel


theorem disposition_at_1770 : dispositionTest 1770 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1770).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1527.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1527) = true
  rw [Nonrational.OldTerminalMatches.M023.r1527_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_1771 : dispositionTest 1771 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1771).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1528.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1528) = true
  rw [Nonrational.OldTerminalMatches.M023.r1528_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1772 : dispositionTest 1772 = true := by decide +kernel

theorem disposition_at_1773 : dispositionTest 1773 = true := by decide +kernel

theorem disposition_at_1774 : dispositionTest 1774 = true := by decide +kernel

theorem disposition_at_1775 : dispositionTest 1775 = true := by decide +kernel

theorem disposition_at_1776 : dispositionTest 1776 = true := by decide +kernel

theorem disposition_at_1777 : dispositionTest 1777 = true := by decide +kernel

theorem disposition_at_1778 : dispositionTest 1778 = true := by decide +kernel

theorem disposition_at_1779 : dispositionTest 1779 = true := by decide +kernel

theorem disposition_at_1780 : dispositionTest 1780 = true := by decide +kernel

theorem disposition_at_1781 : dispositionTest 1781 = true := by decide +kernel

theorem disposition_at_1782 : dispositionTest 1782 = true := by decide +kernel

theorem disposition_at_1783 : dispositionTest 1783 = true := by decide +kernel

theorem disposition_at_1784 : dispositionTest 1784 = true := by decide +kernel

theorem disposition_at_1785 : dispositionTest 1785 = true := by decide +kernel

theorem disposition_at_1786 : dispositionTest 1786 = true := by decide +kernel

theorem disposition_at_1787 : dispositionTest 1787 = true := by decide +kernel

theorem disposition_at_1788 : dispositionTest 1788 = true := by decide +kernel

theorem disposition_at_1789 : dispositionTest 1789 = true := by decide +kernel

theorem disposition_at_1790 : dispositionTest 1790 = true := by decide +kernel

theorem disposition_at_1791 : dispositionTest 1791 = true := by decide +kernel

theorem disposition_interval_1760 : Interval dispositionTest 1760 1761 := by
  intro i hlo hhi
  have h : i = 1760 := by omega
  subst i
  exact disposition_at_1760


theorem disposition_interval_1761 : Interval dispositionTest 1761 1762 := by
  intro i hlo hhi
  have h : i = 1761 := by omega
  subst i
  exact disposition_at_1761


theorem disposition_interval_1762 : Interval dispositionTest 1762 1763 := by
  intro i hlo hhi
  have h : i = 1762 := by omega
  subst i
  exact disposition_at_1762


theorem disposition_interval_1763 : Interval dispositionTest 1763 1764 := by
  intro i hlo hhi
  have h : i = 1763 := by omega
  subst i
  exact disposition_at_1763


theorem disposition_interval_1764 : Interval dispositionTest 1764 1765 := by
  intro i hlo hhi
  have h : i = 1764 := by omega
  subst i
  exact disposition_at_1764


theorem disposition_interval_1765 : Interval dispositionTest 1765 1766 := by
  intro i hlo hhi
  have h : i = 1765 := by omega
  subst i
  exact disposition_at_1765


theorem disposition_interval_1766 : Interval dispositionTest 1766 1767 := by
  intro i hlo hhi
  have h : i = 1766 := by omega
  subst i
  exact disposition_at_1766


theorem disposition_interval_1767 : Interval dispositionTest 1767 1768 := by
  intro i hlo hhi
  have h : i = 1767 := by omega
  subst i
  exact disposition_at_1767


theorem disposition_interval_1768 : Interval dispositionTest 1768 1769 := by
  intro i hlo hhi
  have h : i = 1768 := by omega
  subst i
  exact disposition_at_1768


theorem disposition_interval_1769 : Interval dispositionTest 1769 1770 := by
  intro i hlo hhi
  have h : i = 1769 := by omega
  subst i
  exact disposition_at_1769


theorem disposition_interval_1770 : Interval dispositionTest 1770 1771 := by
  intro i hlo hhi
  have h : i = 1770 := by omega
  subst i
  exact disposition_at_1770


theorem disposition_interval_1771 : Interval dispositionTest 1771 1772 := by
  intro i hlo hhi
  have h : i = 1771 := by omega
  subst i
  exact disposition_at_1771


theorem disposition_interval_1772 : Interval dispositionTest 1772 1773 := by
  intro i hlo hhi
  have h : i = 1772 := by omega
  subst i
  exact disposition_at_1772


theorem disposition_interval_1773 : Interval dispositionTest 1773 1774 := by
  intro i hlo hhi
  have h : i = 1773 := by omega
  subst i
  exact disposition_at_1773


theorem disposition_interval_1774 : Interval dispositionTest 1774 1775 := by
  intro i hlo hhi
  have h : i = 1774 := by omega
  subst i
  exact disposition_at_1774


theorem disposition_interval_1775 : Interval dispositionTest 1775 1776 := by
  intro i hlo hhi
  have h : i = 1775 := by omega
  subst i
  exact disposition_at_1775


theorem disposition_interval_1776 : Interval dispositionTest 1776 1777 := by
  intro i hlo hhi
  have h : i = 1776 := by omega
  subst i
  exact disposition_at_1776


theorem disposition_interval_1777 : Interval dispositionTest 1777 1778 := by
  intro i hlo hhi
  have h : i = 1777 := by omega
  subst i
  exact disposition_at_1777


theorem disposition_interval_1778 : Interval dispositionTest 1778 1779 := by
  intro i hlo hhi
  have h : i = 1778 := by omega
  subst i
  exact disposition_at_1778


theorem disposition_interval_1779 : Interval dispositionTest 1779 1780 := by
  intro i hlo hhi
  have h : i = 1779 := by omega
  subst i
  exact disposition_at_1779


theorem disposition_interval_1780 : Interval dispositionTest 1780 1781 := by
  intro i hlo hhi
  have h : i = 1780 := by omega
  subst i
  exact disposition_at_1780


theorem disposition_interval_1781 : Interval dispositionTest 1781 1782 := by
  intro i hlo hhi
  have h : i = 1781 := by omega
  subst i
  exact disposition_at_1781


theorem disposition_interval_1782 : Interval dispositionTest 1782 1783 := by
  intro i hlo hhi
  have h : i = 1782 := by omega
  subst i
  exact disposition_at_1782


theorem disposition_interval_1783 : Interval dispositionTest 1783 1784 := by
  intro i hlo hhi
  have h : i = 1783 := by omega
  subst i
  exact disposition_at_1783


theorem disposition_interval_1784 : Interval dispositionTest 1784 1785 := by
  intro i hlo hhi
  have h : i = 1784 := by omega
  subst i
  exact disposition_at_1784


theorem disposition_interval_1785 : Interval dispositionTest 1785 1786 := by
  intro i hlo hhi
  have h : i = 1785 := by omega
  subst i
  exact disposition_at_1785


theorem disposition_interval_1786 : Interval dispositionTest 1786 1787 := by
  intro i hlo hhi
  have h : i = 1786 := by omega
  subst i
  exact disposition_at_1786


theorem disposition_interval_1787 : Interval dispositionTest 1787 1788 := by
  intro i hlo hhi
  have h : i = 1787 := by omega
  subst i
  exact disposition_at_1787


theorem disposition_interval_1788 : Interval dispositionTest 1788 1789 := by
  intro i hlo hhi
  have h : i = 1788 := by omega
  subst i
  exact disposition_at_1788


theorem disposition_interval_1789 : Interval dispositionTest 1789 1790 := by
  intro i hlo hhi
  have h : i = 1789 := by omega
  subst i
  exact disposition_at_1789


theorem disposition_interval_1790 : Interval dispositionTest 1790 1791 := by
  intro i hlo hhi
  have h : i = 1790 := by omega
  subst i
  exact disposition_at_1790


theorem disposition_interval_1791 : Interval dispositionTest 1791 1792 := by
  intro i hlo hhi
  have h : i = 1791 := by omega
  subst i
  exact disposition_at_1791

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
