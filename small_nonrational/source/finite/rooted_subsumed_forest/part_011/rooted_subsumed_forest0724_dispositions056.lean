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
theorem disposition_at_1792 : dispositionTest 1792 = true := by decide +kernel

theorem disposition_at_1793 : dispositionTest 1793 = true := by decide +kernel

theorem disposition_at_1794 : dispositionTest 1794 = true := by decide +kernel

theorem disposition_at_1795 : dispositionTest 1795 = true := by decide +kernel

theorem disposition_at_1796 : dispositionTest 1796 = true := by decide +kernel

theorem disposition_at_1797 : dispositionTest 1797 = true := by decide +kernel

theorem disposition_at_1798 : dispositionTest 1798 = true := by decide +kernel

theorem disposition_at_1799 : dispositionTest 1799 = true := by decide +kernel

theorem disposition_at_1800 : dispositionTest 1800 = true := by decide +kernel

theorem disposition_at_1801 : dispositionTest 1801 = true := by decide +kernel

theorem disposition_at_1802 : dispositionTest 1802 = true := by decide +kernel

theorem disposition_at_1803 : dispositionTest 1803 = true := by decide +kernel

theorem disposition_at_1804 : dispositionTest 1804 = true := by decide +kernel

theorem disposition_at_1805 : dispositionTest 1805 = true := by decide +kernel

theorem disposition_at_1806 : dispositionTest 1806 = true := by decide +kernel

theorem disposition_at_1807 : dispositionTest 1807 = true := by decide +kernel

theorem disposition_at_1808 : dispositionTest 1808 = true := by decide +kernel

theorem disposition_at_1809 : dispositionTest 1809 = true := by decide +kernel

theorem disposition_at_1810 : dispositionTest 1810 = true := by decide +kernel

theorem disposition_at_1811 : dispositionTest 1811 = true := by decide +kernel

theorem disposition_at_1812 : dispositionTest 1812 = true := by decide +kernel

theorem disposition_at_1813 : dispositionTest 1813 = true := by decide +kernel

theorem disposition_at_1814 : dispositionTest 1814 = true := by decide +kernel

theorem disposition_at_1815 : dispositionTest 1815 = true := by decide +kernel

theorem disposition_at_1816 : dispositionTest 1816 = true := by decide +kernel

theorem disposition_at_1817 : dispositionTest 1817 = true := by decide +kernel

theorem disposition_at_1818 : dispositionTest 1818 = true := by decide +kernel

theorem disposition_at_1819 : dispositionTest 1819 = true := by decide +kernel

theorem disposition_at_1820 : dispositionTest 1820 = true := by decide +kernel

theorem disposition_at_1821 : dispositionTest 1821 = true := by decide +kernel

theorem disposition_at_1822 : dispositionTest 1822 = true := by decide +kernel

theorem disposition_at_1823 : dispositionTest 1823 = true := by decide +kernel

theorem disposition_interval_1792 : Interval dispositionTest 1792 1793 := by
  intro i hlo hhi
  have h : i = 1792 := by omega
  subst i
  exact disposition_at_1792


theorem disposition_interval_1793 : Interval dispositionTest 1793 1794 := by
  intro i hlo hhi
  have h : i = 1793 := by omega
  subst i
  exact disposition_at_1793


theorem disposition_interval_1794 : Interval dispositionTest 1794 1795 := by
  intro i hlo hhi
  have h : i = 1794 := by omega
  subst i
  exact disposition_at_1794


theorem disposition_interval_1795 : Interval dispositionTest 1795 1796 := by
  intro i hlo hhi
  have h : i = 1795 := by omega
  subst i
  exact disposition_at_1795


theorem disposition_interval_1796 : Interval dispositionTest 1796 1797 := by
  intro i hlo hhi
  have h : i = 1796 := by omega
  subst i
  exact disposition_at_1796


theorem disposition_interval_1797 : Interval dispositionTest 1797 1798 := by
  intro i hlo hhi
  have h : i = 1797 := by omega
  subst i
  exact disposition_at_1797


theorem disposition_interval_1798 : Interval dispositionTest 1798 1799 := by
  intro i hlo hhi
  have h : i = 1798 := by omega
  subst i
  exact disposition_at_1798


theorem disposition_interval_1799 : Interval dispositionTest 1799 1800 := by
  intro i hlo hhi
  have h : i = 1799 := by omega
  subst i
  exact disposition_at_1799


theorem disposition_interval_1800 : Interval dispositionTest 1800 1801 := by
  intro i hlo hhi
  have h : i = 1800 := by omega
  subst i
  exact disposition_at_1800


theorem disposition_interval_1801 : Interval dispositionTest 1801 1802 := by
  intro i hlo hhi
  have h : i = 1801 := by omega
  subst i
  exact disposition_at_1801


theorem disposition_interval_1802 : Interval dispositionTest 1802 1803 := by
  intro i hlo hhi
  have h : i = 1802 := by omega
  subst i
  exact disposition_at_1802


theorem disposition_interval_1803 : Interval dispositionTest 1803 1804 := by
  intro i hlo hhi
  have h : i = 1803 := by omega
  subst i
  exact disposition_at_1803


theorem disposition_interval_1804 : Interval dispositionTest 1804 1805 := by
  intro i hlo hhi
  have h : i = 1804 := by omega
  subst i
  exact disposition_at_1804


theorem disposition_interval_1805 : Interval dispositionTest 1805 1806 := by
  intro i hlo hhi
  have h : i = 1805 := by omega
  subst i
  exact disposition_at_1805


theorem disposition_interval_1806 : Interval dispositionTest 1806 1807 := by
  intro i hlo hhi
  have h : i = 1806 := by omega
  subst i
  exact disposition_at_1806


theorem disposition_interval_1807 : Interval dispositionTest 1807 1808 := by
  intro i hlo hhi
  have h : i = 1807 := by omega
  subst i
  exact disposition_at_1807


theorem disposition_interval_1808 : Interval dispositionTest 1808 1809 := by
  intro i hlo hhi
  have h : i = 1808 := by omega
  subst i
  exact disposition_at_1808


theorem disposition_interval_1809 : Interval dispositionTest 1809 1810 := by
  intro i hlo hhi
  have h : i = 1809 := by omega
  subst i
  exact disposition_at_1809


theorem disposition_interval_1810 : Interval dispositionTest 1810 1811 := by
  intro i hlo hhi
  have h : i = 1810 := by omega
  subst i
  exact disposition_at_1810


theorem disposition_interval_1811 : Interval dispositionTest 1811 1812 := by
  intro i hlo hhi
  have h : i = 1811 := by omega
  subst i
  exact disposition_at_1811


theorem disposition_interval_1812 : Interval dispositionTest 1812 1813 := by
  intro i hlo hhi
  have h : i = 1812 := by omega
  subst i
  exact disposition_at_1812


theorem disposition_interval_1813 : Interval dispositionTest 1813 1814 := by
  intro i hlo hhi
  have h : i = 1813 := by omega
  subst i
  exact disposition_at_1813


theorem disposition_interval_1814 : Interval dispositionTest 1814 1815 := by
  intro i hlo hhi
  have h : i = 1814 := by omega
  subst i
  exact disposition_at_1814


theorem disposition_interval_1815 : Interval dispositionTest 1815 1816 := by
  intro i hlo hhi
  have h : i = 1815 := by omega
  subst i
  exact disposition_at_1815


theorem disposition_interval_1816 : Interval dispositionTest 1816 1817 := by
  intro i hlo hhi
  have h : i = 1816 := by omega
  subst i
  exact disposition_at_1816


theorem disposition_interval_1817 : Interval dispositionTest 1817 1818 := by
  intro i hlo hhi
  have h : i = 1817 := by omega
  subst i
  exact disposition_at_1817


theorem disposition_interval_1818 : Interval dispositionTest 1818 1819 := by
  intro i hlo hhi
  have h : i = 1818 := by omega
  subst i
  exact disposition_at_1818


theorem disposition_interval_1819 : Interval dispositionTest 1819 1820 := by
  intro i hlo hhi
  have h : i = 1819 := by omega
  subst i
  exact disposition_at_1819


theorem disposition_interval_1820 : Interval dispositionTest 1820 1821 := by
  intro i hlo hhi
  have h : i = 1820 := by omega
  subst i
  exact disposition_at_1820


theorem disposition_interval_1821 : Interval dispositionTest 1821 1822 := by
  intro i hlo hhi
  have h : i = 1821 := by omega
  subst i
  exact disposition_at_1821


theorem disposition_interval_1822 : Interval dispositionTest 1822 1823 := by
  intro i hlo hhi
  have h : i = 1822 := by omega
  subst i
  exact disposition_at_1822


theorem disposition_interval_1823 : Interval dispositionTest 1823 1824 := by
  intro i hlo hhi
  have h : i = 1823 := by omega
  subst i
  exact disposition_at_1823

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
