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
theorem disposition_at_800 : dispositionTest 800 = true := by decide +kernel

theorem disposition_at_801 : dispositionTest 801 = true := by decide +kernel

theorem disposition_at_802 : dispositionTest 802 = true := by decide +kernel

theorem disposition_at_803 : dispositionTest 803 = true := by decide +kernel

theorem disposition_at_804 : dispositionTest 804 = true := by decide +kernel

theorem disposition_at_805 : dispositionTest 805 = true := by decide +kernel

theorem disposition_at_806 : dispositionTest 806 = true := by decide +kernel

theorem disposition_at_807 : dispositionTest 807 = true := by decide +kernel

theorem disposition_at_808 : dispositionTest 808 = true := by decide +kernel

theorem disposition_at_809 : dispositionTest 809 = true := by decide +kernel

theorem disposition_at_810 : dispositionTest 810 = true := by decide +kernel

theorem disposition_at_811 : dispositionTest 811 = true := by decide +kernel

theorem disposition_at_812 : dispositionTest 812 = true := by decide +kernel

theorem disposition_at_813 : dispositionTest 813 = true := by decide +kernel

theorem disposition_at_814 : dispositionTest 814 = true := by decide +kernel

theorem disposition_at_815 : dispositionTest 815 = true := by decide +kernel

theorem disposition_at_816 : dispositionTest 816 = true := by decide +kernel

theorem disposition_at_817 : dispositionTest 817 = true := by decide +kernel

theorem disposition_at_818 : dispositionTest 818 = true := by decide +kernel

theorem disposition_at_819 : dispositionTest 819 = true := by decide +kernel

theorem disposition_at_820 : dispositionTest 820 = true := by decide +kernel

theorem disposition_at_821 : dispositionTest 821 = true := by decide +kernel

theorem disposition_at_822 : dispositionTest 822 = true := by decide +kernel

theorem disposition_at_823 : dispositionTest 823 = true := by decide +kernel

theorem disposition_at_824 : dispositionTest 824 = true := by decide +kernel

theorem disposition_at_825 : dispositionTest 825 = true := by decide +kernel

theorem disposition_at_826 : dispositionTest 826 = true := by decide +kernel

theorem disposition_at_827 : dispositionTest 827 = true := by decide +kernel

theorem disposition_at_828 : dispositionTest 828 = true := by decide +kernel

theorem disposition_at_829 : dispositionTest 829 = true := by decide +kernel

theorem disposition_at_830 : dispositionTest 830 = true := by decide +kernel

theorem disposition_at_831 : dispositionTest 831 = true := by decide +kernel

theorem disposition_interval_800 : Interval dispositionTest 800 801 := by
  intro i hlo hhi
  have h : i = 800 := by omega
  subst i
  exact disposition_at_800


theorem disposition_interval_801 : Interval dispositionTest 801 802 := by
  intro i hlo hhi
  have h : i = 801 := by omega
  subst i
  exact disposition_at_801


theorem disposition_interval_802 : Interval dispositionTest 802 803 := by
  intro i hlo hhi
  have h : i = 802 := by omega
  subst i
  exact disposition_at_802


theorem disposition_interval_803 : Interval dispositionTest 803 804 := by
  intro i hlo hhi
  have h : i = 803 := by omega
  subst i
  exact disposition_at_803


theorem disposition_interval_804 : Interval dispositionTest 804 805 := by
  intro i hlo hhi
  have h : i = 804 := by omega
  subst i
  exact disposition_at_804


theorem disposition_interval_805 : Interval dispositionTest 805 806 := by
  intro i hlo hhi
  have h : i = 805 := by omega
  subst i
  exact disposition_at_805


theorem disposition_interval_806 : Interval dispositionTest 806 807 := by
  intro i hlo hhi
  have h : i = 806 := by omega
  subst i
  exact disposition_at_806


theorem disposition_interval_807 : Interval dispositionTest 807 808 := by
  intro i hlo hhi
  have h : i = 807 := by omega
  subst i
  exact disposition_at_807


theorem disposition_interval_808 : Interval dispositionTest 808 809 := by
  intro i hlo hhi
  have h : i = 808 := by omega
  subst i
  exact disposition_at_808


theorem disposition_interval_809 : Interval dispositionTest 809 810 := by
  intro i hlo hhi
  have h : i = 809 := by omega
  subst i
  exact disposition_at_809


theorem disposition_interval_810 : Interval dispositionTest 810 811 := by
  intro i hlo hhi
  have h : i = 810 := by omega
  subst i
  exact disposition_at_810


theorem disposition_interval_811 : Interval dispositionTest 811 812 := by
  intro i hlo hhi
  have h : i = 811 := by omega
  subst i
  exact disposition_at_811


theorem disposition_interval_812 : Interval dispositionTest 812 813 := by
  intro i hlo hhi
  have h : i = 812 := by omega
  subst i
  exact disposition_at_812


theorem disposition_interval_813 : Interval dispositionTest 813 814 := by
  intro i hlo hhi
  have h : i = 813 := by omega
  subst i
  exact disposition_at_813


theorem disposition_interval_814 : Interval dispositionTest 814 815 := by
  intro i hlo hhi
  have h : i = 814 := by omega
  subst i
  exact disposition_at_814


theorem disposition_interval_815 : Interval dispositionTest 815 816 := by
  intro i hlo hhi
  have h : i = 815 := by omega
  subst i
  exact disposition_at_815


theorem disposition_interval_816 : Interval dispositionTest 816 817 := by
  intro i hlo hhi
  have h : i = 816 := by omega
  subst i
  exact disposition_at_816


theorem disposition_interval_817 : Interval dispositionTest 817 818 := by
  intro i hlo hhi
  have h : i = 817 := by omega
  subst i
  exact disposition_at_817


theorem disposition_interval_818 : Interval dispositionTest 818 819 := by
  intro i hlo hhi
  have h : i = 818 := by omega
  subst i
  exact disposition_at_818


theorem disposition_interval_819 : Interval dispositionTest 819 820 := by
  intro i hlo hhi
  have h : i = 819 := by omega
  subst i
  exact disposition_at_819


theorem disposition_interval_820 : Interval dispositionTest 820 821 := by
  intro i hlo hhi
  have h : i = 820 := by omega
  subst i
  exact disposition_at_820


theorem disposition_interval_821 : Interval dispositionTest 821 822 := by
  intro i hlo hhi
  have h : i = 821 := by omega
  subst i
  exact disposition_at_821


theorem disposition_interval_822 : Interval dispositionTest 822 823 := by
  intro i hlo hhi
  have h : i = 822 := by omega
  subst i
  exact disposition_at_822


theorem disposition_interval_823 : Interval dispositionTest 823 824 := by
  intro i hlo hhi
  have h : i = 823 := by omega
  subst i
  exact disposition_at_823


theorem disposition_interval_824 : Interval dispositionTest 824 825 := by
  intro i hlo hhi
  have h : i = 824 := by omega
  subst i
  exact disposition_at_824


theorem disposition_interval_825 : Interval dispositionTest 825 826 := by
  intro i hlo hhi
  have h : i = 825 := by omega
  subst i
  exact disposition_at_825


theorem disposition_interval_826 : Interval dispositionTest 826 827 := by
  intro i hlo hhi
  have h : i = 826 := by omega
  subst i
  exact disposition_at_826


theorem disposition_interval_827 : Interval dispositionTest 827 828 := by
  intro i hlo hhi
  have h : i = 827 := by omega
  subst i
  exact disposition_at_827


theorem disposition_interval_828 : Interval dispositionTest 828 829 := by
  intro i hlo hhi
  have h : i = 828 := by omega
  subst i
  exact disposition_at_828


theorem disposition_interval_829 : Interval dispositionTest 829 830 := by
  intro i hlo hhi
  have h : i = 829 := by omega
  subst i
  exact disposition_at_829


theorem disposition_interval_830 : Interval dispositionTest 830 831 := by
  intro i hlo hhi
  have h : i = 830 := by omega
  subst i
  exact disposition_at_830


theorem disposition_interval_831 : Interval dispositionTest 831 832 := by
  intro i hlo hhi
  have h : i = 831 := by omega
  subst i
  exact disposition_at_831

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
