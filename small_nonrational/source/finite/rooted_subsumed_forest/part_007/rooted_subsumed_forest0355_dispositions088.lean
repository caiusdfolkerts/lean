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
theorem disposition_at_2816 : dispositionTest 2816 = true := by decide +kernel

theorem disposition_at_2817 : dispositionTest 2817 = true := by decide +kernel

theorem disposition_at_2818 : dispositionTest 2818 = true := by decide +kernel

theorem disposition_at_2819 : dispositionTest 2819 = true := by decide +kernel

theorem disposition_at_2820 : dispositionTest 2820 = true := by decide +kernel

theorem disposition_at_2821 : dispositionTest 2821 = true := by decide +kernel

theorem disposition_at_2822 : dispositionTest 2822 = true := by decide +kernel

theorem disposition_at_2823 : dispositionTest 2823 = true := by decide +kernel

theorem disposition_at_2824 : dispositionTest 2824 = true := by decide +kernel

theorem disposition_at_2825 : dispositionTest 2825 = true := by decide +kernel

theorem disposition_at_2826 : dispositionTest 2826 = true := by decide +kernel

theorem disposition_at_2827 : dispositionTest 2827 = true := by decide +kernel

theorem disposition_at_2828 : dispositionTest 2828 = true := by decide +kernel

theorem disposition_at_2829 : dispositionTest 2829 = true := by decide +kernel

theorem disposition_at_2830 : dispositionTest 2830 = true := by decide +kernel

theorem disposition_at_2831 : dispositionTest 2831 = true := by decide +kernel

theorem disposition_at_2832 : dispositionTest 2832 = true := by decide +kernel

theorem disposition_at_2833 : dispositionTest 2833 = true := by decide +kernel

theorem disposition_at_2834 : dispositionTest 2834 = true := by decide +kernel

theorem disposition_at_2835 : dispositionTest 2835 = true := by decide +kernel

theorem disposition_at_2836 : dispositionTest 2836 = true := by decide +kernel

theorem disposition_at_2837 : dispositionTest 2837 = true := by decide +kernel

theorem disposition_at_2838 : dispositionTest 2838 = true := by decide +kernel

theorem disposition_at_2839 : dispositionTest 2839 = true := by decide +kernel

theorem disposition_at_2840 : dispositionTest 2840 = true := by decide +kernel


theorem disposition_at_2841 : dispositionTest 2841 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2841).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1047.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1047) = true
  rw [Nonrational.OldTerminalMatches.M016.r1047_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_2842 : dispositionTest 2842 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2842).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1048.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1048) = true
  rw [Nonrational.OldTerminalMatches.M016.r1048_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2843 : dispositionTest 2843 = true := by decide +kernel

theorem disposition_at_2844 : dispositionTest 2844 = true := by decide +kernel

theorem disposition_at_2845 : dispositionTest 2845 = true := by decide +kernel

theorem disposition_at_2846 : dispositionTest 2846 = true := by decide +kernel

theorem disposition_at_2847 : dispositionTest 2847 = true := by decide +kernel

theorem disposition_interval_2816 : Interval dispositionTest 2816 2817 := by
  intro i hlo hhi
  have h : i = 2816 := by omega
  subst i
  exact disposition_at_2816


theorem disposition_interval_2817 : Interval dispositionTest 2817 2818 := by
  intro i hlo hhi
  have h : i = 2817 := by omega
  subst i
  exact disposition_at_2817


theorem disposition_interval_2818 : Interval dispositionTest 2818 2819 := by
  intro i hlo hhi
  have h : i = 2818 := by omega
  subst i
  exact disposition_at_2818


theorem disposition_interval_2819 : Interval dispositionTest 2819 2820 := by
  intro i hlo hhi
  have h : i = 2819 := by omega
  subst i
  exact disposition_at_2819


theorem disposition_interval_2820 : Interval dispositionTest 2820 2821 := by
  intro i hlo hhi
  have h : i = 2820 := by omega
  subst i
  exact disposition_at_2820


theorem disposition_interval_2821 : Interval dispositionTest 2821 2822 := by
  intro i hlo hhi
  have h : i = 2821 := by omega
  subst i
  exact disposition_at_2821


theorem disposition_interval_2822 : Interval dispositionTest 2822 2823 := by
  intro i hlo hhi
  have h : i = 2822 := by omega
  subst i
  exact disposition_at_2822


theorem disposition_interval_2823 : Interval dispositionTest 2823 2824 := by
  intro i hlo hhi
  have h : i = 2823 := by omega
  subst i
  exact disposition_at_2823


theorem disposition_interval_2824 : Interval dispositionTest 2824 2825 := by
  intro i hlo hhi
  have h : i = 2824 := by omega
  subst i
  exact disposition_at_2824


theorem disposition_interval_2825 : Interval dispositionTest 2825 2826 := by
  intro i hlo hhi
  have h : i = 2825 := by omega
  subst i
  exact disposition_at_2825


theorem disposition_interval_2826 : Interval dispositionTest 2826 2827 := by
  intro i hlo hhi
  have h : i = 2826 := by omega
  subst i
  exact disposition_at_2826


theorem disposition_interval_2827 : Interval dispositionTest 2827 2828 := by
  intro i hlo hhi
  have h : i = 2827 := by omega
  subst i
  exact disposition_at_2827


theorem disposition_interval_2828 : Interval dispositionTest 2828 2829 := by
  intro i hlo hhi
  have h : i = 2828 := by omega
  subst i
  exact disposition_at_2828


theorem disposition_interval_2829 : Interval dispositionTest 2829 2830 := by
  intro i hlo hhi
  have h : i = 2829 := by omega
  subst i
  exact disposition_at_2829


theorem disposition_interval_2830 : Interval dispositionTest 2830 2831 := by
  intro i hlo hhi
  have h : i = 2830 := by omega
  subst i
  exact disposition_at_2830


theorem disposition_interval_2831 : Interval dispositionTest 2831 2832 := by
  intro i hlo hhi
  have h : i = 2831 := by omega
  subst i
  exact disposition_at_2831


theorem disposition_interval_2832 : Interval dispositionTest 2832 2833 := by
  intro i hlo hhi
  have h : i = 2832 := by omega
  subst i
  exact disposition_at_2832


theorem disposition_interval_2833 : Interval dispositionTest 2833 2834 := by
  intro i hlo hhi
  have h : i = 2833 := by omega
  subst i
  exact disposition_at_2833


theorem disposition_interval_2834 : Interval dispositionTest 2834 2835 := by
  intro i hlo hhi
  have h : i = 2834 := by omega
  subst i
  exact disposition_at_2834


theorem disposition_interval_2835 : Interval dispositionTest 2835 2836 := by
  intro i hlo hhi
  have h : i = 2835 := by omega
  subst i
  exact disposition_at_2835


theorem disposition_interval_2836 : Interval dispositionTest 2836 2837 := by
  intro i hlo hhi
  have h : i = 2836 := by omega
  subst i
  exact disposition_at_2836


theorem disposition_interval_2837 : Interval dispositionTest 2837 2838 := by
  intro i hlo hhi
  have h : i = 2837 := by omega
  subst i
  exact disposition_at_2837


theorem disposition_interval_2838 : Interval dispositionTest 2838 2839 := by
  intro i hlo hhi
  have h : i = 2838 := by omega
  subst i
  exact disposition_at_2838


theorem disposition_interval_2839 : Interval dispositionTest 2839 2840 := by
  intro i hlo hhi
  have h : i = 2839 := by omega
  subst i
  exact disposition_at_2839


theorem disposition_interval_2840 : Interval dispositionTest 2840 2841 := by
  intro i hlo hhi
  have h : i = 2840 := by omega
  subst i
  exact disposition_at_2840


theorem disposition_interval_2841 : Interval dispositionTest 2841 2842 := by
  intro i hlo hhi
  have h : i = 2841 := by omega
  subst i
  exact disposition_at_2841


theorem disposition_interval_2842 : Interval dispositionTest 2842 2843 := by
  intro i hlo hhi
  have h : i = 2842 := by omega
  subst i
  exact disposition_at_2842


theorem disposition_interval_2843 : Interval dispositionTest 2843 2844 := by
  intro i hlo hhi
  have h : i = 2843 := by omega
  subst i
  exact disposition_at_2843


theorem disposition_interval_2844 : Interval dispositionTest 2844 2845 := by
  intro i hlo hhi
  have h : i = 2844 := by omega
  subst i
  exact disposition_at_2844


theorem disposition_interval_2845 : Interval dispositionTest 2845 2846 := by
  intro i hlo hhi
  have h : i = 2845 := by omega
  subst i
  exact disposition_at_2845


theorem disposition_interval_2846 : Interval dispositionTest 2846 2847 := by
  intro i hlo hhi
  have h : i = 2846 := by omega
  subst i
  exact disposition_at_2846


theorem disposition_interval_2847 : Interval dispositionTest 2847 2848 := by
  intro i hlo hhi
  have h : i = 2847 := by omega
  subst i
  exact disposition_at_2847

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
