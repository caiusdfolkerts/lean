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
theorem disposition_at_2848 : dispositionTest 2848 = true := by decide +kernel

theorem disposition_at_2849 : dispositionTest 2849 = true := by decide +kernel

theorem disposition_at_2850 : dispositionTest 2850 = true := by decide +kernel

theorem disposition_at_2851 : dispositionTest 2851 = true := by decide +kernel

theorem disposition_at_2852 : dispositionTest 2852 = true := by decide +kernel

theorem disposition_at_2853 : dispositionTest 2853 = true := by decide +kernel

theorem disposition_at_2854 : dispositionTest 2854 = true := by decide +kernel

theorem disposition_at_2855 : dispositionTest 2855 = true := by decide +kernel

theorem disposition_at_2856 : dispositionTest 2856 = true := by decide +kernel

theorem disposition_at_2857 : dispositionTest 2857 = true := by decide +kernel

theorem disposition_at_2858 : dispositionTest 2858 = true := by decide +kernel

theorem disposition_at_2859 : dispositionTest 2859 = true := by decide +kernel

theorem disposition_at_2860 : dispositionTest 2860 = true := by decide +kernel

theorem disposition_at_2861 : dispositionTest 2861 = true := by decide +kernel

theorem disposition_at_2862 : dispositionTest 2862 = true := by decide +kernel

theorem disposition_at_2863 : dispositionTest 2863 = true := by decide +kernel

theorem disposition_at_2864 : dispositionTest 2864 = true := by decide +kernel

theorem disposition_at_2865 : dispositionTest 2865 = true := by decide +kernel

theorem disposition_at_2866 : dispositionTest 2866 = true := by decide +kernel

theorem disposition_at_2867 : dispositionTest 2867 = true := by decide +kernel


theorem disposition_at_2868 : dispositionTest 2868 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2868).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1049.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1049) = true
  rw [Nonrational.OldTerminalMatches.M016.r1049_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2869 : dispositionTest 2869 = true := by decide +kernel

theorem disposition_at_2870 : dispositionTest 2870 = true := by decide +kernel

theorem disposition_at_2871 : dispositionTest 2871 = true := by decide +kernel

theorem disposition_at_2872 : dispositionTest 2872 = true := by decide +kernel

theorem disposition_at_2873 : dispositionTest 2873 = true := by decide +kernel

theorem disposition_at_2874 : dispositionTest 2874 = true := by decide +kernel

theorem disposition_at_2875 : dispositionTest 2875 = true := by decide +kernel

theorem disposition_at_2876 : dispositionTest 2876 = true := by decide +kernel

theorem disposition_at_2877 : dispositionTest 2877 = true := by decide +kernel

theorem disposition_at_2878 : dispositionTest 2878 = true := by decide +kernel

theorem disposition_at_2879 : dispositionTest 2879 = true := by decide +kernel

theorem disposition_interval_2848 : Interval dispositionTest 2848 2849 := by
  intro i hlo hhi
  have h : i = 2848 := by omega
  subst i
  exact disposition_at_2848


theorem disposition_interval_2849 : Interval dispositionTest 2849 2850 := by
  intro i hlo hhi
  have h : i = 2849 := by omega
  subst i
  exact disposition_at_2849


theorem disposition_interval_2850 : Interval dispositionTest 2850 2851 := by
  intro i hlo hhi
  have h : i = 2850 := by omega
  subst i
  exact disposition_at_2850


theorem disposition_interval_2851 : Interval dispositionTest 2851 2852 := by
  intro i hlo hhi
  have h : i = 2851 := by omega
  subst i
  exact disposition_at_2851


theorem disposition_interval_2852 : Interval dispositionTest 2852 2853 := by
  intro i hlo hhi
  have h : i = 2852 := by omega
  subst i
  exact disposition_at_2852


theorem disposition_interval_2853 : Interval dispositionTest 2853 2854 := by
  intro i hlo hhi
  have h : i = 2853 := by omega
  subst i
  exact disposition_at_2853


theorem disposition_interval_2854 : Interval dispositionTest 2854 2855 := by
  intro i hlo hhi
  have h : i = 2854 := by omega
  subst i
  exact disposition_at_2854


theorem disposition_interval_2855 : Interval dispositionTest 2855 2856 := by
  intro i hlo hhi
  have h : i = 2855 := by omega
  subst i
  exact disposition_at_2855


theorem disposition_interval_2856 : Interval dispositionTest 2856 2857 := by
  intro i hlo hhi
  have h : i = 2856 := by omega
  subst i
  exact disposition_at_2856


theorem disposition_interval_2857 : Interval dispositionTest 2857 2858 := by
  intro i hlo hhi
  have h : i = 2857 := by omega
  subst i
  exact disposition_at_2857


theorem disposition_interval_2858 : Interval dispositionTest 2858 2859 := by
  intro i hlo hhi
  have h : i = 2858 := by omega
  subst i
  exact disposition_at_2858


theorem disposition_interval_2859 : Interval dispositionTest 2859 2860 := by
  intro i hlo hhi
  have h : i = 2859 := by omega
  subst i
  exact disposition_at_2859


theorem disposition_interval_2860 : Interval dispositionTest 2860 2861 := by
  intro i hlo hhi
  have h : i = 2860 := by omega
  subst i
  exact disposition_at_2860


theorem disposition_interval_2861 : Interval dispositionTest 2861 2862 := by
  intro i hlo hhi
  have h : i = 2861 := by omega
  subst i
  exact disposition_at_2861


theorem disposition_interval_2862 : Interval dispositionTest 2862 2863 := by
  intro i hlo hhi
  have h : i = 2862 := by omega
  subst i
  exact disposition_at_2862


theorem disposition_interval_2863 : Interval dispositionTest 2863 2864 := by
  intro i hlo hhi
  have h : i = 2863 := by omega
  subst i
  exact disposition_at_2863


theorem disposition_interval_2864 : Interval dispositionTest 2864 2865 := by
  intro i hlo hhi
  have h : i = 2864 := by omega
  subst i
  exact disposition_at_2864


theorem disposition_interval_2865 : Interval dispositionTest 2865 2866 := by
  intro i hlo hhi
  have h : i = 2865 := by omega
  subst i
  exact disposition_at_2865


theorem disposition_interval_2866 : Interval dispositionTest 2866 2867 := by
  intro i hlo hhi
  have h : i = 2866 := by omega
  subst i
  exact disposition_at_2866


theorem disposition_interval_2867 : Interval dispositionTest 2867 2868 := by
  intro i hlo hhi
  have h : i = 2867 := by omega
  subst i
  exact disposition_at_2867


theorem disposition_interval_2868 : Interval dispositionTest 2868 2869 := by
  intro i hlo hhi
  have h : i = 2868 := by omega
  subst i
  exact disposition_at_2868


theorem disposition_interval_2869 : Interval dispositionTest 2869 2870 := by
  intro i hlo hhi
  have h : i = 2869 := by omega
  subst i
  exact disposition_at_2869


theorem disposition_interval_2870 : Interval dispositionTest 2870 2871 := by
  intro i hlo hhi
  have h : i = 2870 := by omega
  subst i
  exact disposition_at_2870


theorem disposition_interval_2871 : Interval dispositionTest 2871 2872 := by
  intro i hlo hhi
  have h : i = 2871 := by omega
  subst i
  exact disposition_at_2871


theorem disposition_interval_2872 : Interval dispositionTest 2872 2873 := by
  intro i hlo hhi
  have h : i = 2872 := by omega
  subst i
  exact disposition_at_2872


theorem disposition_interval_2873 : Interval dispositionTest 2873 2874 := by
  intro i hlo hhi
  have h : i = 2873 := by omega
  subst i
  exact disposition_at_2873


theorem disposition_interval_2874 : Interval dispositionTest 2874 2875 := by
  intro i hlo hhi
  have h : i = 2874 := by omega
  subst i
  exact disposition_at_2874


theorem disposition_interval_2875 : Interval dispositionTest 2875 2876 := by
  intro i hlo hhi
  have h : i = 2875 := by omega
  subst i
  exact disposition_at_2875


theorem disposition_interval_2876 : Interval dispositionTest 2876 2877 := by
  intro i hlo hhi
  have h : i = 2876 := by omega
  subst i
  exact disposition_at_2876


theorem disposition_interval_2877 : Interval dispositionTest 2877 2878 := by
  intro i hlo hhi
  have h : i = 2877 := by omega
  subst i
  exact disposition_at_2877


theorem disposition_interval_2878 : Interval dispositionTest 2878 2879 := by
  intro i hlo hhi
  have h : i = 2878 := by omega
  subst i
  exact disposition_at_2878


theorem disposition_interval_2879 : Interval dispositionTest 2879 2880 := by
  intro i hlo hhi
  have h : i = 2879 := by omega
  subst i
  exact disposition_at_2879

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
