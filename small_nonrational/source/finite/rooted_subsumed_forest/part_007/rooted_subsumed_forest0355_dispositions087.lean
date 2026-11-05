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
theorem disposition_at_2784 : dispositionTest 2784 = true := by decide +kernel

theorem disposition_at_2785 : dispositionTest 2785 = true := by decide +kernel

theorem disposition_at_2786 : dispositionTest 2786 = true := by decide +kernel

theorem disposition_at_2787 : dispositionTest 2787 = true := by decide +kernel

theorem disposition_at_2788 : dispositionTest 2788 = true := by decide +kernel

theorem disposition_at_2789 : dispositionTest 2789 = true := by decide +kernel

theorem disposition_at_2790 : dispositionTest 2790 = true := by decide +kernel

theorem disposition_at_2791 : dispositionTest 2791 = true := by decide +kernel

theorem disposition_at_2792 : dispositionTest 2792 = true := by decide +kernel

theorem disposition_at_2793 : dispositionTest 2793 = true := by decide +kernel

theorem disposition_at_2794 : dispositionTest 2794 = true := by decide +kernel

theorem disposition_at_2795 : dispositionTest 2795 = true := by decide +kernel


theorem disposition_at_2796 : dispositionTest 2796 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2796).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M016.r1046.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M016.r1046) = true
  rw [Nonrational.OldTerminalMatches.M016.r1046_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2797 : dispositionTest 2797 = true := by decide +kernel

theorem disposition_at_2798 : dispositionTest 2798 = true := by decide +kernel

theorem disposition_at_2799 : dispositionTest 2799 = true := by decide +kernel

theorem disposition_at_2800 : dispositionTest 2800 = true := by decide +kernel

theorem disposition_at_2801 : dispositionTest 2801 = true := by decide +kernel

theorem disposition_at_2802 : dispositionTest 2802 = true := by decide +kernel

theorem disposition_at_2803 : dispositionTest 2803 = true := by decide +kernel

theorem disposition_at_2804 : dispositionTest 2804 = true := by decide +kernel

theorem disposition_at_2805 : dispositionTest 2805 = true := by decide +kernel

theorem disposition_at_2806 : dispositionTest 2806 = true := by decide +kernel

theorem disposition_at_2807 : dispositionTest 2807 = true := by decide +kernel

theorem disposition_at_2808 : dispositionTest 2808 = true := by decide +kernel

theorem disposition_at_2809 : dispositionTest 2809 = true := by decide +kernel

theorem disposition_at_2810 : dispositionTest 2810 = true := by decide +kernel

theorem disposition_at_2811 : dispositionTest 2811 = true := by decide +kernel

theorem disposition_at_2812 : dispositionTest 2812 = true := by decide +kernel

theorem disposition_at_2813 : dispositionTest 2813 = true := by decide +kernel

theorem disposition_at_2814 : dispositionTest 2814 = true := by decide +kernel

theorem disposition_at_2815 : dispositionTest 2815 = true := by decide +kernel

theorem disposition_interval_2784 : Interval dispositionTest 2784 2785 := by
  intro i hlo hhi
  have h : i = 2784 := by omega
  subst i
  exact disposition_at_2784


theorem disposition_interval_2785 : Interval dispositionTest 2785 2786 := by
  intro i hlo hhi
  have h : i = 2785 := by omega
  subst i
  exact disposition_at_2785


theorem disposition_interval_2786 : Interval dispositionTest 2786 2787 := by
  intro i hlo hhi
  have h : i = 2786 := by omega
  subst i
  exact disposition_at_2786


theorem disposition_interval_2787 : Interval dispositionTest 2787 2788 := by
  intro i hlo hhi
  have h : i = 2787 := by omega
  subst i
  exact disposition_at_2787


theorem disposition_interval_2788 : Interval dispositionTest 2788 2789 := by
  intro i hlo hhi
  have h : i = 2788 := by omega
  subst i
  exact disposition_at_2788


theorem disposition_interval_2789 : Interval dispositionTest 2789 2790 := by
  intro i hlo hhi
  have h : i = 2789 := by omega
  subst i
  exact disposition_at_2789


theorem disposition_interval_2790 : Interval dispositionTest 2790 2791 := by
  intro i hlo hhi
  have h : i = 2790 := by omega
  subst i
  exact disposition_at_2790


theorem disposition_interval_2791 : Interval dispositionTest 2791 2792 := by
  intro i hlo hhi
  have h : i = 2791 := by omega
  subst i
  exact disposition_at_2791


theorem disposition_interval_2792 : Interval dispositionTest 2792 2793 := by
  intro i hlo hhi
  have h : i = 2792 := by omega
  subst i
  exact disposition_at_2792


theorem disposition_interval_2793 : Interval dispositionTest 2793 2794 := by
  intro i hlo hhi
  have h : i = 2793 := by omega
  subst i
  exact disposition_at_2793


theorem disposition_interval_2794 : Interval dispositionTest 2794 2795 := by
  intro i hlo hhi
  have h : i = 2794 := by omega
  subst i
  exact disposition_at_2794


theorem disposition_interval_2795 : Interval dispositionTest 2795 2796 := by
  intro i hlo hhi
  have h : i = 2795 := by omega
  subst i
  exact disposition_at_2795


theorem disposition_interval_2796 : Interval dispositionTest 2796 2797 := by
  intro i hlo hhi
  have h : i = 2796 := by omega
  subst i
  exact disposition_at_2796


theorem disposition_interval_2797 : Interval dispositionTest 2797 2798 := by
  intro i hlo hhi
  have h : i = 2797 := by omega
  subst i
  exact disposition_at_2797


theorem disposition_interval_2798 : Interval dispositionTest 2798 2799 := by
  intro i hlo hhi
  have h : i = 2798 := by omega
  subst i
  exact disposition_at_2798


theorem disposition_interval_2799 : Interval dispositionTest 2799 2800 := by
  intro i hlo hhi
  have h : i = 2799 := by omega
  subst i
  exact disposition_at_2799


theorem disposition_interval_2800 : Interval dispositionTest 2800 2801 := by
  intro i hlo hhi
  have h : i = 2800 := by omega
  subst i
  exact disposition_at_2800


theorem disposition_interval_2801 : Interval dispositionTest 2801 2802 := by
  intro i hlo hhi
  have h : i = 2801 := by omega
  subst i
  exact disposition_at_2801


theorem disposition_interval_2802 : Interval dispositionTest 2802 2803 := by
  intro i hlo hhi
  have h : i = 2802 := by omega
  subst i
  exact disposition_at_2802


theorem disposition_interval_2803 : Interval dispositionTest 2803 2804 := by
  intro i hlo hhi
  have h : i = 2803 := by omega
  subst i
  exact disposition_at_2803


theorem disposition_interval_2804 : Interval dispositionTest 2804 2805 := by
  intro i hlo hhi
  have h : i = 2804 := by omega
  subst i
  exact disposition_at_2804


theorem disposition_interval_2805 : Interval dispositionTest 2805 2806 := by
  intro i hlo hhi
  have h : i = 2805 := by omega
  subst i
  exact disposition_at_2805


theorem disposition_interval_2806 : Interval dispositionTest 2806 2807 := by
  intro i hlo hhi
  have h : i = 2806 := by omega
  subst i
  exact disposition_at_2806


theorem disposition_interval_2807 : Interval dispositionTest 2807 2808 := by
  intro i hlo hhi
  have h : i = 2807 := by omega
  subst i
  exact disposition_at_2807


theorem disposition_interval_2808 : Interval dispositionTest 2808 2809 := by
  intro i hlo hhi
  have h : i = 2808 := by omega
  subst i
  exact disposition_at_2808


theorem disposition_interval_2809 : Interval dispositionTest 2809 2810 := by
  intro i hlo hhi
  have h : i = 2809 := by omega
  subst i
  exact disposition_at_2809


theorem disposition_interval_2810 : Interval dispositionTest 2810 2811 := by
  intro i hlo hhi
  have h : i = 2810 := by omega
  subst i
  exact disposition_at_2810


theorem disposition_interval_2811 : Interval dispositionTest 2811 2812 := by
  intro i hlo hhi
  have h : i = 2811 := by omega
  subst i
  exact disposition_at_2811


theorem disposition_interval_2812 : Interval dispositionTest 2812 2813 := by
  intro i hlo hhi
  have h : i = 2812 := by omega
  subst i
  exact disposition_at_2812


theorem disposition_interval_2813 : Interval dispositionTest 2813 2814 := by
  intro i hlo hhi
  have h : i = 2813 := by omega
  subst i
  exact disposition_at_2813


theorem disposition_interval_2814 : Interval dispositionTest 2814 2815 := by
  intro i hlo hhi
  have h : i = 2814 := by omega
  subst i
  exact disposition_at_2814


theorem disposition_interval_2815 : Interval dispositionTest 2815 2816 := by
  intro i hlo hhi
  have h : i = 2815 := by omega
  subst i
  exact disposition_at_2815

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
