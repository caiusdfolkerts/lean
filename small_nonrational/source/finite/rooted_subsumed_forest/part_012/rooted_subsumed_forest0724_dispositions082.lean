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
theorem disposition_at_2624 : dispositionTest 2624 = true := by decide +kernel

theorem disposition_at_2625 : dispositionTest 2625 = true := by decide +kernel

theorem disposition_at_2626 : dispositionTest 2626 = true := by decide +kernel

theorem disposition_at_2627 : dispositionTest 2627 = true := by decide +kernel

theorem disposition_at_2628 : dispositionTest 2628 = true := by decide +kernel

theorem disposition_at_2629 : dispositionTest 2629 = true := by decide +kernel

theorem disposition_at_2630 : dispositionTest 2630 = true := by decide +kernel

theorem disposition_at_2631 : dispositionTest 2631 = true := by decide +kernel

theorem disposition_at_2632 : dispositionTest 2632 = true := by decide +kernel

theorem disposition_at_2633 : dispositionTest 2633 = true := by decide +kernel

theorem disposition_at_2634 : dispositionTest 2634 = true := by decide +kernel

theorem disposition_at_2635 : dispositionTest 2635 = true := by decide +kernel

theorem disposition_at_2636 : dispositionTest 2636 = true := by decide +kernel

theorem disposition_at_2637 : dispositionTest 2637 = true := by decide +kernel

theorem disposition_at_2638 : dispositionTest 2638 = true := by decide +kernel

theorem disposition_at_2639 : dispositionTest 2639 = true := by decide +kernel

theorem disposition_at_2640 : dispositionTest 2640 = true := by decide +kernel

theorem disposition_at_2641 : dispositionTest 2641 = true := by decide +kernel

theorem disposition_at_2642 : dispositionTest 2642 = true := by decide +kernel

theorem disposition_at_2643 : dispositionTest 2643 = true := by decide +kernel

theorem disposition_at_2644 : dispositionTest 2644 = true := by decide +kernel

theorem disposition_at_2645 : dispositionTest 2645 = true := by decide +kernel

theorem disposition_at_2646 : dispositionTest 2646 = true := by decide +kernel

theorem disposition_at_2647 : dispositionTest 2647 = true := by decide +kernel

theorem disposition_at_2648 : dispositionTest 2648 = true := by decide +kernel

theorem disposition_at_2649 : dispositionTest 2649 = true := by decide +kernel

theorem disposition_at_2650 : dispositionTest 2650 = true := by decide +kernel

theorem disposition_at_2651 : dispositionTest 2651 = true := by decide +kernel

theorem disposition_at_2652 : dispositionTest 2652 = true := by decide +kernel

theorem disposition_at_2653 : dispositionTest 2653 = true := by decide +kernel

theorem disposition_at_2654 : dispositionTest 2654 = true := by decide +kernel

theorem disposition_at_2655 : dispositionTest 2655 = true := by decide +kernel

theorem disposition_interval_2624 : Interval dispositionTest 2624 2625 := by
  intro i hlo hhi
  have h : i = 2624 := by omega
  subst i
  exact disposition_at_2624


theorem disposition_interval_2625 : Interval dispositionTest 2625 2626 := by
  intro i hlo hhi
  have h : i = 2625 := by omega
  subst i
  exact disposition_at_2625


theorem disposition_interval_2626 : Interval dispositionTest 2626 2627 := by
  intro i hlo hhi
  have h : i = 2626 := by omega
  subst i
  exact disposition_at_2626


theorem disposition_interval_2627 : Interval dispositionTest 2627 2628 := by
  intro i hlo hhi
  have h : i = 2627 := by omega
  subst i
  exact disposition_at_2627


theorem disposition_interval_2628 : Interval dispositionTest 2628 2629 := by
  intro i hlo hhi
  have h : i = 2628 := by omega
  subst i
  exact disposition_at_2628


theorem disposition_interval_2629 : Interval dispositionTest 2629 2630 := by
  intro i hlo hhi
  have h : i = 2629 := by omega
  subst i
  exact disposition_at_2629


theorem disposition_interval_2630 : Interval dispositionTest 2630 2631 := by
  intro i hlo hhi
  have h : i = 2630 := by omega
  subst i
  exact disposition_at_2630


theorem disposition_interval_2631 : Interval dispositionTest 2631 2632 := by
  intro i hlo hhi
  have h : i = 2631 := by omega
  subst i
  exact disposition_at_2631


theorem disposition_interval_2632 : Interval dispositionTest 2632 2633 := by
  intro i hlo hhi
  have h : i = 2632 := by omega
  subst i
  exact disposition_at_2632


theorem disposition_interval_2633 : Interval dispositionTest 2633 2634 := by
  intro i hlo hhi
  have h : i = 2633 := by omega
  subst i
  exact disposition_at_2633


theorem disposition_interval_2634 : Interval dispositionTest 2634 2635 := by
  intro i hlo hhi
  have h : i = 2634 := by omega
  subst i
  exact disposition_at_2634


theorem disposition_interval_2635 : Interval dispositionTest 2635 2636 := by
  intro i hlo hhi
  have h : i = 2635 := by omega
  subst i
  exact disposition_at_2635


theorem disposition_interval_2636 : Interval dispositionTest 2636 2637 := by
  intro i hlo hhi
  have h : i = 2636 := by omega
  subst i
  exact disposition_at_2636


theorem disposition_interval_2637 : Interval dispositionTest 2637 2638 := by
  intro i hlo hhi
  have h : i = 2637 := by omega
  subst i
  exact disposition_at_2637


theorem disposition_interval_2638 : Interval dispositionTest 2638 2639 := by
  intro i hlo hhi
  have h : i = 2638 := by omega
  subst i
  exact disposition_at_2638


theorem disposition_interval_2639 : Interval dispositionTest 2639 2640 := by
  intro i hlo hhi
  have h : i = 2639 := by omega
  subst i
  exact disposition_at_2639


theorem disposition_interval_2640 : Interval dispositionTest 2640 2641 := by
  intro i hlo hhi
  have h : i = 2640 := by omega
  subst i
  exact disposition_at_2640


theorem disposition_interval_2641 : Interval dispositionTest 2641 2642 := by
  intro i hlo hhi
  have h : i = 2641 := by omega
  subst i
  exact disposition_at_2641


theorem disposition_interval_2642 : Interval dispositionTest 2642 2643 := by
  intro i hlo hhi
  have h : i = 2642 := by omega
  subst i
  exact disposition_at_2642


theorem disposition_interval_2643 : Interval dispositionTest 2643 2644 := by
  intro i hlo hhi
  have h : i = 2643 := by omega
  subst i
  exact disposition_at_2643


theorem disposition_interval_2644 : Interval dispositionTest 2644 2645 := by
  intro i hlo hhi
  have h : i = 2644 := by omega
  subst i
  exact disposition_at_2644


theorem disposition_interval_2645 : Interval dispositionTest 2645 2646 := by
  intro i hlo hhi
  have h : i = 2645 := by omega
  subst i
  exact disposition_at_2645


theorem disposition_interval_2646 : Interval dispositionTest 2646 2647 := by
  intro i hlo hhi
  have h : i = 2646 := by omega
  subst i
  exact disposition_at_2646


theorem disposition_interval_2647 : Interval dispositionTest 2647 2648 := by
  intro i hlo hhi
  have h : i = 2647 := by omega
  subst i
  exact disposition_at_2647


theorem disposition_interval_2648 : Interval dispositionTest 2648 2649 := by
  intro i hlo hhi
  have h : i = 2648 := by omega
  subst i
  exact disposition_at_2648


theorem disposition_interval_2649 : Interval dispositionTest 2649 2650 := by
  intro i hlo hhi
  have h : i = 2649 := by omega
  subst i
  exact disposition_at_2649


theorem disposition_interval_2650 : Interval dispositionTest 2650 2651 := by
  intro i hlo hhi
  have h : i = 2650 := by omega
  subst i
  exact disposition_at_2650


theorem disposition_interval_2651 : Interval dispositionTest 2651 2652 := by
  intro i hlo hhi
  have h : i = 2651 := by omega
  subst i
  exact disposition_at_2651


theorem disposition_interval_2652 : Interval dispositionTest 2652 2653 := by
  intro i hlo hhi
  have h : i = 2652 := by omega
  subst i
  exact disposition_at_2652


theorem disposition_interval_2653 : Interval dispositionTest 2653 2654 := by
  intro i hlo hhi
  have h : i = 2653 := by omega
  subst i
  exact disposition_at_2653


theorem disposition_interval_2654 : Interval dispositionTest 2654 2655 := by
  intro i hlo hhi
  have h : i = 2654 := by omega
  subst i
  exact disposition_at_2654


theorem disposition_interval_2655 : Interval dispositionTest 2655 2656 := by
  intro i hlo hhi
  have h : i = 2655 := by omega
  subst i
  exact disposition_at_2655

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
