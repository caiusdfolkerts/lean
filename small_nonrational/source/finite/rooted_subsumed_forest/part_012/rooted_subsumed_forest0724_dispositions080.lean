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
theorem disposition_at_2560 : dispositionTest 2560 = true := by decide +kernel

theorem disposition_at_2561 : dispositionTest 2561 = true := by decide +kernel

theorem disposition_at_2562 : dispositionTest 2562 = true := by decide +kernel

theorem disposition_at_2563 : dispositionTest 2563 = true := by decide +kernel

theorem disposition_at_2564 : dispositionTest 2564 = true := by decide +kernel

theorem disposition_at_2565 : dispositionTest 2565 = true := by decide +kernel

theorem disposition_at_2566 : dispositionTest 2566 = true := by decide +kernel

theorem disposition_at_2567 : dispositionTest 2567 = true := by decide +kernel

theorem disposition_at_2568 : dispositionTest 2568 = true := by decide +kernel

theorem disposition_at_2569 : dispositionTest 2569 = true := by decide +kernel

theorem disposition_at_2570 : dispositionTest 2570 = true := by decide +kernel

theorem disposition_at_2571 : dispositionTest 2571 = true := by decide +kernel

theorem disposition_at_2572 : dispositionTest 2572 = true := by decide +kernel

theorem disposition_at_2573 : dispositionTest 2573 = true := by decide +kernel

theorem disposition_at_2574 : dispositionTest 2574 = true := by decide +kernel

theorem disposition_at_2575 : dispositionTest 2575 = true := by decide +kernel

theorem disposition_at_2576 : dispositionTest 2576 = true := by decide +kernel

theorem disposition_at_2577 : dispositionTest 2577 = true := by decide +kernel

theorem disposition_at_2578 : dispositionTest 2578 = true := by decide +kernel

theorem disposition_at_2579 : dispositionTest 2579 = true := by decide +kernel

theorem disposition_at_2580 : dispositionTest 2580 = true := by decide +kernel

theorem disposition_at_2581 : dispositionTest 2581 = true := by decide +kernel

theorem disposition_at_2582 : dispositionTest 2582 = true := by decide +kernel

theorem disposition_at_2583 : dispositionTest 2583 = true := by decide +kernel

theorem disposition_at_2584 : dispositionTest 2584 = true := by decide +kernel

theorem disposition_at_2585 : dispositionTest 2585 = true := by decide +kernel

theorem disposition_at_2586 : dispositionTest 2586 = true := by decide +kernel

theorem disposition_at_2587 : dispositionTest 2587 = true := by decide +kernel

theorem disposition_at_2588 : dispositionTest 2588 = true := by decide +kernel

theorem disposition_at_2589 : dispositionTest 2589 = true := by decide +kernel

theorem disposition_at_2590 : dispositionTest 2590 = true := by decide +kernel

theorem disposition_at_2591 : dispositionTest 2591 = true := by decide +kernel

theorem disposition_interval_2560 : Interval dispositionTest 2560 2561 := by
  intro i hlo hhi
  have h : i = 2560 := by omega
  subst i
  exact disposition_at_2560


theorem disposition_interval_2561 : Interval dispositionTest 2561 2562 := by
  intro i hlo hhi
  have h : i = 2561 := by omega
  subst i
  exact disposition_at_2561


theorem disposition_interval_2562 : Interval dispositionTest 2562 2563 := by
  intro i hlo hhi
  have h : i = 2562 := by omega
  subst i
  exact disposition_at_2562


theorem disposition_interval_2563 : Interval dispositionTest 2563 2564 := by
  intro i hlo hhi
  have h : i = 2563 := by omega
  subst i
  exact disposition_at_2563


theorem disposition_interval_2564 : Interval dispositionTest 2564 2565 := by
  intro i hlo hhi
  have h : i = 2564 := by omega
  subst i
  exact disposition_at_2564


theorem disposition_interval_2565 : Interval dispositionTest 2565 2566 := by
  intro i hlo hhi
  have h : i = 2565 := by omega
  subst i
  exact disposition_at_2565


theorem disposition_interval_2566 : Interval dispositionTest 2566 2567 := by
  intro i hlo hhi
  have h : i = 2566 := by omega
  subst i
  exact disposition_at_2566


theorem disposition_interval_2567 : Interval dispositionTest 2567 2568 := by
  intro i hlo hhi
  have h : i = 2567 := by omega
  subst i
  exact disposition_at_2567


theorem disposition_interval_2568 : Interval dispositionTest 2568 2569 := by
  intro i hlo hhi
  have h : i = 2568 := by omega
  subst i
  exact disposition_at_2568


theorem disposition_interval_2569 : Interval dispositionTest 2569 2570 := by
  intro i hlo hhi
  have h : i = 2569 := by omega
  subst i
  exact disposition_at_2569


theorem disposition_interval_2570 : Interval dispositionTest 2570 2571 := by
  intro i hlo hhi
  have h : i = 2570 := by omega
  subst i
  exact disposition_at_2570


theorem disposition_interval_2571 : Interval dispositionTest 2571 2572 := by
  intro i hlo hhi
  have h : i = 2571 := by omega
  subst i
  exact disposition_at_2571


theorem disposition_interval_2572 : Interval dispositionTest 2572 2573 := by
  intro i hlo hhi
  have h : i = 2572 := by omega
  subst i
  exact disposition_at_2572


theorem disposition_interval_2573 : Interval dispositionTest 2573 2574 := by
  intro i hlo hhi
  have h : i = 2573 := by omega
  subst i
  exact disposition_at_2573


theorem disposition_interval_2574 : Interval dispositionTest 2574 2575 := by
  intro i hlo hhi
  have h : i = 2574 := by omega
  subst i
  exact disposition_at_2574


theorem disposition_interval_2575 : Interval dispositionTest 2575 2576 := by
  intro i hlo hhi
  have h : i = 2575 := by omega
  subst i
  exact disposition_at_2575


theorem disposition_interval_2576 : Interval dispositionTest 2576 2577 := by
  intro i hlo hhi
  have h : i = 2576 := by omega
  subst i
  exact disposition_at_2576


theorem disposition_interval_2577 : Interval dispositionTest 2577 2578 := by
  intro i hlo hhi
  have h : i = 2577 := by omega
  subst i
  exact disposition_at_2577


theorem disposition_interval_2578 : Interval dispositionTest 2578 2579 := by
  intro i hlo hhi
  have h : i = 2578 := by omega
  subst i
  exact disposition_at_2578


theorem disposition_interval_2579 : Interval dispositionTest 2579 2580 := by
  intro i hlo hhi
  have h : i = 2579 := by omega
  subst i
  exact disposition_at_2579


theorem disposition_interval_2580 : Interval dispositionTest 2580 2581 := by
  intro i hlo hhi
  have h : i = 2580 := by omega
  subst i
  exact disposition_at_2580


theorem disposition_interval_2581 : Interval dispositionTest 2581 2582 := by
  intro i hlo hhi
  have h : i = 2581 := by omega
  subst i
  exact disposition_at_2581


theorem disposition_interval_2582 : Interval dispositionTest 2582 2583 := by
  intro i hlo hhi
  have h : i = 2582 := by omega
  subst i
  exact disposition_at_2582


theorem disposition_interval_2583 : Interval dispositionTest 2583 2584 := by
  intro i hlo hhi
  have h : i = 2583 := by omega
  subst i
  exact disposition_at_2583


theorem disposition_interval_2584 : Interval dispositionTest 2584 2585 := by
  intro i hlo hhi
  have h : i = 2584 := by omega
  subst i
  exact disposition_at_2584


theorem disposition_interval_2585 : Interval dispositionTest 2585 2586 := by
  intro i hlo hhi
  have h : i = 2585 := by omega
  subst i
  exact disposition_at_2585


theorem disposition_interval_2586 : Interval dispositionTest 2586 2587 := by
  intro i hlo hhi
  have h : i = 2586 := by omega
  subst i
  exact disposition_at_2586


theorem disposition_interval_2587 : Interval dispositionTest 2587 2588 := by
  intro i hlo hhi
  have h : i = 2587 := by omega
  subst i
  exact disposition_at_2587


theorem disposition_interval_2588 : Interval dispositionTest 2588 2589 := by
  intro i hlo hhi
  have h : i = 2588 := by omega
  subst i
  exact disposition_at_2588


theorem disposition_interval_2589 : Interval dispositionTest 2589 2590 := by
  intro i hlo hhi
  have h : i = 2589 := by omega
  subst i
  exact disposition_at_2589


theorem disposition_interval_2590 : Interval dispositionTest 2590 2591 := by
  intro i hlo hhi
  have h : i = 2590 := by omega
  subst i
  exact disposition_at_2590


theorem disposition_interval_2591 : Interval dispositionTest 2591 2592 := by
  intro i hlo hhi
  have h : i = 2591 := by omega
  subst i
  exact disposition_at_2591

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
