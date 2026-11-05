module

public import PolygonN7ClassificationPart006

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_02416 : FiniteChecks.Interval terminalTest 2416 2424 :=
  FiniteChecks.interval_of_check terminalTest 2416 8 (by decide +kernel)

theorem terminal_data_02424 : FiniteChecks.Interval terminalTest 2424 2432 :=
  FiniteChecks.interval_of_check terminalTest 2424 8 (by decide +kernel)

theorem terminal_data_02432 : FiniteChecks.Interval terminalTest 2432 2440 :=
  FiniteChecks.interval_of_check terminalTest 2432 8 (by decide +kernel)

theorem terminal_data_02440 : FiniteChecks.Interval terminalTest 2440 2448 :=
  FiniteChecks.interval_of_check terminalTest 2440 8 (by decide +kernel)

theorem terminal_data_02448 : FiniteChecks.Interval terminalTest 2448 2456 :=
  FiniteChecks.interval_of_check terminalTest 2448 8 (by decide +kernel)

theorem terminal_data_02456 : FiniteChecks.Interval terminalTest 2456 2464 :=
  FiniteChecks.interval_of_check terminalTest 2456 8 (by decide +kernel)

theorem terminal_data_02464 : FiniteChecks.Interval terminalTest 2464 2472 :=
  FiniteChecks.interval_of_check terminalTest 2464 8 (by decide +kernel)

theorem terminal_data_02472 : FiniteChecks.Interval terminalTest 2472 2480 :=
  FiniteChecks.interval_of_check terminalTest 2472 8 (by decide +kernel)

theorem terminal_data_02480 : FiniteChecks.Interval terminalTest 2480 2488 :=
  FiniteChecks.interval_of_check terminalTest 2480 8 (by decide +kernel)

theorem terminal_data_02488 : FiniteChecks.Interval terminalTest 2488 2496 :=
  FiniteChecks.interval_of_check terminalTest 2488 8 (by decide +kernel)

theorem terminal_data_02496 : FiniteChecks.Interval terminalTest 2496 2504 :=
  FiniteChecks.interval_of_check terminalTest 2496 8 (by decide +kernel)

theorem terminal_data_02504 : FiniteChecks.Interval terminalTest 2504 2512 :=
  FiniteChecks.interval_of_check terminalTest 2504 8 (by decide +kernel)

theorem terminal_data_02512 : FiniteChecks.Interval terminalTest 2512 2520 :=
  FiniteChecks.interval_of_check terminalTest 2512 8 (by decide +kernel)

theorem terminal_data_02520 : FiniteChecks.Interval terminalTest 2520 2528 :=
  FiniteChecks.interval_of_check terminalTest 2520 8 (by decide +kernel)

theorem terminal_data_02528 : FiniteChecks.Interval terminalTest 2528 2536 :=
  FiniteChecks.interval_of_check terminalTest 2528 8 (by decide +kernel)

theorem terminal_data_02536 : FiniteChecks.Interval terminalTest 2536 2544 :=
  FiniteChecks.interval_of_check terminalTest 2536 8 (by decide +kernel)

theorem terminal_data_02544 : FiniteChecks.Interval terminalTest 2544 2552 :=
  FiniteChecks.interval_of_check terminalTest 2544 8 (by decide +kernel)

theorem terminal_data_02552 : FiniteChecks.Interval terminalTest 2552 2560 :=
  FiniteChecks.interval_of_check terminalTest 2552 8 (by decide +kernel)

theorem terminal_data_02560 : FiniteChecks.Interval terminalTest 2560 2568 :=
  FiniteChecks.interval_of_check terminalTest 2560 8 (by decide +kernel)

theorem terminal_data_02568 : FiniteChecks.Interval terminalTest 2568 2576 :=
  FiniteChecks.interval_of_check terminalTest 2568 8 (by decide +kernel)

theorem terminal_data_02576 : FiniteChecks.Interval terminalTest 2576 2584 :=
  FiniteChecks.interval_of_check terminalTest 2576 8 (by decide +kernel)

theorem terminal_data_02584 : FiniteChecks.Interval terminalTest 2584 2592 :=
  FiniteChecks.interval_of_check terminalTest 2584 8 (by decide +kernel)

theorem terminal_data_02592 : FiniteChecks.Interval terminalTest 2592 2600 :=
  FiniteChecks.interval_of_check terminalTest 2592 8 (by decide +kernel)

theorem terminal_data_02600 : FiniteChecks.Interval terminalTest 2600 2608 :=
  FiniteChecks.interval_of_check terminalTest 2600 8 (by decide +kernel)

theorem terminal_data_02608 : FiniteChecks.Interval terminalTest 2608 2616 :=
  FiniteChecks.interval_of_check terminalTest 2608 8 (by decide +kernel)

theorem terminal_data_02616 : FiniteChecks.Interval terminalTest 2616 2624 :=
  FiniteChecks.interval_of_check terminalTest 2616 8 (by decide +kernel)

theorem terminal_data_02624 : FiniteChecks.Interval terminalTest 2624 2632 :=
  FiniteChecks.interval_of_check terminalTest 2624 8 (by decide +kernel)

theorem terminal_data_02632 : FiniteChecks.Interval terminalTest 2632 2640 :=
  FiniteChecks.interval_of_check terminalTest 2632 8 (by decide +kernel)

theorem terminal_data_02640 : FiniteChecks.Interval terminalTest 2640 2648 :=
  FiniteChecks.interval_of_check terminalTest 2640 8 (by decide +kernel)

theorem terminal_data_02648 : FiniteChecks.Interval terminalTest 2648 2656 :=
  FiniteChecks.interval_of_check terminalTest 2648 8 (by decide +kernel)

theorem terminal_data_02656 : FiniteChecks.Interval terminalTest 2656 2664 :=
  FiniteChecks.interval_of_check terminalTest 2656 8 (by decide +kernel)

theorem terminal_data_02664 : FiniteChecks.Interval terminalTest 2664 2672 :=
  FiniteChecks.interval_of_check terminalTest 2664 8 (by decide +kernel)

theorem terminal_data_02672 : FiniteChecks.Interval terminalTest 2672 2680 :=
  FiniteChecks.interval_of_check terminalTest 2672 8 (by decide +kernel)

theorem terminal_data_02680 : FiniteChecks.Interval terminalTest 2680 2688 :=
  FiniteChecks.interval_of_check terminalTest 2680 8 (by decide +kernel)

theorem terminal_data_02688 : FiniteChecks.Interval terminalTest 2688 2696 :=
  FiniteChecks.interval_of_check terminalTest 2688 8 (by decide +kernel)

theorem terminal_data_02696 : FiniteChecks.Interval terminalTest 2696 2704 :=
  FiniteChecks.interval_of_check terminalTest 2696 8 (by decide +kernel)

theorem terminal_data_02704 : FiniteChecks.Interval terminalTest 2704 2712 :=
  FiniteChecks.interval_of_check terminalTest 2704 8 (by decide +kernel)

theorem terminal_data_02712 : FiniteChecks.Interval terminalTest 2712 2720 :=
  FiniteChecks.interval_of_check terminalTest 2712 8 (by decide +kernel)

theorem terminal_data_02720 : FiniteChecks.Interval terminalTest 2720 2728 :=
  FiniteChecks.interval_of_check terminalTest 2720 8 (by decide +kernel)

theorem terminal_data_02728 : FiniteChecks.Interval terminalTest 2728 2736 :=
  FiniteChecks.interval_of_check terminalTest 2728 8 (by decide +kernel)

theorem terminal_data_02736 : FiniteChecks.Interval terminalTest 2736 2744 :=
  FiniteChecks.interval_of_check terminalTest 2736 8 (by decide +kernel)

theorem terminal_data_02744 : FiniteChecks.Interval terminalTest 2744 2752 :=
  FiniteChecks.interval_of_check terminalTest 2744 8 (by decide +kernel)

theorem terminal_data_02752 : FiniteChecks.Interval terminalTest 2752 2760 :=
  FiniteChecks.interval_of_check terminalTest 2752 8 (by decide +kernel)

theorem terminal_data_02760 : FiniteChecks.Interval terminalTest 2760 2768 :=
  FiniteChecks.interval_of_check terminalTest 2760 8 (by decide +kernel)

theorem terminal_data_02768 : FiniteChecks.Interval terminalTest 2768 2776 :=
  FiniteChecks.interval_of_check terminalTest 2768 8 (by decide +kernel)

theorem terminal_data_02776 : FiniteChecks.Interval terminalTest 2776 2784 :=
  FiniteChecks.interval_of_check terminalTest 2776 8 (by decide +kernel)

theorem terminal_data_02784 : FiniteChecks.Interval terminalTest 2784 2792 :=
  FiniteChecks.interval_of_check terminalTest 2784 8 (by decide +kernel)

theorem terminal_data_02792 : FiniteChecks.Interval terminalTest 2792 2800 :=
  FiniteChecks.interval_of_check terminalTest 2792 8 (by decide +kernel)

theorem terminal_data_02800 : FiniteChecks.Interval terminalTest 2800 2808 :=
  FiniteChecks.interval_of_check terminalTest 2800 8 (by decide +kernel)

theorem terminal_data_02808 : FiniteChecks.Interval terminalTest 2808 2816 :=
  FiniteChecks.interval_of_check terminalTest 2808 8 (by decide +kernel)

theorem terminal_data_02816 : FiniteChecks.Interval terminalTest 2816 2824 :=
  FiniteChecks.interval_of_check terminalTest 2816 8 (by decide +kernel)

theorem terminal_data_02824 : FiniteChecks.Interval terminalTest 2824 2832 :=
  FiniteChecks.interval_of_check terminalTest 2824 8 (by decide +kernel)

theorem terminal_data_02832 : FiniteChecks.Interval terminalTest 2832 2840 :=
  FiniteChecks.interval_of_check terminalTest 2832 8 (by decide +kernel)

theorem terminal_data_02840 : FiniteChecks.Interval terminalTest 2840 2848 :=
  FiniteChecks.interval_of_check terminalTest 2840 8 (by decide +kernel)

theorem terminal_data_02848 : FiniteChecks.Interval terminalTest 2848 2856 :=
  FiniteChecks.interval_of_check terminalTest 2848 8 (by decide +kernel)

theorem terminal_data_02856 : FiniteChecks.Interval terminalTest 2856 2864 :=
  FiniteChecks.interval_of_check terminalTest 2856 8 (by decide +kernel)

theorem terminal_data_02864 : FiniteChecks.Interval terminalTest 2864 2872 :=
  FiniteChecks.interval_of_check terminalTest 2864 8 (by decide +kernel)

theorem terminal_data_02872 : FiniteChecks.Interval terminalTest 2872 2880 :=
  FiniteChecks.interval_of_check terminalTest 2872 8 (by decide +kernel)

theorem terminal_data_02880 : FiniteChecks.Interval terminalTest 2880 2888 :=
  FiniteChecks.interval_of_check terminalTest 2880 8 (by decide +kernel)

theorem terminal_data_02888 : FiniteChecks.Interval terminalTest 2888 2896 :=
  FiniteChecks.interval_of_check terminalTest 2888 8 (by decide +kernel)

theorem terminal_data_02896 : FiniteChecks.Interval terminalTest 2896 2904 :=
  FiniteChecks.interval_of_check terminalTest 2896 8 (by decide +kernel)

theorem terminal_data_02904 : FiniteChecks.Interval terminalTest 2904 2912 :=
  FiniteChecks.interval_of_check terminalTest 2904 8 (by decide +kernel)

theorem terminal_data_02912 : FiniteChecks.Interval terminalTest 2912 2920 :=
  FiniteChecks.interval_of_check terminalTest 2912 8 (by decide +kernel)

theorem terminal_data_02920 : FiniteChecks.Interval terminalTest 2920 2928 :=
  FiniteChecks.interval_of_check terminalTest 2920 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
