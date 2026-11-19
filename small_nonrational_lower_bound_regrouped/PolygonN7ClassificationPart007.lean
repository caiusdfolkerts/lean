module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart006

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 02416 2416 2424 8
cert_terminal_data 02424 2424 2432 8
cert_terminal_data 02432 2432 2440 8
cert_terminal_data 02440 2440 2448 8
cert_terminal_data 02448 2448 2456 8
cert_terminal_data 02456 2456 2464 8
cert_terminal_data 02464 2464 2472 8
cert_terminal_data 02472 2472 2480 8
cert_terminal_data 02480 2480 2488 8
cert_terminal_data 02488 2488 2496 8
cert_terminal_data 02496 2496 2504 8
cert_terminal_data 02504 2504 2512 8
cert_terminal_data 02512 2512 2520 8
cert_terminal_data 02520 2520 2528 8
cert_terminal_data 02528 2528 2536 8
cert_terminal_data 02536 2536 2544 8
cert_terminal_data 02544 2544 2552 8
cert_terminal_data 02552 2552 2560 8
cert_terminal_data 02560 2560 2568 8
cert_terminal_data 02568 2568 2576 8
cert_terminal_data 02576 2576 2584 8
cert_terminal_data 02584 2584 2592 8
cert_terminal_data 02592 2592 2600 8
cert_terminal_data 02600 2600 2608 8
cert_terminal_data 02608 2608 2616 8
cert_terminal_data 02616 2616 2624 8
cert_terminal_data 02624 2624 2632 8
cert_terminal_data 02632 2632 2640 8
cert_terminal_data 02640 2640 2648 8
cert_terminal_data 02648 2648 2656 8
cert_terminal_data 02656 2656 2664 8
cert_terminal_data 02664 2664 2672 8
cert_terminal_data 02672 2672 2680 8
cert_terminal_data 02680 2680 2688 8
cert_terminal_data 02688 2688 2696 8
cert_terminal_data 02696 2696 2704 8
cert_terminal_data 02704 2704 2712 8
cert_terminal_data 02712 2712 2720 8
cert_terminal_data 02720 2720 2728 8
cert_terminal_data 02728 2728 2736 8
cert_terminal_data 02736 2736 2744 8
cert_terminal_data 02744 2744 2752 8
cert_terminal_data 02752 2752 2760 8
cert_terminal_data 02760 2760 2768 8
cert_terminal_data 02768 2768 2776 8
cert_terminal_data 02776 2776 2784 8
cert_terminal_data 02784 2784 2792 8
cert_terminal_data 02792 2792 2800 8
cert_terminal_data 02800 2800 2808 8
cert_terminal_data 02808 2808 2816 8
cert_terminal_data 02816 2816 2824 8
cert_terminal_data 02824 2824 2832 8
cert_terminal_data 02832 2832 2840 8
cert_terminal_data 02840 2840 2848 8
cert_terminal_data 02848 2848 2856 8
cert_terminal_data 02856 2856 2864 8
cert_terminal_data 02864 2864 2872 8
cert_terminal_data 02872 2872 2880 8
cert_terminal_data 02880 2880 2888 8
cert_terminal_data 02888 2888 2896 8
cert_terminal_data 02896 2896 2904 8
cert_terminal_data 02904 2904 2912 8
cert_terminal_data 02912 2912 2920 8
theorem terminal_data_02920 : FiniteChecks.Interval terminalTest 2920 2928 :=
  FiniteChecks.interval_of_check terminalTest 2920 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
