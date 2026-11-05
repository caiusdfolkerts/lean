module

public import PolygonN7ClassificationPart008

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_03440 : FiniteChecks.Interval terminalTest 3440 3448 :=
  FiniteChecks.interval_of_check terminalTest 3440 8 (by decide +kernel)

theorem terminal_data_03448 : FiniteChecks.Interval terminalTest 3448 3456 :=
  FiniteChecks.interval_of_check terminalTest 3448 8 (by decide +kernel)

theorem terminal_data_03456 : FiniteChecks.Interval terminalTest 3456 3464 :=
  FiniteChecks.interval_of_check terminalTest 3456 8 (by decide +kernel)

theorem terminal_data_03464 : FiniteChecks.Interval terminalTest 3464 3472 :=
  FiniteChecks.interval_of_check terminalTest 3464 8 (by decide +kernel)

theorem terminal_data_03472 : FiniteChecks.Interval terminalTest 3472 3480 :=
  FiniteChecks.interval_of_check terminalTest 3472 8 (by decide +kernel)

theorem terminal_data_03480 : FiniteChecks.Interval terminalTest 3480 3488 :=
  FiniteChecks.interval_of_check terminalTest 3480 8 (by decide +kernel)

theorem terminal_data_03488 : FiniteChecks.Interval terminalTest 3488 3496 :=
  FiniteChecks.interval_of_check terminalTest 3488 8 (by decide +kernel)

theorem terminal_data_03496 : FiniteChecks.Interval terminalTest 3496 3504 :=
  FiniteChecks.interval_of_check terminalTest 3496 8 (by decide +kernel)

theorem terminal_data_03504 : FiniteChecks.Interval terminalTest 3504 3512 :=
  FiniteChecks.interval_of_check terminalTest 3504 8 (by decide +kernel)

theorem terminal_data_03512 : FiniteChecks.Interval terminalTest 3512 3520 :=
  FiniteChecks.interval_of_check terminalTest 3512 8 (by decide +kernel)

theorem terminal_data_03520 : FiniteChecks.Interval terminalTest 3520 3528 :=
  FiniteChecks.interval_of_check terminalTest 3520 8 (by decide +kernel)

theorem terminal_data_03528 : FiniteChecks.Interval terminalTest 3528 3536 :=
  FiniteChecks.interval_of_check terminalTest 3528 8 (by decide +kernel)

theorem terminal_data_03536 : FiniteChecks.Interval terminalTest 3536 3544 :=
  FiniteChecks.interval_of_check terminalTest 3536 8 (by decide +kernel)

theorem terminal_data_03544 : FiniteChecks.Interval terminalTest 3544 3552 :=
  FiniteChecks.interval_of_check terminalTest 3544 8 (by decide +kernel)

theorem terminal_data_03552 : FiniteChecks.Interval terminalTest 3552 3560 :=
  FiniteChecks.interval_of_check terminalTest 3552 8 (by decide +kernel)

theorem terminal_data_03560 : FiniteChecks.Interval terminalTest 3560 3568 :=
  FiniteChecks.interval_of_check terminalTest 3560 8 (by decide +kernel)

theorem terminal_data_03568 : FiniteChecks.Interval terminalTest 3568 3576 :=
  FiniteChecks.interval_of_check terminalTest 3568 8 (by decide +kernel)

theorem terminal_data_03576 : FiniteChecks.Interval terminalTest 3576 3584 :=
  FiniteChecks.interval_of_check terminalTest 3576 8 (by decide +kernel)

theorem terminal_data_03584 : FiniteChecks.Interval terminalTest 3584 3592 :=
  FiniteChecks.interval_of_check terminalTest 3584 8 (by decide +kernel)

theorem terminal_data_03592 : FiniteChecks.Interval terminalTest 3592 3600 :=
  FiniteChecks.interval_of_check terminalTest 3592 8 (by decide +kernel)

theorem terminal_data_03600 : FiniteChecks.Interval terminalTest 3600 3608 :=
  FiniteChecks.interval_of_check terminalTest 3600 8 (by decide +kernel)

theorem terminal_data_03608 : FiniteChecks.Interval terminalTest 3608 3616 :=
  FiniteChecks.interval_of_check terminalTest 3608 8 (by decide +kernel)

theorem terminal_data_03616 : FiniteChecks.Interval terminalTest 3616 3624 :=
  FiniteChecks.interval_of_check terminalTest 3616 8 (by decide +kernel)

theorem terminal_data_03624 : FiniteChecks.Interval terminalTest 3624 3632 :=
  FiniteChecks.interval_of_check terminalTest 3624 8 (by decide +kernel)

theorem terminal_data_03632 : FiniteChecks.Interval terminalTest 3632 3640 :=
  FiniteChecks.interval_of_check terminalTest 3632 8 (by decide +kernel)

theorem terminal_data_03640 : FiniteChecks.Interval terminalTest 3640 3648 :=
  FiniteChecks.interval_of_check terminalTest 3640 8 (by decide +kernel)

theorem terminal_data_03648 : FiniteChecks.Interval terminalTest 3648 3656 :=
  FiniteChecks.interval_of_check terminalTest 3648 8 (by decide +kernel)

theorem terminal_data_03656 : FiniteChecks.Interval terminalTest 3656 3664 :=
  FiniteChecks.interval_of_check terminalTest 3656 8 (by decide +kernel)

theorem terminal_data_03664 : FiniteChecks.Interval terminalTest 3664 3672 :=
  FiniteChecks.interval_of_check terminalTest 3664 8 (by decide +kernel)

theorem terminal_data_03672 : FiniteChecks.Interval terminalTest 3672 3680 :=
  FiniteChecks.interval_of_check terminalTest 3672 8 (by decide +kernel)

theorem terminal_data_03680 : FiniteChecks.Interval terminalTest 3680 3688 :=
  FiniteChecks.interval_of_check terminalTest 3680 8 (by decide +kernel)

theorem terminal_data_03688 : FiniteChecks.Interval terminalTest 3688 3696 :=
  FiniteChecks.interval_of_check terminalTest 3688 8 (by decide +kernel)

theorem terminal_data_03696 : FiniteChecks.Interval terminalTest 3696 3704 :=
  FiniteChecks.interval_of_check terminalTest 3696 8 (by decide +kernel)

theorem terminal_data_03704 : FiniteChecks.Interval terminalTest 3704 3712 :=
  FiniteChecks.interval_of_check terminalTest 3704 8 (by decide +kernel)

theorem terminal_data_03712 : FiniteChecks.Interval terminalTest 3712 3720 :=
  FiniteChecks.interval_of_check terminalTest 3712 8 (by decide +kernel)

theorem terminal_data_03720 : FiniteChecks.Interval terminalTest 3720 3728 :=
  FiniteChecks.interval_of_check terminalTest 3720 8 (by decide +kernel)

theorem terminal_data_03728 : FiniteChecks.Interval terminalTest 3728 3736 :=
  FiniteChecks.interval_of_check terminalTest 3728 8 (by decide +kernel)

theorem terminal_data_03736 : FiniteChecks.Interval terminalTest 3736 3744 :=
  FiniteChecks.interval_of_check terminalTest 3736 8 (by decide +kernel)

theorem terminal_data_03744 : FiniteChecks.Interval terminalTest 3744 3752 :=
  FiniteChecks.interval_of_check terminalTest 3744 8 (by decide +kernel)

theorem terminal_data_03752 : FiniteChecks.Interval terminalTest 3752 3760 :=
  FiniteChecks.interval_of_check terminalTest 3752 8 (by decide +kernel)

theorem terminal_data_03760 : FiniteChecks.Interval terminalTest 3760 3768 :=
  FiniteChecks.interval_of_check terminalTest 3760 8 (by decide +kernel)

theorem terminal_data_03768 : FiniteChecks.Interval terminalTest 3768 3776 :=
  FiniteChecks.interval_of_check terminalTest 3768 8 (by decide +kernel)

theorem terminal_data_03776 : FiniteChecks.Interval terminalTest 3776 3784 :=
  FiniteChecks.interval_of_check terminalTest 3776 8 (by decide +kernel)

theorem terminal_data_03784 : FiniteChecks.Interval terminalTest 3784 3792 :=
  FiniteChecks.interval_of_check terminalTest 3784 8 (by decide +kernel)

theorem terminal_data_03792 : FiniteChecks.Interval terminalTest 3792 3796 :=
  FiniteChecks.interval_of_check terminalTest 3792 4 (by decide +kernel)

theorem terminal_data_join_00008_00024 : FiniteChecks.Interval terminalTest 8 24 :=
  FiniteChecks.interval_append terminalTest 8 16 24 terminal_data_00008 terminal_data_00016

theorem terminal_data_join_00000_00024 : FiniteChecks.Interval terminalTest 0 24 :=
  FiniteChecks.interval_append terminalTest 0 8 24 terminal_data_00000 terminal_data_join_00008_00024

theorem terminal_data_join_00024_00040 : FiniteChecks.Interval terminalTest 24 40 :=
  FiniteChecks.interval_append terminalTest 24 32 40 terminal_data_00024 terminal_data_00032

theorem terminal_data_join_00040_00056 : FiniteChecks.Interval terminalTest 40 56 :=
  FiniteChecks.interval_append terminalTest 40 48 56 terminal_data_00040 terminal_data_00048

theorem terminal_data_join_00024_00056 : FiniteChecks.Interval terminalTest 24 56 :=
  FiniteChecks.interval_append terminalTest 24 40 56 terminal_data_join_00024_00040 terminal_data_join_00040_00056

theorem terminal_data_join_00000_00056 : FiniteChecks.Interval terminalTest 0 56 :=
  FiniteChecks.interval_append terminalTest 0 24 56 terminal_data_join_00000_00024 terminal_data_join_00024_00056

theorem terminal_data_join_00064_00080 : FiniteChecks.Interval terminalTest 64 80 :=
  FiniteChecks.interval_append terminalTest 64 72 80 terminal_data_00064 terminal_data_00072

theorem terminal_data_join_00056_00080 : FiniteChecks.Interval terminalTest 56 80 :=
  FiniteChecks.interval_append terminalTest 56 64 80 terminal_data_00056 terminal_data_join_00064_00080

theorem terminal_data_join_00080_00096 : FiniteChecks.Interval terminalTest 80 96 :=
  FiniteChecks.interval_append terminalTest 80 88 96 terminal_data_00080 terminal_data_00088

theorem terminal_data_join_00096_00112 : FiniteChecks.Interval terminalTest 96 112 :=
  FiniteChecks.interval_append terminalTest 96 104 112 terminal_data_00096 terminal_data_00104

theorem terminal_data_join_00080_00112 : FiniteChecks.Interval terminalTest 80 112 :=
  FiniteChecks.interval_append terminalTest 80 96 112 terminal_data_join_00080_00096 terminal_data_join_00096_00112

theorem terminal_data_join_00056_00112 : FiniteChecks.Interval terminalTest 56 112 :=
  FiniteChecks.interval_append terminalTest 56 80 112 terminal_data_join_00056_00080 terminal_data_join_00080_00112

theorem terminal_data_join_00000_00112 : FiniteChecks.Interval terminalTest 0 112 :=
  FiniteChecks.interval_append terminalTest 0 56 112 terminal_data_join_00000_00056 terminal_data_join_00056_00112

theorem terminal_data_join_00120_00136 : FiniteChecks.Interval terminalTest 120 136 :=
  FiniteChecks.interval_append terminalTest 120 128 136 terminal_data_00120 terminal_data_00128

theorem terminal_data_join_00112_00136 : FiniteChecks.Interval terminalTest 112 136 :=
  FiniteChecks.interval_append terminalTest 112 120 136 terminal_data_00112 terminal_data_join_00120_00136

theorem terminal_data_join_00136_00152 : FiniteChecks.Interval terminalTest 136 152 :=
  FiniteChecks.interval_append terminalTest 136 144 152 terminal_data_00136 terminal_data_00144

theorem terminal_data_join_00152_00168 : FiniteChecks.Interval terminalTest 152 168 :=
  FiniteChecks.interval_append terminalTest 152 160 168 terminal_data_00152 terminal_data_00160

theorem terminal_data_join_00136_00168 : FiniteChecks.Interval terminalTest 136 168 :=
  FiniteChecks.interval_append terminalTest 136 152 168 terminal_data_join_00136_00152 terminal_data_join_00152_00168

theorem terminal_data_join_00112_00168 : FiniteChecks.Interval terminalTest 112 168 :=
  FiniteChecks.interval_append terminalTest 112 136 168 terminal_data_join_00112_00136 terminal_data_join_00136_00168


end Papers.RationalityTen.ConcretePolygonClassification.N7
