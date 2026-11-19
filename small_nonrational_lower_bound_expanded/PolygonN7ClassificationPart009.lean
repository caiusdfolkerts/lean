module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart008

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 03440 3440 3448 8
cert_terminal_data 03448 3448 3456 8
cert_terminal_data 03456 3456 3464 8
cert_terminal_data 03464 3464 3472 8
cert_terminal_data 03472 3472 3480 8
cert_terminal_data 03480 3480 3488 8
cert_terminal_data 03488 3488 3496 8
cert_terminal_data 03496 3496 3504 8
cert_terminal_data 03504 3504 3512 8
cert_terminal_data 03512 3512 3520 8
cert_terminal_data 03520 3520 3528 8
cert_terminal_data 03528 3528 3536 8
cert_terminal_data 03536 3536 3544 8
cert_terminal_data 03544 3544 3552 8
cert_terminal_data 03552 3552 3560 8
cert_terminal_data 03560 3560 3568 8
cert_terminal_data 03568 3568 3576 8
cert_terminal_data 03576 3576 3584 8
cert_terminal_data 03584 3584 3592 8
cert_terminal_data 03592 3592 3600 8
cert_terminal_data 03600 3600 3608 8
cert_terminal_data 03608 3608 3616 8
cert_terminal_data 03616 3616 3624 8
cert_terminal_data 03624 3624 3632 8
cert_terminal_data 03632 3632 3640 8
cert_terminal_data 03640 3640 3648 8
cert_terminal_data 03648 3648 3656 8
cert_terminal_data 03656 3656 3664 8
cert_terminal_data 03664 3664 3672 8
cert_terminal_data 03672 3672 3680 8
cert_terminal_data 03680 3680 3688 8
cert_terminal_data 03688 3688 3696 8
cert_terminal_data 03696 3696 3704 8
cert_terminal_data 03704 3704 3712 8
cert_terminal_data 03712 3712 3720 8
cert_terminal_data 03720 3720 3728 8
cert_terminal_data 03728 3728 3736 8
cert_terminal_data 03736 3736 3744 8
cert_terminal_data 03744 3744 3752 8
cert_terminal_data 03752 3752 3760 8
cert_terminal_data 03760 3760 3768 8
cert_terminal_data 03768 3768 3776 8
cert_terminal_data 03776 3776 3784 8
cert_terminal_data 03784 3784 3792 8
cert_terminal_data 03792 3792 3796 4
cert_terminal_data_join_2 00008 00024 8 24 16 00016
cert_terminal_data_join_3 00000 00024 0 24 8 00008
cert_terminal_data_join_2 00024 00040 24 40 32 00032
cert_terminal_data_join_2 00040 00056 40 56 48 00048
cert_terminal_data_join 00024 00056 24 56 40 00040
cert_terminal_data_join 00000 00056 0 56 24 00024
cert_terminal_data_join_2 00064 00080 64 80 72 00072
cert_terminal_data_join_3 00056 00080 56 80 64 00064
cert_terminal_data_join_2 00080 00096 80 96 88 00088
cert_terminal_data_join_2 00096 00112 96 112 104 00104
cert_terminal_data_join 00080 00112 80 112 96 00096
cert_terminal_data_join 00056 00112 56 112 80 00080
cert_terminal_data_join 00000 00112 0 112 56 00056
cert_terminal_data_join_2 00120 00136 120 136 128 00128
cert_terminal_data_join_3 00112 00136 112 136 120 00120
cert_terminal_data_join_2 00136 00152 136 152 144 00144
cert_terminal_data_join_2 00152 00168 152 168 160 00160
cert_terminal_data_join 00136 00168 136 168 152 00152
theorem terminal_data_join_00112_00168 : FiniteChecks.Interval terminalTest 112 168 :=
  FiniteChecks.interval_append terminalTest 112 136 168 terminal_data_join_00112_00136 terminal_data_join_00136_00168


end Papers.RationalityTen.ConcretePolygonClassification.N7
