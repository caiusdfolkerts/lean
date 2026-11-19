module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart015

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join_2 03272 03288 3272 3288 3280 03280
cert_terminal_data_join 03256 03288 3256 3288 3272 03272
cert_terminal_data_join_2 03288 03304 3288 3304 3296 03296
cert_terminal_data_join_2 03304 03320 3304 3320 3312 03312
cert_terminal_data_join 03288 03320 3288 3320 3304 03304
cert_terminal_data_join 03256 03320 3256 3320 3288 03288
cert_terminal_data_join 03200 03320 3200 3320 3256 03256
cert_terminal_data_join 03080 03320 3080 3320 3200 03200
cert_terminal_data_join 02848 03320 2848 3320 3080 03080
cert_terminal_data_join_2 03328 03344 3328 3344 3336 03336
cert_terminal_data_join_3 03320 03344 3320 3344 3328 03328
cert_terminal_data_join_2 03344 03360 3344 3360 3352 03352
cert_terminal_data_join_2 03360 03376 3360 3376 3368 03368
cert_terminal_data_join 03344 03376 3344 3376 3360 03360
cert_terminal_data_join 03320 03376 3320 3376 3344 03344
cert_terminal_data_join_2 03376 03392 3376 3392 3384 03384
cert_terminal_data_join_2 03392 03408 3392 3408 3400 03400
cert_terminal_data_join 03376 03408 3376 3408 3392 03392
cert_terminal_data_join_2 03408 03424 3408 3424 3416 03416
cert_terminal_data_join_2 03424 03440 3424 3440 3432 03432
cert_terminal_data_join 03408 03440 3408 3440 3424 03424
cert_terminal_data_join 03376 03440 3376 3440 3408 03408
cert_terminal_data_join 03320 03440 3320 3440 3376 03376
cert_terminal_data_join_2 03448 03464 3448 3464 3456 03456
cert_terminal_data_join_3 03440 03464 3440 3464 3448 03448
cert_terminal_data_join_2 03464 03480 3464 3480 3472 03472
cert_terminal_data_join_2 03480 03496 3480 3496 3488 03488
cert_terminal_data_join 03464 03496 3464 3496 3480 03480
cert_terminal_data_join 03440 03496 3440 3496 3464 03464
cert_terminal_data_join_2 03496 03512 3496 3512 3504 03504
cert_terminal_data_join_2 03512 03528 3512 3528 3520 03520
cert_terminal_data_join 03496 03528 3496 3528 3512 03512
cert_terminal_data_join_2 03528 03544 3528 3544 3536 03536
cert_terminal_data_join_2 03544 03560 3544 3560 3552 03552
cert_terminal_data_join 03528 03560 3528 3560 3544 03544
cert_terminal_data_join 03496 03560 3496 3560 3528 03528
cert_terminal_data_join 03440 03560 3440 3560 3496 03496
cert_terminal_data_join 03320 03560 3320 3560 3440 03440
cert_terminal_data_join_2 03568 03584 3568 3584 3576 03576
cert_terminal_data_join_3 03560 03584 3560 3584 3568 03568
cert_terminal_data_join_2 03584 03600 3584 3600 3592 03592
cert_terminal_data_join_2 03600 03616 3600 3616 3608 03608
cert_terminal_data_join 03584 03616 3584 3616 3600 03600
cert_terminal_data_join 03560 03616 3560 3616 3584 03584
cert_terminal_data_join_2 03616 03632 3616 3632 3624 03624
cert_terminal_data_join_2 03632 03648 3632 3648 3640 03640
cert_terminal_data_join 03616 03648 3616 3648 3632 03632
cert_terminal_data_join_2 03648 03664 3648 3664 3656 03656
cert_terminal_data_join_2 03664 03680 3664 3680 3672 03672
cert_terminal_data_join 03648 03680 3648 3680 3664 03664
cert_terminal_data_join 03616 03680 3616 3680 3648 03648
cert_terminal_data_join 03560 03680 3560 3680 3616 03616
cert_terminal_data_join_2 03688 03704 3688 3704 3696 03696
cert_terminal_data_join_3 03680 03704 3680 3704 3688 03688
cert_terminal_data_join_2 03704 03720 3704 3720 3712 03712
cert_terminal_data_join_2 03720 03736 3720 3736 3728 03728
cert_terminal_data_join 03704 03736 3704 3736 3720 03720
cert_terminal_data_join 03680 03736 3680 3736 3704 03704
cert_terminal_data_join_2 03736 03752 3736 3752 3744 03744
cert_terminal_data_join_2 03752 03768 3752 3768 3760 03760
cert_terminal_data_join 03736 03768 3736 3768 3752 03752
cert_terminal_data_join_2 03768 03784 3768 3784 3776 03776
cert_terminal_data_join_2 03784 03796 3784 3796 3792 03792
theorem terminal_data_join_03768_03796 : FiniteChecks.Interval terminalTest 3768 3796 :=
  FiniteChecks.interval_append terminalTest 3768 3784 3796 terminal_data_join_03768_03784 terminal_data_join_03784_03796


end Papers.RationalityTen.ConcretePolygonClassification.N7
