module

public import PolygonN7ClassificationPart015

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_03272_03288 : FiniteChecks.Interval terminalTest 3272 3288 :=
  FiniteChecks.interval_append terminalTest 3272 3280 3288 terminal_data_03272 terminal_data_03280

theorem terminal_data_join_03256_03288 : FiniteChecks.Interval terminalTest 3256 3288 :=
  FiniteChecks.interval_append terminalTest 3256 3272 3288 terminal_data_join_03256_03272 terminal_data_join_03272_03288

theorem terminal_data_join_03288_03304 : FiniteChecks.Interval terminalTest 3288 3304 :=
  FiniteChecks.interval_append terminalTest 3288 3296 3304 terminal_data_03288 terminal_data_03296

theorem terminal_data_join_03304_03320 : FiniteChecks.Interval terminalTest 3304 3320 :=
  FiniteChecks.interval_append terminalTest 3304 3312 3320 terminal_data_03304 terminal_data_03312

theorem terminal_data_join_03288_03320 : FiniteChecks.Interval terminalTest 3288 3320 :=
  FiniteChecks.interval_append terminalTest 3288 3304 3320 terminal_data_join_03288_03304 terminal_data_join_03304_03320

theorem terminal_data_join_03256_03320 : FiniteChecks.Interval terminalTest 3256 3320 :=
  FiniteChecks.interval_append terminalTest 3256 3288 3320 terminal_data_join_03256_03288 terminal_data_join_03288_03320

theorem terminal_data_join_03200_03320 : FiniteChecks.Interval terminalTest 3200 3320 :=
  FiniteChecks.interval_append terminalTest 3200 3256 3320 terminal_data_join_03200_03256 terminal_data_join_03256_03320

theorem terminal_data_join_03080_03320 : FiniteChecks.Interval terminalTest 3080 3320 :=
  FiniteChecks.interval_append terminalTest 3080 3200 3320 terminal_data_join_03080_03200 terminal_data_join_03200_03320

theorem terminal_data_join_02848_03320 : FiniteChecks.Interval terminalTest 2848 3320 :=
  FiniteChecks.interval_append terminalTest 2848 3080 3320 terminal_data_join_02848_03080 terminal_data_join_03080_03320

theorem terminal_data_join_03328_03344 : FiniteChecks.Interval terminalTest 3328 3344 :=
  FiniteChecks.interval_append terminalTest 3328 3336 3344 terminal_data_03328 terminal_data_03336

theorem terminal_data_join_03320_03344 : FiniteChecks.Interval terminalTest 3320 3344 :=
  FiniteChecks.interval_append terminalTest 3320 3328 3344 terminal_data_03320 terminal_data_join_03328_03344

theorem terminal_data_join_03344_03360 : FiniteChecks.Interval terminalTest 3344 3360 :=
  FiniteChecks.interval_append terminalTest 3344 3352 3360 terminal_data_03344 terminal_data_03352

theorem terminal_data_join_03360_03376 : FiniteChecks.Interval terminalTest 3360 3376 :=
  FiniteChecks.interval_append terminalTest 3360 3368 3376 terminal_data_03360 terminal_data_03368

theorem terminal_data_join_03344_03376 : FiniteChecks.Interval terminalTest 3344 3376 :=
  FiniteChecks.interval_append terminalTest 3344 3360 3376 terminal_data_join_03344_03360 terminal_data_join_03360_03376

theorem terminal_data_join_03320_03376 : FiniteChecks.Interval terminalTest 3320 3376 :=
  FiniteChecks.interval_append terminalTest 3320 3344 3376 terminal_data_join_03320_03344 terminal_data_join_03344_03376

theorem terminal_data_join_03376_03392 : FiniteChecks.Interval terminalTest 3376 3392 :=
  FiniteChecks.interval_append terminalTest 3376 3384 3392 terminal_data_03376 terminal_data_03384

theorem terminal_data_join_03392_03408 : FiniteChecks.Interval terminalTest 3392 3408 :=
  FiniteChecks.interval_append terminalTest 3392 3400 3408 terminal_data_03392 terminal_data_03400

theorem terminal_data_join_03376_03408 : FiniteChecks.Interval terminalTest 3376 3408 :=
  FiniteChecks.interval_append terminalTest 3376 3392 3408 terminal_data_join_03376_03392 terminal_data_join_03392_03408

theorem terminal_data_join_03408_03424 : FiniteChecks.Interval terminalTest 3408 3424 :=
  FiniteChecks.interval_append terminalTest 3408 3416 3424 terminal_data_03408 terminal_data_03416

theorem terminal_data_join_03424_03440 : FiniteChecks.Interval terminalTest 3424 3440 :=
  FiniteChecks.interval_append terminalTest 3424 3432 3440 terminal_data_03424 terminal_data_03432

theorem terminal_data_join_03408_03440 : FiniteChecks.Interval terminalTest 3408 3440 :=
  FiniteChecks.interval_append terminalTest 3408 3424 3440 terminal_data_join_03408_03424 terminal_data_join_03424_03440

theorem terminal_data_join_03376_03440 : FiniteChecks.Interval terminalTest 3376 3440 :=
  FiniteChecks.interval_append terminalTest 3376 3408 3440 terminal_data_join_03376_03408 terminal_data_join_03408_03440

theorem terminal_data_join_03320_03440 : FiniteChecks.Interval terminalTest 3320 3440 :=
  FiniteChecks.interval_append terminalTest 3320 3376 3440 terminal_data_join_03320_03376 terminal_data_join_03376_03440

theorem terminal_data_join_03448_03464 : FiniteChecks.Interval terminalTest 3448 3464 :=
  FiniteChecks.interval_append terminalTest 3448 3456 3464 terminal_data_03448 terminal_data_03456

theorem terminal_data_join_03440_03464 : FiniteChecks.Interval terminalTest 3440 3464 :=
  FiniteChecks.interval_append terminalTest 3440 3448 3464 terminal_data_03440 terminal_data_join_03448_03464

theorem terminal_data_join_03464_03480 : FiniteChecks.Interval terminalTest 3464 3480 :=
  FiniteChecks.interval_append terminalTest 3464 3472 3480 terminal_data_03464 terminal_data_03472

theorem terminal_data_join_03480_03496 : FiniteChecks.Interval terminalTest 3480 3496 :=
  FiniteChecks.interval_append terminalTest 3480 3488 3496 terminal_data_03480 terminal_data_03488

theorem terminal_data_join_03464_03496 : FiniteChecks.Interval terminalTest 3464 3496 :=
  FiniteChecks.interval_append terminalTest 3464 3480 3496 terminal_data_join_03464_03480 terminal_data_join_03480_03496

theorem terminal_data_join_03440_03496 : FiniteChecks.Interval terminalTest 3440 3496 :=
  FiniteChecks.interval_append terminalTest 3440 3464 3496 terminal_data_join_03440_03464 terminal_data_join_03464_03496

theorem terminal_data_join_03496_03512 : FiniteChecks.Interval terminalTest 3496 3512 :=
  FiniteChecks.interval_append terminalTest 3496 3504 3512 terminal_data_03496 terminal_data_03504

theorem terminal_data_join_03512_03528 : FiniteChecks.Interval terminalTest 3512 3528 :=
  FiniteChecks.interval_append terminalTest 3512 3520 3528 terminal_data_03512 terminal_data_03520

theorem terminal_data_join_03496_03528 : FiniteChecks.Interval terminalTest 3496 3528 :=
  FiniteChecks.interval_append terminalTest 3496 3512 3528 terminal_data_join_03496_03512 terminal_data_join_03512_03528

theorem terminal_data_join_03528_03544 : FiniteChecks.Interval terminalTest 3528 3544 :=
  FiniteChecks.interval_append terminalTest 3528 3536 3544 terminal_data_03528 terminal_data_03536

theorem terminal_data_join_03544_03560 : FiniteChecks.Interval terminalTest 3544 3560 :=
  FiniteChecks.interval_append terminalTest 3544 3552 3560 terminal_data_03544 terminal_data_03552

theorem terminal_data_join_03528_03560 : FiniteChecks.Interval terminalTest 3528 3560 :=
  FiniteChecks.interval_append terminalTest 3528 3544 3560 terminal_data_join_03528_03544 terminal_data_join_03544_03560

theorem terminal_data_join_03496_03560 : FiniteChecks.Interval terminalTest 3496 3560 :=
  FiniteChecks.interval_append terminalTest 3496 3528 3560 terminal_data_join_03496_03528 terminal_data_join_03528_03560

theorem terminal_data_join_03440_03560 : FiniteChecks.Interval terminalTest 3440 3560 :=
  FiniteChecks.interval_append terminalTest 3440 3496 3560 terminal_data_join_03440_03496 terminal_data_join_03496_03560

theorem terminal_data_join_03320_03560 : FiniteChecks.Interval terminalTest 3320 3560 :=
  FiniteChecks.interval_append terminalTest 3320 3440 3560 terminal_data_join_03320_03440 terminal_data_join_03440_03560

theorem terminal_data_join_03568_03584 : FiniteChecks.Interval terminalTest 3568 3584 :=
  FiniteChecks.interval_append terminalTest 3568 3576 3584 terminal_data_03568 terminal_data_03576

theorem terminal_data_join_03560_03584 : FiniteChecks.Interval terminalTest 3560 3584 :=
  FiniteChecks.interval_append terminalTest 3560 3568 3584 terminal_data_03560 terminal_data_join_03568_03584

theorem terminal_data_join_03584_03600 : FiniteChecks.Interval terminalTest 3584 3600 :=
  FiniteChecks.interval_append terminalTest 3584 3592 3600 terminal_data_03584 terminal_data_03592

theorem terminal_data_join_03600_03616 : FiniteChecks.Interval terminalTest 3600 3616 :=
  FiniteChecks.interval_append terminalTest 3600 3608 3616 terminal_data_03600 terminal_data_03608

theorem terminal_data_join_03584_03616 : FiniteChecks.Interval terminalTest 3584 3616 :=
  FiniteChecks.interval_append terminalTest 3584 3600 3616 terminal_data_join_03584_03600 terminal_data_join_03600_03616

theorem terminal_data_join_03560_03616 : FiniteChecks.Interval terminalTest 3560 3616 :=
  FiniteChecks.interval_append terminalTest 3560 3584 3616 terminal_data_join_03560_03584 terminal_data_join_03584_03616

theorem terminal_data_join_03616_03632 : FiniteChecks.Interval terminalTest 3616 3632 :=
  FiniteChecks.interval_append terminalTest 3616 3624 3632 terminal_data_03616 terminal_data_03624

theorem terminal_data_join_03632_03648 : FiniteChecks.Interval terminalTest 3632 3648 :=
  FiniteChecks.interval_append terminalTest 3632 3640 3648 terminal_data_03632 terminal_data_03640

theorem terminal_data_join_03616_03648 : FiniteChecks.Interval terminalTest 3616 3648 :=
  FiniteChecks.interval_append terminalTest 3616 3632 3648 terminal_data_join_03616_03632 terminal_data_join_03632_03648

theorem terminal_data_join_03648_03664 : FiniteChecks.Interval terminalTest 3648 3664 :=
  FiniteChecks.interval_append terminalTest 3648 3656 3664 terminal_data_03648 terminal_data_03656

theorem terminal_data_join_03664_03680 : FiniteChecks.Interval terminalTest 3664 3680 :=
  FiniteChecks.interval_append terminalTest 3664 3672 3680 terminal_data_03664 terminal_data_03672

theorem terminal_data_join_03648_03680 : FiniteChecks.Interval terminalTest 3648 3680 :=
  FiniteChecks.interval_append terminalTest 3648 3664 3680 terminal_data_join_03648_03664 terminal_data_join_03664_03680

theorem terminal_data_join_03616_03680 : FiniteChecks.Interval terminalTest 3616 3680 :=
  FiniteChecks.interval_append terminalTest 3616 3648 3680 terminal_data_join_03616_03648 terminal_data_join_03648_03680

theorem terminal_data_join_03560_03680 : FiniteChecks.Interval terminalTest 3560 3680 :=
  FiniteChecks.interval_append terminalTest 3560 3616 3680 terminal_data_join_03560_03616 terminal_data_join_03616_03680

theorem terminal_data_join_03688_03704 : FiniteChecks.Interval terminalTest 3688 3704 :=
  FiniteChecks.interval_append terminalTest 3688 3696 3704 terminal_data_03688 terminal_data_03696

theorem terminal_data_join_03680_03704 : FiniteChecks.Interval terminalTest 3680 3704 :=
  FiniteChecks.interval_append terminalTest 3680 3688 3704 terminal_data_03680 terminal_data_join_03688_03704

theorem terminal_data_join_03704_03720 : FiniteChecks.Interval terminalTest 3704 3720 :=
  FiniteChecks.interval_append terminalTest 3704 3712 3720 terminal_data_03704 terminal_data_03712

theorem terminal_data_join_03720_03736 : FiniteChecks.Interval terminalTest 3720 3736 :=
  FiniteChecks.interval_append terminalTest 3720 3728 3736 terminal_data_03720 terminal_data_03728

theorem terminal_data_join_03704_03736 : FiniteChecks.Interval terminalTest 3704 3736 :=
  FiniteChecks.interval_append terminalTest 3704 3720 3736 terminal_data_join_03704_03720 terminal_data_join_03720_03736

theorem terminal_data_join_03680_03736 : FiniteChecks.Interval terminalTest 3680 3736 :=
  FiniteChecks.interval_append terminalTest 3680 3704 3736 terminal_data_join_03680_03704 terminal_data_join_03704_03736

theorem terminal_data_join_03736_03752 : FiniteChecks.Interval terminalTest 3736 3752 :=
  FiniteChecks.interval_append terminalTest 3736 3744 3752 terminal_data_03736 terminal_data_03744

theorem terminal_data_join_03752_03768 : FiniteChecks.Interval terminalTest 3752 3768 :=
  FiniteChecks.interval_append terminalTest 3752 3760 3768 terminal_data_03752 terminal_data_03760

theorem terminal_data_join_03736_03768 : FiniteChecks.Interval terminalTest 3736 3768 :=
  FiniteChecks.interval_append terminalTest 3736 3752 3768 terminal_data_join_03736_03752 terminal_data_join_03752_03768

theorem terminal_data_join_03768_03784 : FiniteChecks.Interval terminalTest 3768 3784 :=
  FiniteChecks.interval_append terminalTest 3768 3776 3784 terminal_data_03768 terminal_data_03776

theorem terminal_data_join_03784_03796 : FiniteChecks.Interval terminalTest 3784 3796 :=
  FiniteChecks.interval_append terminalTest 3784 3792 3796 terminal_data_03784 terminal_data_03792

theorem terminal_data_join_03768_03796 : FiniteChecks.Interval terminalTest 3768 3796 :=
  FiniteChecks.interval_append terminalTest 3768 3784 3796 terminal_data_join_03768_03784 terminal_data_join_03784_03796


end Papers.RationalityTen.ConcretePolygonClassification.N7
