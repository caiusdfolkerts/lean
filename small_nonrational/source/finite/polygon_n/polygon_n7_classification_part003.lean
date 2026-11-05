module

public import PolygonN7ClassificationPart002

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_00368 : FiniteChecks.Interval terminalTest 368 376 :=
  FiniteChecks.interval_of_check terminalTest 368 8 (by decide +kernel)

theorem terminal_data_00376 : FiniteChecks.Interval terminalTest 376 384 :=
  FiniteChecks.interval_of_check terminalTest 376 8 (by decide +kernel)

theorem terminal_data_00384 : FiniteChecks.Interval terminalTest 384 392 :=
  FiniteChecks.interval_of_check terminalTest 384 8 (by decide +kernel)

theorem terminal_data_00392 : FiniteChecks.Interval terminalTest 392 400 :=
  FiniteChecks.interval_of_check terminalTest 392 8 (by decide +kernel)

theorem terminal_data_00400 : FiniteChecks.Interval terminalTest 400 408 :=
  FiniteChecks.interval_of_check terminalTest 400 8 (by decide +kernel)

theorem terminal_data_00408 : FiniteChecks.Interval terminalTest 408 416 :=
  FiniteChecks.interval_of_check terminalTest 408 8 (by decide +kernel)

theorem terminal_data_00416 : FiniteChecks.Interval terminalTest 416 424 :=
  FiniteChecks.interval_of_check terminalTest 416 8 (by decide +kernel)

theorem terminal_data_00424 : FiniteChecks.Interval terminalTest 424 432 :=
  FiniteChecks.interval_of_check terminalTest 424 8 (by decide +kernel)

theorem terminal_data_00432 : FiniteChecks.Interval terminalTest 432 440 :=
  FiniteChecks.interval_of_check terminalTest 432 8 (by decide +kernel)

theorem terminal_data_00440 : FiniteChecks.Interval terminalTest 440 448 :=
  FiniteChecks.interval_of_check terminalTest 440 8 (by decide +kernel)

theorem terminal_data_00448 : FiniteChecks.Interval terminalTest 448 456 :=
  FiniteChecks.interval_of_check terminalTest 448 8 (by decide +kernel)

theorem terminal_data_00456 : FiniteChecks.Interval terminalTest 456 464 :=
  FiniteChecks.interval_of_check terminalTest 456 8 (by decide +kernel)

theorem terminal_data_00464 : FiniteChecks.Interval terminalTest 464 472 :=
  FiniteChecks.interval_of_check terminalTest 464 8 (by decide +kernel)

theorem terminal_data_00472 : FiniteChecks.Interval terminalTest 472 480 :=
  FiniteChecks.interval_of_check terminalTest 472 8 (by decide +kernel)

theorem terminal_data_00480 : FiniteChecks.Interval terminalTest 480 488 :=
  FiniteChecks.interval_of_check terminalTest 480 8 (by decide +kernel)

theorem terminal_data_00488 : FiniteChecks.Interval terminalTest 488 496 :=
  FiniteChecks.interval_of_check terminalTest 488 8 (by decide +kernel)

theorem terminal_data_00496 : FiniteChecks.Interval terminalTest 496 504 :=
  FiniteChecks.interval_of_check terminalTest 496 8 (by decide +kernel)

theorem terminal_data_00504 : FiniteChecks.Interval terminalTest 504 512 :=
  FiniteChecks.interval_of_check terminalTest 504 8 (by decide +kernel)

theorem terminal_data_00512 : FiniteChecks.Interval terminalTest 512 520 :=
  FiniteChecks.interval_of_check terminalTest 512 8 (by decide +kernel)

theorem terminal_data_00520 : FiniteChecks.Interval terminalTest 520 528 :=
  FiniteChecks.interval_of_check terminalTest 520 8 (by decide +kernel)

theorem terminal_data_00528 : FiniteChecks.Interval terminalTest 528 536 :=
  FiniteChecks.interval_of_check terminalTest 528 8 (by decide +kernel)

theorem terminal_data_00536 : FiniteChecks.Interval terminalTest 536 544 :=
  FiniteChecks.interval_of_check terminalTest 536 8 (by decide +kernel)

theorem terminal_data_00544 : FiniteChecks.Interval terminalTest 544 552 :=
  FiniteChecks.interval_of_check terminalTest 544 8 (by decide +kernel)

theorem terminal_data_00552 : FiniteChecks.Interval terminalTest 552 560 :=
  FiniteChecks.interval_of_check terminalTest 552 8 (by decide +kernel)

theorem terminal_data_00560 : FiniteChecks.Interval terminalTest 560 568 :=
  FiniteChecks.interval_of_check terminalTest 560 8 (by decide +kernel)

theorem terminal_data_00568 : FiniteChecks.Interval terminalTest 568 576 :=
  FiniteChecks.interval_of_check terminalTest 568 8 (by decide +kernel)

theorem terminal_data_00576 : FiniteChecks.Interval terminalTest 576 584 :=
  FiniteChecks.interval_of_check terminalTest 576 8 (by decide +kernel)

theorem terminal_data_00584 : FiniteChecks.Interval terminalTest 584 592 :=
  FiniteChecks.interval_of_check terminalTest 584 8 (by decide +kernel)

theorem terminal_data_00592 : FiniteChecks.Interval terminalTest 592 600 :=
  FiniteChecks.interval_of_check terminalTest 592 8 (by decide +kernel)

theorem terminal_data_00600 : FiniteChecks.Interval terminalTest 600 608 :=
  FiniteChecks.interval_of_check terminalTest 600 8 (by decide +kernel)

theorem terminal_data_00608 : FiniteChecks.Interval terminalTest 608 616 :=
  FiniteChecks.interval_of_check terminalTest 608 8 (by decide +kernel)

theorem terminal_data_00616 : FiniteChecks.Interval terminalTest 616 624 :=
  FiniteChecks.interval_of_check terminalTest 616 8 (by decide +kernel)

theorem terminal_data_00624 : FiniteChecks.Interval terminalTest 624 632 :=
  FiniteChecks.interval_of_check terminalTest 624 8 (by decide +kernel)

theorem terminal_data_00632 : FiniteChecks.Interval terminalTest 632 640 :=
  FiniteChecks.interval_of_check terminalTest 632 8 (by decide +kernel)

theorem terminal_data_00640 : FiniteChecks.Interval terminalTest 640 648 :=
  FiniteChecks.interval_of_check terminalTest 640 8 (by decide +kernel)

theorem terminal_data_00648 : FiniteChecks.Interval terminalTest 648 656 :=
  FiniteChecks.interval_of_check terminalTest 648 8 (by decide +kernel)

theorem terminal_data_00656 : FiniteChecks.Interval terminalTest 656 664 :=
  FiniteChecks.interval_of_check terminalTest 656 8 (by decide +kernel)

theorem terminal_data_00664 : FiniteChecks.Interval terminalTest 664 672 :=
  FiniteChecks.interval_of_check terminalTest 664 8 (by decide +kernel)

theorem terminal_data_00672 : FiniteChecks.Interval terminalTest 672 680 :=
  FiniteChecks.interval_of_check terminalTest 672 8 (by decide +kernel)

theorem terminal_data_00680 : FiniteChecks.Interval terminalTest 680 688 :=
  FiniteChecks.interval_of_check terminalTest 680 8 (by decide +kernel)

theorem terminal_data_00688 : FiniteChecks.Interval terminalTest 688 696 :=
  FiniteChecks.interval_of_check terminalTest 688 8 (by decide +kernel)

theorem terminal_data_00696 : FiniteChecks.Interval terminalTest 696 704 :=
  FiniteChecks.interval_of_check terminalTest 696 8 (by decide +kernel)

theorem terminal_data_00704 : FiniteChecks.Interval terminalTest 704 712 :=
  FiniteChecks.interval_of_check terminalTest 704 8 (by decide +kernel)

theorem terminal_data_00712 : FiniteChecks.Interval terminalTest 712 720 :=
  FiniteChecks.interval_of_check terminalTest 712 8 (by decide +kernel)

theorem terminal_data_00720 : FiniteChecks.Interval terminalTest 720 728 :=
  FiniteChecks.interval_of_check terminalTest 720 8 (by decide +kernel)

theorem terminal_data_00728 : FiniteChecks.Interval terminalTest 728 736 :=
  FiniteChecks.interval_of_check terminalTest 728 8 (by decide +kernel)

theorem terminal_data_00736 : FiniteChecks.Interval terminalTest 736 744 :=
  FiniteChecks.interval_of_check terminalTest 736 8 (by decide +kernel)

theorem terminal_data_00744 : FiniteChecks.Interval terminalTest 744 752 :=
  FiniteChecks.interval_of_check terminalTest 744 8 (by decide +kernel)

theorem terminal_data_00752 : FiniteChecks.Interval terminalTest 752 760 :=
  FiniteChecks.interval_of_check terminalTest 752 8 (by decide +kernel)

theorem terminal_data_00760 : FiniteChecks.Interval terminalTest 760 768 :=
  FiniteChecks.interval_of_check terminalTest 760 8 (by decide +kernel)

theorem terminal_data_00768 : FiniteChecks.Interval terminalTest 768 776 :=
  FiniteChecks.interval_of_check terminalTest 768 8 (by decide +kernel)

theorem terminal_data_00776 : FiniteChecks.Interval terminalTest 776 784 :=
  FiniteChecks.interval_of_check terminalTest 776 8 (by decide +kernel)

theorem terminal_data_00784 : FiniteChecks.Interval terminalTest 784 792 :=
  FiniteChecks.interval_of_check terminalTest 784 8 (by decide +kernel)

theorem terminal_data_00792 : FiniteChecks.Interval terminalTest 792 800 :=
  FiniteChecks.interval_of_check terminalTest 792 8 (by decide +kernel)

theorem terminal_data_00800 : FiniteChecks.Interval terminalTest 800 808 :=
  FiniteChecks.interval_of_check terminalTest 800 8 (by decide +kernel)

theorem terminal_data_00808 : FiniteChecks.Interval terminalTest 808 816 :=
  FiniteChecks.interval_of_check terminalTest 808 8 (by decide +kernel)

theorem terminal_data_00816 : FiniteChecks.Interval terminalTest 816 824 :=
  FiniteChecks.interval_of_check terminalTest 816 8 (by decide +kernel)

theorem terminal_data_00824 : FiniteChecks.Interval terminalTest 824 832 :=
  FiniteChecks.interval_of_check terminalTest 824 8 (by decide +kernel)

theorem terminal_data_00832 : FiniteChecks.Interval terminalTest 832 840 :=
  FiniteChecks.interval_of_check terminalTest 832 8 (by decide +kernel)

theorem terminal_data_00840 : FiniteChecks.Interval terminalTest 840 848 :=
  FiniteChecks.interval_of_check terminalTest 840 8 (by decide +kernel)

theorem terminal_data_00848 : FiniteChecks.Interval terminalTest 848 856 :=
  FiniteChecks.interval_of_check terminalTest 848 8 (by decide +kernel)

theorem terminal_data_00856 : FiniteChecks.Interval terminalTest 856 864 :=
  FiniteChecks.interval_of_check terminalTest 856 8 (by decide +kernel)

theorem terminal_data_00864 : FiniteChecks.Interval terminalTest 864 872 :=
  FiniteChecks.interval_of_check terminalTest 864 8 (by decide +kernel)

theorem terminal_data_00872 : FiniteChecks.Interval terminalTest 872 880 :=
  FiniteChecks.interval_of_check terminalTest 872 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
