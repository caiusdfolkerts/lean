module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart002

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 00368 368 376 8
cert_terminal_data 00376 376 384 8
cert_terminal_data 00384 384 392 8
cert_terminal_data 00392 392 400 8
cert_terminal_data 00400 400 408 8
cert_terminal_data 00408 408 416 8
cert_terminal_data 00416 416 424 8
cert_terminal_data 00424 424 432 8
cert_terminal_data 00432 432 440 8
cert_terminal_data 00440 440 448 8
cert_terminal_data 00448 448 456 8
cert_terminal_data 00456 456 464 8
cert_terminal_data 00464 464 472 8
cert_terminal_data 00472 472 480 8
cert_terminal_data 00480 480 488 8
cert_terminal_data 00488 488 496 8
cert_terminal_data 00496 496 504 8
cert_terminal_data 00504 504 512 8
cert_terminal_data 00512 512 520 8
cert_terminal_data 00520 520 528 8
cert_terminal_data 00528 528 536 8
cert_terminal_data 00536 536 544 8
cert_terminal_data 00544 544 552 8
cert_terminal_data 00552 552 560 8
cert_terminal_data 00560 560 568 8
cert_terminal_data 00568 568 576 8
cert_terminal_data 00576 576 584 8
cert_terminal_data 00584 584 592 8
cert_terminal_data 00592 592 600 8
cert_terminal_data 00600 600 608 8
cert_terminal_data 00608 608 616 8
cert_terminal_data 00616 616 624 8
cert_terminal_data 00624 624 632 8
cert_terminal_data 00632 632 640 8
cert_terminal_data 00640 640 648 8
cert_terminal_data 00648 648 656 8
cert_terminal_data 00656 656 664 8
cert_terminal_data 00664 664 672 8
cert_terminal_data 00672 672 680 8
cert_terminal_data 00680 680 688 8
cert_terminal_data 00688 688 696 8
cert_terminal_data 00696 696 704 8
cert_terminal_data 00704 704 712 8
cert_terminal_data 00712 712 720 8
cert_terminal_data 00720 720 728 8
cert_terminal_data 00728 728 736 8
cert_terminal_data 00736 736 744 8
cert_terminal_data 00744 744 752 8
cert_terminal_data 00752 752 760 8
cert_terminal_data 00760 760 768 8
cert_terminal_data 00768 768 776 8
cert_terminal_data 00776 776 784 8
cert_terminal_data 00784 784 792 8
cert_terminal_data 00792 792 800 8
cert_terminal_data 00800 800 808 8
cert_terminal_data 00808 808 816 8
cert_terminal_data 00816 816 824 8
cert_terminal_data 00824 824 832 8
cert_terminal_data 00832 832 840 8
cert_terminal_data 00840 840 848 8
cert_terminal_data 00848 848 856 8
cert_terminal_data 00856 856 864 8
cert_terminal_data 00864 864 872 8
theorem terminal_data_00872 : FiniteChecks.Interval terminalTest 872 880 :=
  FiniteChecks.interval_of_check terminalTest 872 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
