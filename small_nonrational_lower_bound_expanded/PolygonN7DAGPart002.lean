module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_nodes_part 002 00512 512 520 8
cert_nodes_part 002 00520 520 528 8
cert_nodes_part 002 00528 528 536 8
cert_nodes_part 002 00536 536 544 8
cert_nodes_part 002 00544 544 552 8
cert_nodes_part 002 00552 552 560 8
cert_nodes_part 002 00560 560 568 8
cert_nodes_part 002 00568 568 576 8
cert_nodes_part 002 00576 576 584 8
cert_nodes_part 002 00584 584 592 8
cert_nodes_part 002 00592 592 600 8
cert_nodes_part 002 00600 600 608 8
cert_nodes_part 002 00608 608 616 8
cert_nodes_part 002 00616 616 624 8
cert_nodes_part 002 00624 624 632 8
cert_nodes_part 002 00632 632 640 8
cert_nodes_part 002 00640 640 648 8
cert_nodes_part 002 00648 648 656 8
cert_nodes_part 002 00656 656 664 8
cert_nodes_part 002 00664 664 672 8
cert_nodes_part 002 00672 672 680 8
cert_nodes_part 002 00680 680 688 8
cert_nodes_part 002 00688 688 696 8
cert_nodes_part 002 00696 696 704 8
cert_nodes_part 002 00704 704 712 8
cert_nodes_part 002 00712 712 720 8
cert_nodes_part 002 00720 720 728 8
cert_nodes_part 002 00728 728 736 8
cert_nodes_part 002 00736 736 744 8
cert_nodes_part 002 00744 744 752 8
cert_nodes_part 002 00752 752 760 8
cert_nodes_part 002 00760 760 768 8
cert_nodes_part_join_2 002 00512 00528 512 528 520 00520
cert_nodes_part_join_2 002 00528 00544 528 544 536 00536
cert_nodes_part_join 002 00512 00544 512 544 528 00528
cert_nodes_part_join_2 002 00544 00560 544 560 552 00552
cert_nodes_part_join_2 002 00560 00576 560 576 568 00568
cert_nodes_part_join 002 00544 00576 544 576 560 00560
cert_nodes_part_join 002 00512 00576 512 576 544 00544
cert_nodes_part_join_2 002 00576 00592 576 592 584 00584
cert_nodes_part_join_2 002 00592 00608 592 608 600 00600
cert_nodes_part_join 002 00576 00608 576 608 592 00592
cert_nodes_part_join_2 002 00608 00624 608 624 616 00616
cert_nodes_part_join_2 002 00624 00640 624 640 632 00632
cert_nodes_part_join 002 00608 00640 608 640 624 00624
cert_nodes_part_join 002 00576 00640 576 640 608 00608
cert_nodes_part_join 002 00512 00640 512 640 576 00576
cert_nodes_part_join_2 002 00640 00656 640 656 648 00648
cert_nodes_part_join_2 002 00656 00672 656 672 664 00664
cert_nodes_part_join 002 00640 00672 640 672 656 00656
cert_nodes_part_join_2 002 00672 00688 672 688 680 00680
cert_nodes_part_join_2 002 00688 00704 688 704 696 00696
cert_nodes_part_join 002 00672 00704 672 704 688 00688
cert_nodes_part_join 002 00640 00704 640 704 672 00672
cert_nodes_part_join_2 002 00704 00720 704 720 712 00712
cert_nodes_part_join_2 002 00720 00736 720 736 728 00728
cert_nodes_part_join 002 00704 00736 704 736 720 00720
cert_nodes_part_join_2 002 00736 00752 736 752 744 00744
cert_nodes_part_join_2 002 00752 00768 752 768 760 00760
cert_nodes_part_join 002 00736 00768 736 768 752 00752
cert_nodes_part_join 002 00704 00768 704 768 736 00736
cert_nodes_part_join 002 00640 00768 640 768 704 00704
cert_nodes_part_join 002 00512 00768 512 768 640 00640
end Papers.RationalityTen.PolygonGrowth.N7
