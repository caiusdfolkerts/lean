module
prelude
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

theorem nodes_part002_00512 : FiniteChecks.Interval nodeTest 512 520 :=
  FiniteChecks.interval_of_check nodeTest 512 8 (by decide +kernel)

theorem nodes_part002_00520 : FiniteChecks.Interval nodeTest 520 528 :=
  FiniteChecks.interval_of_check nodeTest 520 8 (by decide +kernel)

theorem nodes_part002_00528 : FiniteChecks.Interval nodeTest 528 536 :=
  FiniteChecks.interval_of_check nodeTest 528 8 (by decide +kernel)

theorem nodes_part002_00536 : FiniteChecks.Interval nodeTest 536 544 :=
  FiniteChecks.interval_of_check nodeTest 536 8 (by decide +kernel)

theorem nodes_part002_00544 : FiniteChecks.Interval nodeTest 544 552 :=
  FiniteChecks.interval_of_check nodeTest 544 8 (by decide +kernel)

theorem nodes_part002_00552 : FiniteChecks.Interval nodeTest 552 560 :=
  FiniteChecks.interval_of_check nodeTest 552 8 (by decide +kernel)

theorem nodes_part002_00560 : FiniteChecks.Interval nodeTest 560 568 :=
  FiniteChecks.interval_of_check nodeTest 560 8 (by decide +kernel)

theorem nodes_part002_00568 : FiniteChecks.Interval nodeTest 568 576 :=
  FiniteChecks.interval_of_check nodeTest 568 8 (by decide +kernel)

theorem nodes_part002_00576 : FiniteChecks.Interval nodeTest 576 584 :=
  FiniteChecks.interval_of_check nodeTest 576 8 (by decide +kernel)

theorem nodes_part002_00584 : FiniteChecks.Interval nodeTest 584 592 :=
  FiniteChecks.interval_of_check nodeTest 584 8 (by decide +kernel)

theorem nodes_part002_00592 : FiniteChecks.Interval nodeTest 592 600 :=
  FiniteChecks.interval_of_check nodeTest 592 8 (by decide +kernel)

theorem nodes_part002_00600 : FiniteChecks.Interval nodeTest 600 608 :=
  FiniteChecks.interval_of_check nodeTest 600 8 (by decide +kernel)

theorem nodes_part002_00608 : FiniteChecks.Interval nodeTest 608 616 :=
  FiniteChecks.interval_of_check nodeTest 608 8 (by decide +kernel)

theorem nodes_part002_00616 : FiniteChecks.Interval nodeTest 616 624 :=
  FiniteChecks.interval_of_check nodeTest 616 8 (by decide +kernel)

theorem nodes_part002_00624 : FiniteChecks.Interval nodeTest 624 632 :=
  FiniteChecks.interval_of_check nodeTest 624 8 (by decide +kernel)

theorem nodes_part002_00632 : FiniteChecks.Interval nodeTest 632 640 :=
  FiniteChecks.interval_of_check nodeTest 632 8 (by decide +kernel)

theorem nodes_part002_00640 : FiniteChecks.Interval nodeTest 640 648 :=
  FiniteChecks.interval_of_check nodeTest 640 8 (by decide +kernel)

theorem nodes_part002_00648 : FiniteChecks.Interval nodeTest 648 656 :=
  FiniteChecks.interval_of_check nodeTest 648 8 (by decide +kernel)

theorem nodes_part002_00656 : FiniteChecks.Interval nodeTest 656 664 :=
  FiniteChecks.interval_of_check nodeTest 656 8 (by decide +kernel)

theorem nodes_part002_00664 : FiniteChecks.Interval nodeTest 664 672 :=
  FiniteChecks.interval_of_check nodeTest 664 8 (by decide +kernel)

theorem nodes_part002_00672 : FiniteChecks.Interval nodeTest 672 680 :=
  FiniteChecks.interval_of_check nodeTest 672 8 (by decide +kernel)

theorem nodes_part002_00680 : FiniteChecks.Interval nodeTest 680 688 :=
  FiniteChecks.interval_of_check nodeTest 680 8 (by decide +kernel)

theorem nodes_part002_00688 : FiniteChecks.Interval nodeTest 688 696 :=
  FiniteChecks.interval_of_check nodeTest 688 8 (by decide +kernel)

theorem nodes_part002_00696 : FiniteChecks.Interval nodeTest 696 704 :=
  FiniteChecks.interval_of_check nodeTest 696 8 (by decide +kernel)

theorem nodes_part002_00704 : FiniteChecks.Interval nodeTest 704 712 :=
  FiniteChecks.interval_of_check nodeTest 704 8 (by decide +kernel)

theorem nodes_part002_00712 : FiniteChecks.Interval nodeTest 712 720 :=
  FiniteChecks.interval_of_check nodeTest 712 8 (by decide +kernel)

theorem nodes_part002_00720 : FiniteChecks.Interval nodeTest 720 728 :=
  FiniteChecks.interval_of_check nodeTest 720 8 (by decide +kernel)

theorem nodes_part002_00728 : FiniteChecks.Interval nodeTest 728 736 :=
  FiniteChecks.interval_of_check nodeTest 728 8 (by decide +kernel)

theorem nodes_part002_00736 : FiniteChecks.Interval nodeTest 736 744 :=
  FiniteChecks.interval_of_check nodeTest 736 8 (by decide +kernel)

theorem nodes_part002_00744 : FiniteChecks.Interval nodeTest 744 752 :=
  FiniteChecks.interval_of_check nodeTest 744 8 (by decide +kernel)

theorem nodes_part002_00752 : FiniteChecks.Interval nodeTest 752 760 :=
  FiniteChecks.interval_of_check nodeTest 752 8 (by decide +kernel)

theorem nodes_part002_00760 : FiniteChecks.Interval nodeTest 760 768 :=
  FiniteChecks.interval_of_check nodeTest 760 8 (by decide +kernel)

theorem nodes_part002_join_00512_00528 : FiniteChecks.Interval nodeTest 512 528 :=
  FiniteChecks.interval_append nodeTest 512 520 528 nodes_part002_00512 nodes_part002_00520

theorem nodes_part002_join_00528_00544 : FiniteChecks.Interval nodeTest 528 544 :=
  FiniteChecks.interval_append nodeTest 528 536 544 nodes_part002_00528 nodes_part002_00536

theorem nodes_part002_join_00512_00544 : FiniteChecks.Interval nodeTest 512 544 :=
  FiniteChecks.interval_append nodeTest 512 528 544 nodes_part002_join_00512_00528 nodes_part002_join_00528_00544

theorem nodes_part002_join_00544_00560 : FiniteChecks.Interval nodeTest 544 560 :=
  FiniteChecks.interval_append nodeTest 544 552 560 nodes_part002_00544 nodes_part002_00552

theorem nodes_part002_join_00560_00576 : FiniteChecks.Interval nodeTest 560 576 :=
  FiniteChecks.interval_append nodeTest 560 568 576 nodes_part002_00560 nodes_part002_00568

theorem nodes_part002_join_00544_00576 : FiniteChecks.Interval nodeTest 544 576 :=
  FiniteChecks.interval_append nodeTest 544 560 576 nodes_part002_join_00544_00560 nodes_part002_join_00560_00576

theorem nodes_part002_join_00512_00576 : FiniteChecks.Interval nodeTest 512 576 :=
  FiniteChecks.interval_append nodeTest 512 544 576 nodes_part002_join_00512_00544 nodes_part002_join_00544_00576

theorem nodes_part002_join_00576_00592 : FiniteChecks.Interval nodeTest 576 592 :=
  FiniteChecks.interval_append nodeTest 576 584 592 nodes_part002_00576 nodes_part002_00584

theorem nodes_part002_join_00592_00608 : FiniteChecks.Interval nodeTest 592 608 :=
  FiniteChecks.interval_append nodeTest 592 600 608 nodes_part002_00592 nodes_part002_00600

theorem nodes_part002_join_00576_00608 : FiniteChecks.Interval nodeTest 576 608 :=
  FiniteChecks.interval_append nodeTest 576 592 608 nodes_part002_join_00576_00592 nodes_part002_join_00592_00608

theorem nodes_part002_join_00608_00624 : FiniteChecks.Interval nodeTest 608 624 :=
  FiniteChecks.interval_append nodeTest 608 616 624 nodes_part002_00608 nodes_part002_00616

theorem nodes_part002_join_00624_00640 : FiniteChecks.Interval nodeTest 624 640 :=
  FiniteChecks.interval_append nodeTest 624 632 640 nodes_part002_00624 nodes_part002_00632

theorem nodes_part002_join_00608_00640 : FiniteChecks.Interval nodeTest 608 640 :=
  FiniteChecks.interval_append nodeTest 608 624 640 nodes_part002_join_00608_00624 nodes_part002_join_00624_00640

theorem nodes_part002_join_00576_00640 : FiniteChecks.Interval nodeTest 576 640 :=
  FiniteChecks.interval_append nodeTest 576 608 640 nodes_part002_join_00576_00608 nodes_part002_join_00608_00640

theorem nodes_part002_join_00512_00640 : FiniteChecks.Interval nodeTest 512 640 :=
  FiniteChecks.interval_append nodeTest 512 576 640 nodes_part002_join_00512_00576 nodes_part002_join_00576_00640

theorem nodes_part002_join_00640_00656 : FiniteChecks.Interval nodeTest 640 656 :=
  FiniteChecks.interval_append nodeTest 640 648 656 nodes_part002_00640 nodes_part002_00648

theorem nodes_part002_join_00656_00672 : FiniteChecks.Interval nodeTest 656 672 :=
  FiniteChecks.interval_append nodeTest 656 664 672 nodes_part002_00656 nodes_part002_00664

theorem nodes_part002_join_00640_00672 : FiniteChecks.Interval nodeTest 640 672 :=
  FiniteChecks.interval_append nodeTest 640 656 672 nodes_part002_join_00640_00656 nodes_part002_join_00656_00672

theorem nodes_part002_join_00672_00688 : FiniteChecks.Interval nodeTest 672 688 :=
  FiniteChecks.interval_append nodeTest 672 680 688 nodes_part002_00672 nodes_part002_00680

theorem nodes_part002_join_00688_00704 : FiniteChecks.Interval nodeTest 688 704 :=
  FiniteChecks.interval_append nodeTest 688 696 704 nodes_part002_00688 nodes_part002_00696

theorem nodes_part002_join_00672_00704 : FiniteChecks.Interval nodeTest 672 704 :=
  FiniteChecks.interval_append nodeTest 672 688 704 nodes_part002_join_00672_00688 nodes_part002_join_00688_00704

theorem nodes_part002_join_00640_00704 : FiniteChecks.Interval nodeTest 640 704 :=
  FiniteChecks.interval_append nodeTest 640 672 704 nodes_part002_join_00640_00672 nodes_part002_join_00672_00704

theorem nodes_part002_join_00704_00720 : FiniteChecks.Interval nodeTest 704 720 :=
  FiniteChecks.interval_append nodeTest 704 712 720 nodes_part002_00704 nodes_part002_00712

theorem nodes_part002_join_00720_00736 : FiniteChecks.Interval nodeTest 720 736 :=
  FiniteChecks.interval_append nodeTest 720 728 736 nodes_part002_00720 nodes_part002_00728

theorem nodes_part002_join_00704_00736 : FiniteChecks.Interval nodeTest 704 736 :=
  FiniteChecks.interval_append nodeTest 704 720 736 nodes_part002_join_00704_00720 nodes_part002_join_00720_00736

theorem nodes_part002_join_00736_00752 : FiniteChecks.Interval nodeTest 736 752 :=
  FiniteChecks.interval_append nodeTest 736 744 752 nodes_part002_00736 nodes_part002_00744

theorem nodes_part002_join_00752_00768 : FiniteChecks.Interval nodeTest 752 768 :=
  FiniteChecks.interval_append nodeTest 752 760 768 nodes_part002_00752 nodes_part002_00760

theorem nodes_part002_join_00736_00768 : FiniteChecks.Interval nodeTest 736 768 :=
  FiniteChecks.interval_append nodeTest 736 752 768 nodes_part002_join_00736_00752 nodes_part002_join_00752_00768

theorem nodes_part002_join_00704_00768 : FiniteChecks.Interval nodeTest 704 768 :=
  FiniteChecks.interval_append nodeTest 704 736 768 nodes_part002_join_00704_00736 nodes_part002_join_00736_00768

theorem nodes_part002_join_00640_00768 : FiniteChecks.Interval nodeTest 640 768 :=
  FiniteChecks.interval_append nodeTest 640 704 768 nodes_part002_join_00640_00704 nodes_part002_join_00704_00768

theorem nodes_part002_join_00512_00768 : FiniteChecks.Interval nodeTest 512 768 :=
  FiniteChecks.interval_append nodeTest 512 640 768 nodes_part002_join_00512_00640 nodes_part002_join_00640_00768

end Papers.RationalityTen.PolygonGrowth.N7
