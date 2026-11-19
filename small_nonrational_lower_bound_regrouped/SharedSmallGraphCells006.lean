module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_006_b1536 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1544 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 8 (by decide +kernel)

theorem cells_006_b1544 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1544 1552 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1544 8 (by decide +kernel)

theorem cells_006_b1552 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1552 1560 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1552 8 (by decide +kernel)

theorem cells_006_b1560 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1560 1568 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1560 8 (by decide +kernel)

theorem cells_006_b1568 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1568 1576 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1568 8 (by decide +kernel)

theorem cells_006_b1576 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1576 1584 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1576 8 (by decide +kernel)

theorem cells_006_b1584 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1584 1592 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1584 8 (by decide +kernel)

theorem cells_006_b1592 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1592 1600 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1592 8 (by decide +kernel)

theorem cells_006_b1600 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1600 1608 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1600 8 (by decide +kernel)

theorem cells_006_b1608 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1608 1616 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1608 8 (by decide +kernel)

theorem cells_006_b1616 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1616 1624 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1616 8 (by decide +kernel)

theorem cells_006_b1624 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1624 1632 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1624 8 (by decide +kernel)

theorem cells_006_b1632 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1632 1640 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1632 8 (by decide +kernel)

theorem cells_006_b1640 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1640 1648 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1640 8 (by decide +kernel)

theorem cells_006_b1648 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1648 1656 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1648 8 (by decide +kernel)

theorem cells_006_b1656 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1656 1664 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1656 8 (by decide +kernel)

theorem cells_006_b1664 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 1672 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 8 (by decide +kernel)

theorem cells_006_b1672 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1672 1680 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1672 8 (by decide +kernel)

theorem cells_006_b1680 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1680 1688 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1680 8 (by decide +kernel)

theorem cells_006_b1688 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1688 1696 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1688 8 (by decide +kernel)

theorem cells_006_b1696 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1696 1704 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1696 8 (by decide +kernel)

theorem cells_006_b1704 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1704 1712 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1704 8 (by decide +kernel)

theorem cells_006_b1712 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1712 1720 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1712 8 (by decide +kernel)

theorem cells_006_b1720 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1720 1728 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1720 8 (by decide +kernel)

theorem cells_006_b1728 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1728 1736 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1728 8 (by decide +kernel)

theorem cells_006_b1736 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1736 1744 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1736 8 (by decide +kernel)

theorem cells_006_b1744 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1744 1752 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1744 8 (by decide +kernel)

theorem cells_006_b1752 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1752 1760 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1752 8 (by decide +kernel)

theorem cells_006_b1760 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1760 1768 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1760 8 (by decide +kernel)

theorem cells_006_b1768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1768 1776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1768 8 (by decide +kernel)

theorem cells_006_b1776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1776 1784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1776 8 (by decide +kernel)

theorem cells_006_b1784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1784 1792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1784 8 (by decide +kernel)

theorem cells_006 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1792 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1664 1792
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1600 1664
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1568 1600
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1552 1568
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1544 1552
 cells_006_b1536
 cells_006_b1544)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1552 1560 1568
 cells_006_b1552
 cells_006_b1560))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1568 1584 1600
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1568 1576 1584
 cells_006_b1568
 cells_006_b1576)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1584 1592 1600
 cells_006_b1584
 cells_006_b1592)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1600 1632 1664
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1600 1616 1632
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1600 1608 1616
 cells_006_b1600
 cells_006_b1608)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1616 1624 1632
 cells_006_b1616
 cells_006_b1624))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1632 1648 1664
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1632 1640 1648
 cells_006_b1632
 cells_006_b1640)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1648 1656 1664
 cells_006_b1648
 cells_006_b1656))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 1728 1792
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 1696 1728
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 1680 1696
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1664 1672 1680
 cells_006_b1664
 cells_006_b1672)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1680 1688 1696
 cells_006_b1680
 cells_006_b1688))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1696 1712 1728
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1696 1704 1712
 cells_006_b1696
 cells_006_b1704)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1712 1720 1728
 cells_006_b1712
 cells_006_b1720)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1728 1760 1792
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1728 1744 1760
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1728 1736 1744
 cells_006_b1728
 cells_006_b1736)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1744 1752 1760
 cells_006_b1744
 cells_006_b1752))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1760 1776 1792
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1760 1768 1776
 cells_006_b1760
 cells_006_b1768)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1776 1784 1792
 cells_006_b1776
 cells_006_b1784)))))
end Papers.RationalityTen.SharedSmallGraph
