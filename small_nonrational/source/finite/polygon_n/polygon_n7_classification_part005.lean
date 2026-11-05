module

public import PolygonN7ClassificationPart004

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_01392 : FiniteChecks.Interval terminalTest 1392 1400 :=
  FiniteChecks.interval_of_check terminalTest 1392 8 (by decide +kernel)

theorem terminal_data_01400 : FiniteChecks.Interval terminalTest 1400 1408 :=
  FiniteChecks.interval_of_check terminalTest 1400 8 (by decide +kernel)

theorem terminal_data_01408 : FiniteChecks.Interval terminalTest 1408 1416 :=
  FiniteChecks.interval_of_check terminalTest 1408 8 (by decide +kernel)

theorem terminal_data_01416 : FiniteChecks.Interval terminalTest 1416 1424 :=
  FiniteChecks.interval_of_check terminalTest 1416 8 (by decide +kernel)

theorem terminal_data_01424 : FiniteChecks.Interval terminalTest 1424 1432 :=
  FiniteChecks.interval_of_check terminalTest 1424 8 (by decide +kernel)

theorem terminal_data_01432 : FiniteChecks.Interval terminalTest 1432 1440 :=
  FiniteChecks.interval_of_check terminalTest 1432 8 (by decide +kernel)

theorem terminal_data_01440 : FiniteChecks.Interval terminalTest 1440 1448 :=
  FiniteChecks.interval_of_check terminalTest 1440 8 (by decide +kernel)

theorem terminal_data_01448 : FiniteChecks.Interval terminalTest 1448 1456 :=
  FiniteChecks.interval_of_check terminalTest 1448 8 (by decide +kernel)

theorem terminal_data_01456 : FiniteChecks.Interval terminalTest 1456 1464 :=
  FiniteChecks.interval_of_check terminalTest 1456 8 (by decide +kernel)

theorem terminal_data_01464 : FiniteChecks.Interval terminalTest 1464 1472 :=
  FiniteChecks.interval_of_check terminalTest 1464 8 (by decide +kernel)

theorem terminal_data_01472 : FiniteChecks.Interval terminalTest 1472 1480 :=
  FiniteChecks.interval_of_check terminalTest 1472 8 (by decide +kernel)

theorem terminal_data_01480 : FiniteChecks.Interval terminalTest 1480 1488 :=
  FiniteChecks.interval_of_check terminalTest 1480 8 (by decide +kernel)

theorem terminal_data_01488 : FiniteChecks.Interval terminalTest 1488 1496 :=
  FiniteChecks.interval_of_check terminalTest 1488 8 (by decide +kernel)

theorem terminal_data_01496 : FiniteChecks.Interval terminalTest 1496 1504 :=
  FiniteChecks.interval_of_check terminalTest 1496 8 (by decide +kernel)

theorem terminal_data_01504 : FiniteChecks.Interval terminalTest 1504 1512 :=
  FiniteChecks.interval_of_check terminalTest 1504 8 (by decide +kernel)

theorem terminal_data_01512 : FiniteChecks.Interval terminalTest 1512 1520 :=
  FiniteChecks.interval_of_check terminalTest 1512 8 (by decide +kernel)

theorem terminal_data_01520 : FiniteChecks.Interval terminalTest 1520 1528 :=
  FiniteChecks.interval_of_check terminalTest 1520 8 (by decide +kernel)

theorem terminal_data_01528 : FiniteChecks.Interval terminalTest 1528 1536 :=
  FiniteChecks.interval_of_check terminalTest 1528 8 (by decide +kernel)

theorem terminal_data_01536 : FiniteChecks.Interval terminalTest 1536 1544 :=
  FiniteChecks.interval_of_check terminalTest 1536 8 (by decide +kernel)

theorem terminal_data_01544 : FiniteChecks.Interval terminalTest 1544 1552 :=
  FiniteChecks.interval_of_check terminalTest 1544 8 (by decide +kernel)

theorem terminal_data_01552 : FiniteChecks.Interval terminalTest 1552 1560 :=
  FiniteChecks.interval_of_check terminalTest 1552 8 (by decide +kernel)

theorem terminal_data_01560 : FiniteChecks.Interval terminalTest 1560 1568 :=
  FiniteChecks.interval_of_check terminalTest 1560 8 (by decide +kernel)

theorem terminal_data_01568 : FiniteChecks.Interval terminalTest 1568 1576 :=
  FiniteChecks.interval_of_check terminalTest 1568 8 (by decide +kernel)

theorem terminal_data_01576 : FiniteChecks.Interval terminalTest 1576 1584 :=
  FiniteChecks.interval_of_check terminalTest 1576 8 (by decide +kernel)

theorem terminal_data_01584 : FiniteChecks.Interval terminalTest 1584 1592 :=
  FiniteChecks.interval_of_check terminalTest 1584 8 (by decide +kernel)

theorem terminal_data_01592 : FiniteChecks.Interval terminalTest 1592 1600 :=
  FiniteChecks.interval_of_check terminalTest 1592 8 (by decide +kernel)

theorem terminal_data_01600 : FiniteChecks.Interval terminalTest 1600 1608 :=
  FiniteChecks.interval_of_check terminalTest 1600 8 (by decide +kernel)

theorem terminal_data_01608 : FiniteChecks.Interval terminalTest 1608 1616 :=
  FiniteChecks.interval_of_check terminalTest 1608 8 (by decide +kernel)

theorem terminal_data_01616 : FiniteChecks.Interval terminalTest 1616 1624 :=
  FiniteChecks.interval_of_check terminalTest 1616 8 (by decide +kernel)

theorem terminal_data_01624 : FiniteChecks.Interval terminalTest 1624 1632 :=
  FiniteChecks.interval_of_check terminalTest 1624 8 (by decide +kernel)

theorem terminal_data_01632 : FiniteChecks.Interval terminalTest 1632 1640 :=
  FiniteChecks.interval_of_check terminalTest 1632 8 (by decide +kernel)

theorem terminal_data_01640 : FiniteChecks.Interval terminalTest 1640 1648 :=
  FiniteChecks.interval_of_check terminalTest 1640 8 (by decide +kernel)

theorem terminal_data_01648 : FiniteChecks.Interval terminalTest 1648 1656 :=
  FiniteChecks.interval_of_check terminalTest 1648 8 (by decide +kernel)

theorem terminal_data_01656 : FiniteChecks.Interval terminalTest 1656 1664 :=
  FiniteChecks.interval_of_check terminalTest 1656 8 (by decide +kernel)

theorem terminal_data_01664 : FiniteChecks.Interval terminalTest 1664 1672 :=
  FiniteChecks.interval_of_check terminalTest 1664 8 (by decide +kernel)

theorem terminal_data_01672 : FiniteChecks.Interval terminalTest 1672 1680 :=
  FiniteChecks.interval_of_check terminalTest 1672 8 (by decide +kernel)

theorem terminal_data_01680 : FiniteChecks.Interval terminalTest 1680 1688 :=
  FiniteChecks.interval_of_check terminalTest 1680 8 (by decide +kernel)

theorem terminal_data_01688 : FiniteChecks.Interval terminalTest 1688 1696 :=
  FiniteChecks.interval_of_check terminalTest 1688 8 (by decide +kernel)

theorem terminal_data_01696 : FiniteChecks.Interval terminalTest 1696 1704 :=
  FiniteChecks.interval_of_check terminalTest 1696 8 (by decide +kernel)

theorem terminal_data_01704 : FiniteChecks.Interval terminalTest 1704 1712 :=
  FiniteChecks.interval_of_check terminalTest 1704 8 (by decide +kernel)

theorem terminal_data_01712 : FiniteChecks.Interval terminalTest 1712 1720 :=
  FiniteChecks.interval_of_check terminalTest 1712 8 (by decide +kernel)

theorem terminal_data_01720 : FiniteChecks.Interval terminalTest 1720 1728 :=
  FiniteChecks.interval_of_check terminalTest 1720 8 (by decide +kernel)

theorem terminal_data_01728 : FiniteChecks.Interval terminalTest 1728 1736 :=
  FiniteChecks.interval_of_check terminalTest 1728 8 (by decide +kernel)

theorem terminal_data_01736 : FiniteChecks.Interval terminalTest 1736 1744 :=
  FiniteChecks.interval_of_check terminalTest 1736 8 (by decide +kernel)

theorem terminal_data_01744 : FiniteChecks.Interval terminalTest 1744 1752 :=
  FiniteChecks.interval_of_check terminalTest 1744 8 (by decide +kernel)

theorem terminal_data_01752 : FiniteChecks.Interval terminalTest 1752 1760 :=
  FiniteChecks.interval_of_check terminalTest 1752 8 (by decide +kernel)

theorem terminal_data_01760 : FiniteChecks.Interval terminalTest 1760 1768 :=
  FiniteChecks.interval_of_check terminalTest 1760 8 (by decide +kernel)

theorem terminal_data_01768 : FiniteChecks.Interval terminalTest 1768 1776 :=
  FiniteChecks.interval_of_check terminalTest 1768 8 (by decide +kernel)

theorem terminal_data_01776 : FiniteChecks.Interval terminalTest 1776 1784 :=
  FiniteChecks.interval_of_check terminalTest 1776 8 (by decide +kernel)

theorem terminal_data_01784 : FiniteChecks.Interval terminalTest 1784 1792 :=
  FiniteChecks.interval_of_check terminalTest 1784 8 (by decide +kernel)

theorem terminal_data_01792 : FiniteChecks.Interval terminalTest 1792 1800 :=
  FiniteChecks.interval_of_check terminalTest 1792 8 (by decide +kernel)

theorem terminal_data_01800 : FiniteChecks.Interval terminalTest 1800 1808 :=
  FiniteChecks.interval_of_check terminalTest 1800 8 (by decide +kernel)

theorem terminal_data_01808 : FiniteChecks.Interval terminalTest 1808 1816 :=
  FiniteChecks.interval_of_check terminalTest 1808 8 (by decide +kernel)

theorem terminal_data_01816 : FiniteChecks.Interval terminalTest 1816 1824 :=
  FiniteChecks.interval_of_check terminalTest 1816 8 (by decide +kernel)

theorem terminal_data_01824 : FiniteChecks.Interval terminalTest 1824 1832 :=
  FiniteChecks.interval_of_check terminalTest 1824 8 (by decide +kernel)

theorem terminal_data_01832 : FiniteChecks.Interval terminalTest 1832 1840 :=
  FiniteChecks.interval_of_check terminalTest 1832 8 (by decide +kernel)

theorem terminal_data_01840 : FiniteChecks.Interval terminalTest 1840 1848 :=
  FiniteChecks.interval_of_check terminalTest 1840 8 (by decide +kernel)

theorem terminal_data_01848 : FiniteChecks.Interval terminalTest 1848 1856 :=
  FiniteChecks.interval_of_check terminalTest 1848 8 (by decide +kernel)

theorem terminal_data_01856 : FiniteChecks.Interval terminalTest 1856 1864 :=
  FiniteChecks.interval_of_check terminalTest 1856 8 (by decide +kernel)

theorem terminal_data_01864 : FiniteChecks.Interval terminalTest 1864 1872 :=
  FiniteChecks.interval_of_check terminalTest 1864 8 (by decide +kernel)

theorem terminal_data_01872 : FiniteChecks.Interval terminalTest 1872 1880 :=
  FiniteChecks.interval_of_check terminalTest 1872 8 (by decide +kernel)

theorem terminal_data_01880 : FiniteChecks.Interval terminalTest 1880 1888 :=
  FiniteChecks.interval_of_check terminalTest 1880 8 (by decide +kernel)

theorem terminal_data_01888 : FiniteChecks.Interval terminalTest 1888 1896 :=
  FiniteChecks.interval_of_check terminalTest 1888 8 (by decide +kernel)

theorem terminal_data_01896 : FiniteChecks.Interval terminalTest 1896 1904 :=
  FiniteChecks.interval_of_check terminalTest 1896 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
