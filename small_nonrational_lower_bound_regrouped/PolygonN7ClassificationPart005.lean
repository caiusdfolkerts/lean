module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart004

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 01392 1392 1400 8
cert_terminal_data 01400 1400 1408 8
cert_terminal_data 01408 1408 1416 8
cert_terminal_data 01416 1416 1424 8
cert_terminal_data 01424 1424 1432 8
cert_terminal_data 01432 1432 1440 8
cert_terminal_data 01440 1440 1448 8
cert_terminal_data 01448 1448 1456 8
cert_terminal_data 01456 1456 1464 8
cert_terminal_data 01464 1464 1472 8
cert_terminal_data 01472 1472 1480 8
cert_terminal_data 01480 1480 1488 8
cert_terminal_data 01488 1488 1496 8
cert_terminal_data 01496 1496 1504 8
cert_terminal_data 01504 1504 1512 8
cert_terminal_data 01512 1512 1520 8
cert_terminal_data 01520 1520 1528 8
cert_terminal_data 01528 1528 1536 8
cert_terminal_data 01536 1536 1544 8
cert_terminal_data 01544 1544 1552 8
cert_terminal_data 01552 1552 1560 8
cert_terminal_data 01560 1560 1568 8
cert_terminal_data 01568 1568 1576 8
cert_terminal_data 01576 1576 1584 8
cert_terminal_data 01584 1584 1592 8
cert_terminal_data 01592 1592 1600 8
cert_terminal_data 01600 1600 1608 8
cert_terminal_data 01608 1608 1616 8
cert_terminal_data 01616 1616 1624 8
cert_terminal_data 01624 1624 1632 8
cert_terminal_data 01632 1632 1640 8
cert_terminal_data 01640 1640 1648 8
cert_terminal_data 01648 1648 1656 8
cert_terminal_data 01656 1656 1664 8
cert_terminal_data 01664 1664 1672 8
cert_terminal_data 01672 1672 1680 8
cert_terminal_data 01680 1680 1688 8
cert_terminal_data 01688 1688 1696 8
cert_terminal_data 01696 1696 1704 8
cert_terminal_data 01704 1704 1712 8
cert_terminal_data 01712 1712 1720 8
cert_terminal_data 01720 1720 1728 8
cert_terminal_data 01728 1728 1736 8
cert_terminal_data 01736 1736 1744 8
cert_terminal_data 01744 1744 1752 8
cert_terminal_data 01752 1752 1760 8
cert_terminal_data 01760 1760 1768 8
cert_terminal_data 01768 1768 1776 8
cert_terminal_data 01776 1776 1784 8
cert_terminal_data 01784 1784 1792 8
cert_terminal_data 01792 1792 1800 8
cert_terminal_data 01800 1800 1808 8
cert_terminal_data 01808 1808 1816 8
cert_terminal_data 01816 1816 1824 8
cert_terminal_data 01824 1824 1832 8
cert_terminal_data 01832 1832 1840 8
cert_terminal_data 01840 1840 1848 8
cert_terminal_data 01848 1848 1856 8
cert_terminal_data 01856 1856 1864 8
cert_terminal_data 01864 1864 1872 8
cert_terminal_data 01872 1872 1880 8
cert_terminal_data 01880 1880 1888 8
cert_terminal_data 01888 1888 1896 8
theorem terminal_data_01896 : FiniteChecks.Interval terminalTest 1896 1904 :=
  FiniteChecks.interval_of_check terminalTest 1896 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
